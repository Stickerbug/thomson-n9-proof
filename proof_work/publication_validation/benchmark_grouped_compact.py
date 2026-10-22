#!/usr/bin/env python3
"""Reproduce an isolated grouped-proof experiment using the existing .lake cache."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("target", type=int)
parser.add_argument("--variant", choices=("baseline", "compact"), default="compact")
parser.add_argument("--work-dir", type=Path)
args = parser.parse_args()
pv = Path(__file__).resolve().parent
formal = pv / "formal"
work = (args.work_dir or pv.parents[1] / "work" / "grouped_compact_benchmark").resolve()
lean_dir = os.environ.get("LEAN_BIN_DIR")
lean = str(Path(lean_dir) / "lean") if lean_dir else shutil.which("lean")
if not lean:
    raise SystemExit("set LEAN_BIN_DIR or put Lean on PATH")
checker = str(Path(lean).resolve().with_name("leanchecker"))
label = args.variant.capitalize() + str(args.target)
namespace = "Optimization" + label
source = work / "Optimization" / (label + ".lean")
source.parent.mkdir(parents=True, exist_ok=True)
generator = pv / ("export_grouped_compact.py" if args.variant == "compact" else "export_grouped_generic.py")
subprocess.run([sys.executable, str(generator), str(args.target), str(source), namespace], check=True)
with source.open("a") as handle:
    for suffix in ("sum", "gathered"):
        handle.write(f"\n#print axioms ThomsonNine.{namespace}.t{args.target:03d}_{suffix}\n")
libraries = [work, formal / ".lake/build/lib/lean",
             formal / ".lake/packages/mathlib/.lake/build/lib/lean"]
libraries += [formal / ".lake/pinned_sources" / n / ".lake/build/lib/lean"
              for n in ("aesop", "batteries", "Qq", "plausible", "importGraph",
                        "proofwidgets", "LeanSearchClient", "Cli")]
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libraries)))
env["PATH"] = str(Path(lean).resolve().parent) + os.pathsep + env.get("PATH", "")
artifact = source.with_suffix(".olean")
command = [lean, "-j2", "-o", str(artifact), "-i", str(source.with_suffix(".ilean")),
           str(source.relative_to(work))]
record = {"target": args.target, "variant": args.variant, "command": command,
          "scope": "ISOLATED_EXPERIMENT_NOT_FORMAL_ROOT; module replay is not --fresh",
          "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
start = time.monotonic()
compile_log = work / (label + "_compile.log")
with compile_log.open("w") as handle:
    code = subprocess.run(command, cwd=work, env=env, stdout=handle, stderr=subprocess.STDOUT).returncode
record.update(compile_exit_code=code, compile_seconds=time.monotonic() - start)
if code == 0:
    audit = compile_log.read_text()
    axioms = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", audit)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if len(axioms) != 2 or any(not set(a.replace(" ", "").split(",")) <= allowed for a in axioms):
        raise SystemExit("missing or failed prototype axiom audit")
    record["olean_bytes"] = artifact.stat().st_size
    record["olean_sha256"] = hashlib.sha256(artifact.read_bytes()).hexdigest()
    start = time.monotonic()
    with (work / (label + "_kernel.log")).open("w") as handle:
        code = subprocess.run([checker, "Optimization." + label], cwd=work, env=env,
                              stdout=handle, stderr=subprocess.STDOUT).returncode
    record.update(kernel_replay_exit_code=code, kernel_replay_seconds=time.monotonic() - start)
(work / (label + "_result.json")).write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2), flush=True)
raise SystemExit(code)

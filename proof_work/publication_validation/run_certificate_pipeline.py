#!/usr/bin/env python3
"""Run one generated Thomson certificate adapter through Lean.

The manifest is untrusted input.  This runner validates its paths and invokes
Lean without a shell.  It is a certificate checker/dispatcher, not a numerical
candidate searcher: a failed or missing certificate returns UNKNOWN/FAIL and
never becomes a theorem.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import PurePosixPath

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PV = os.path.join(ROOT, "proof_work", "publication_validation")
FORMAL = os.path.join(PV, "formal")


def safe_relative(value: str) -> bool:
    p = PurePosixPath(value.replace("\\", "/"))
    return bool(value) and not p.is_absolute() and ".." not in p.parts


def load_manifest(path: str) -> dict:
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    if data.get("schema") != "thomson-certificate-v1":
        raise ValueError("unsupported manifest schema")
    n = data.get("instance_n")
    if not isinstance(n, int) or n < 0:
        raise ValueError("instance_n must be a nonnegative integer")
    if data.get("mode") in {"candidate_only", "external_claim_only", "discovery"}:
        refs = data.get("evidence_refs", [])
        if not isinstance(refs, list) or not all(isinstance(x, str) and safe_relative(x) for x in refs):
            raise ValueError("candidate_only evidence_refs must be safe relative paths")
        missing = [x for x in refs if not os.path.isfile(os.path.join(ROOT, x))]
        if missing:
            raise ValueError("missing candidate evidence: " + ", ".join(missing))
        return data
    lean_file = data.get("lean_file")
    if not isinstance(lean_file, str) or not safe_relative(lean_file):
        raise ValueError("lean_file must be a safe relative path")
    theorem = data.get("root_theorem")
    if not isinstance(theorem, str) or not theorem or any(c.isspace() for c in theorem):
        raise ValueError("root_theorem must be a nonempty declaration name")
    absolute = os.path.join(FORMAL, lean_file)
    if not os.path.isfile(absolute):
        raise ValueError("lean_file does not exist: " + lean_file)
    return data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest")
    parser.add_argument("--lean-bin-dir", default=os.environ.get("LEAN_BIN_DIR", ""))
    parser.add_argument("--report", help="write a JSON execution report")
    args = parser.parse_args()
    started = datetime.now(timezone.utc).isoformat()
    report = {"schema": "thomson-certificate-run-v1", "started_utc": started}
    try:
        manifest_path = os.path.abspath(args.manifest)
        data = load_manifest(manifest_path)
        report.update({"instance_n": data["instance_n"],
                       "root_theorem": data["root_theorem"]})
        if "lean_file" in data:
            report["lean_file"] = data["lean_file"]
        if data.get("mode") in {"candidate_only", "external_claim_only", "discovery"}:
            reason = ("candidate data supplied without a Lean certificate adapter"
                      if data.get("mode") == "candidate_only" else
                      "external theorem contract recorded without local source import or replay"
                      if data.get("mode") == "external_claim_only" else
                      "discovery intake has no accepted n=10 candidate, exact energy model, or Lean adapter")
            report.update({"status": "UNKNOWN", "phase": data.get("phase", "intake"), "reason": reason,
                           "evidence_refs": data["evidence_refs"], "exit_code": None})
            if args.report:
                with open(args.report, "w", encoding="utf-8") as f:
                    json.dump(report, f, ensure_ascii=False, indent=2)
                    f.write("\n")
            print(json.dumps({k: v for k, v in report.items() if k != "output"}, ensure_ascii=False))
            return 1
        source = data["lean_file"]
        output = os.path.join(FORMAL, ".lake", "build", "lib", "lean",
                              os.path.splitext(source)[0] + ".olean")
        os.makedirs(os.path.dirname(output), exist_ok=True)
        env = dict(os.environ)
        if args.lean_bin_dir:
            env["PATH"] = args.lean_bin_dir + os.pathsep + env.get("PATH", "")
        cmd = ["lake", "env", "lean", "-o", output, source]
        proc = subprocess.run(cmd, cwd=FORMAL, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        report.update({"command": cmd, "exit_code": proc.returncode,
                       "output": proc.stdout[-12000:],
                       "status": "PASS" if proc.returncode == 0 else "FAIL"})
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        report.update({"status": "UNKNOWN", "error": str(exc), "exit_code": None})
    if args.report:
        with open(args.report, "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
            f.write("\n")
    print(json.dumps({k: v for k, v in report.items() if k != "output"}, ensure_ascii=False))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())

"""Exact energy identity and linkage audit; no independent interval implementation."""
if not __debug__: raise RuntimeError("Run without -O")
import json
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations,product
from collections import Counter
from hashlib import sha256
B=Path(__file__).resolve().parent
def read(n):return json.loads((B/n).read_text())
ordered=Counter()
for a,b,c in product(range(9),repeat=3):
 ids=tuple(sorted(set((a,b,c))));ordered[("T",ids)if len(ids)==3 else("D",ids)if len(ids)==2 else("F111",)]+=1
assert sum(ordered.values())==729 and ordered[("F111",)]==9
assert all(ordered[("T",t)]==6 for t in combinations(range(9),3))
assert all(ordered[("D",p)]==6 for p in combinations(range(9),2))
e=Counter()
for t in combinations(range(9),3):
 for p in combinations(t,2):e[("f",p)]+=Q(1,7);e[("D",p)]-=Q(1,7)
 e[("T",t)]-=1;e[("E_star",)]-=Q(1,84);e[("F111",)]-=Q(1,56)
for k,v in ordered.items():e[k]+=Q(v,6)
expected={("f",p):Q(1)for p in combinations(range(9),2)};expected[("E_star",)]=Q(-1)
assert {k:v for k,v in e.items()if v}==expected
r=read("relative_normal2026_replay2/prerequisites_and_root.json")
for n,h in r["source_sha256"].items():assert sha256((B/n).read_bytes()).hexdigest()==h,n
for n,h in r["artifacts_sha256"].items():assert sha256((B/"relative_normal2026_replay2"/n).read_bytes()).hexdigest()==h,n
assert r["pair_root_Hermite_PSD_coefficients_locals_rebuilt"]and r["all12locals_rebuilt"]
a=read("analytic10_sharp2026_run1.json");b=read("relative_normal2026_replay2/root_replay.json")
for x in(a,b):
 assert x["status"]=="CONDITIONAL_SHARP_CLOSED"and Q(x["delta"])==0 and x["pending_count"]==0 and not x["pending"]
 assert x["visited_nodes"]==136125 and x["split_nodes"]==68062 and sum(x["counts"].values())==68063
 assert all(x["coverage"].values())and all(v>0 for v in x["local_counts"].values())
 assert x["guard_reason"]is None and x["h_range_skipped_nodes"]==0
for k in r["fresh_root"]["matching_fields"]:assert a[k]==b[k],k
g=read("d10_relative_normal2026_contact_geometry_review.json")
assert g["status"]=="GEOMETRIC_DERIVATION_REVIEW_PASS_WITH_EXPLICIT_DEPENDENCIES"
assert len(g["physical_anchor_moment_checks"])==11 and all(x["real_moments_identical"]for x in g["physical_anchor_moment_checks"])
o={"status":"LOCAL_COMPUTER_ASSISTED_PROOF_CHAIN_CLOSED_UNREVIEWED","energy_statement":"E_min(9)=E_D3h(r_star)","exact_energy_identity_checked":True,"all_source_hashes_match":True,"two_full_roots_match":True,"delta":"0","pending_count":0,"uniqueness_proved":False,"peer_reviewed":False,"formally_verified":False,"independent_implementation":False,"mathematical_dependencies":["circle harmonic PSD identity","fixed-kernel anchor annihilation and rank33/W compatibility","Hermite remainder positivity and local convexity/Gram graph proof","Legendre pair reduction","outward Bernstein coverage and arithmetic soundness"],"limitations":"Session-internal review and same-code replay; external review and independent implementation remain outstanding."}
p=B/"sharp2026_final_linkage.json"
if p.exists(): assert json.loads(p.read_text())==o
else: p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+"\n")
print(o["status"]);print("Exact identity: E-E_star=sum_84(R_f)/7+sum_729(F)/6")

"""Read-only prerequisite replay; add --replay-root for a NEW full-root check.
Default performs no global tree and makes NO new global-proof claim.
This nonsharp path uses no Hermite/contact-exactness/local-certificate theorem.
"""
if not __debug__:raise RuntimeError('Run without -O: exact assertions are mandatory')
import argparse,json,hashlib,runpy,os,time
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations
BASE=Path(__file__).resolve().parent
os.chdir(BASE.parent)
from dyadic_interval import I,S,BITS
from certify_pair_moments import derivative
from certify_three_point_d4 import mul,add,scale,mono,const
from narrowroot2026_kernel import run as rebuild_kernel
from analytic10_2026_engine import check_analytic,_serial,_hash

def load(n):return json.loads((BASE/n).read_text())
def raw(v):
 assert v['denominator_power_of_two']==BITS
 return I(int(v['lo_numerator']),int(v['hi_numerator']),raw=True)
def check_hashes():
 manifest=load('analytic10_2026_dependencies.json')
 for name,sha in manifest['sha256'].items():assert hashlib.sha256((BASE/name).read_bytes()).hexdigest()==sha,('dependency hash mismatch',name)
 return manifest

def rebuild_F_c(ctx):
 Ns=ctx['N'];xx=ctx['x'];lookup={tuple(t):j for j,t in enumerate(ctx['indices'])};AA=[]
 for k,N in enumerate(Ns):
  n=len(N)
  if not n:AA.append([]);continue
  B=[[xx[lookup[k,min(i,j),max(i,j)]]for j in range(n)]for i in range(n)];m=len(N[0]);AA.append([[sum((N[a][i]*sum((B[a][b]*N[b][j]for b in range(n)),I(0))for a in range(n)),I(0))for j in range(m)]for i in range(m)])
 a=add(mono(2,1),scale(mul(mono(0,1),mono(1,1)),-1));b=mul(add(const(1),scale(mono(0,2),-1)),add(const(1),scale(mono(1,2),-1)));QQ=[const(1),a]
 for k in range(1,10):QQ.append(add(scale(mul(a,QQ[-1]),2),scale(mul(b,QQ[-2]),-1)))
 fp={}
 for k,Ak in enumerate(AA):
  for i,row in enumerate(Ak):
   for j,c in enumerate(row):
    for e,q in QQ[k].items():
     es=(e[0]+i,e[1]+j,e[2])
     for pm in permutations(range(3)):
      key=[0]*3
      for axis in range(3):key[pm[axis]]=es[axis]
      key=tuple(key);fp[key]=fp.get(key,I(0))+c*(q/6)
 nodes=ctx['nodes'];E=sum((w/(2-2*x).sqrt()for w,x in zip([6,3,6,3,12,6],nodes)),I(0));F111=sum(fp.values(),I(0));return fp,E/12+F111/8,E,F111

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--replay-root',action='store_true');args=parser.parse_args();start=time.monotonic();manifest=check_hashes();saved=load('analytic10_2026_run1.json');co=load('narrowroot2026_coefficients.json');cert=load('narrowroot2026_certificate.json');root=load('narrowroot2026_root.json');delta=Q(1,10**7);decimal=Q('25.75998643126983')
 assert saved['conditional_only'] and saved['status']=='CONDITIONAL_NONSHARP_CLOSED'and saved['pending_count']==0 and saved['pending']==[] and saved['guard_reason']is None
 assert saved['delta']==str(delta)and saved['counts']['local_region']==0 and sum(saved['local_counts'].values())==0
 assert all(saved['coverage'].values())and saved['visited_nodes']==sum(saved['counts'].values())+saved['split_nodes']and sum(saved['counts'].values())==saved['split_nodes']+1
 assert saved['root_inputs_sha256']==_hash(saved['rootinputs'])and saved['engine_sha256']==hashlib.sha256((BASE/'analytic10_2026_engine.py').read_bytes()).hexdigest()
 # Bracket an actual continuous stationary root. Uniqueness in this interval follows
 # analytically from E''(r)>4sqrt(3)/r^3>0; global optimality in r is NOT used.
 lo,hi=map(Q,root['root_refined']);assert 0<lo<hi<1 and hi-lo<Q(1,2**350);assert derivative(I(lo)).hi<0<derivative(I(hi)).lo
 assert cert['root_interval']==root['root_refined']
 # This call rebuilds analytic bases and corrected B, asserts nonzero LU pivots,
 # then proves positive interval LDL pivots for every reduced block. No output.
 ctx=rebuild_kernel(None,str(BASE/'narrowroot2026_certificate.json'),True)
 assert [x.bounds()for x in ctx['x']]==cert['reduced_solution_enclosures']
 fp,c,E,F111=rebuild_F_c(ctx);archived={tuple(p):raw(v)for p,v in co['F_coefficients']};assert set(fp)==set(archived)
 assert all(fp[p].bounds()==archived[p].bounds()for p in fp)
 assert c.bounds()==co['c']and E.bounds()==co['E_star']and F111.bounds()==co['F111']
 assert all(max(p[i]for p in fp)<=10 for i in range(3))
 # Independent closed-form candidate energy, distinct from the F/c assembly.
 r=I(lo,hi);EC=I(3).sqrt()+2*I(3).sqrt()/r+I('1.5')/(1-r*r).sqrt()+6/(4-r*r).sqrt()+12/(2-r).sqrt()+6/(2+2*r).sqrt()
 assert E.lo<=EC.hi and EC.lo<=E.hi
 assert decimal<=Q(E.lo,S)-delta and decimal<=Q(EC.lo,S)-delta
 # Re-prove rational f>=p and strict pair exclusion from coefficient strings;
 # pair reduction applies to all E<=U. Any E>U already exceeds our target.
 runpy.run_path(str(BASE/'verify_pair056_saved.py'),run_name='analytic10_pair_prerequisite')
 pair=load('pair056_optimized_certificate.json');U=Q(pair['U']);assert Q(E.hi,S)-delta<U and decimal<U
 boundary=saved['rootinputs']['boundary_multipliers']
 for term in boundary:assert Q(term['lambda'])>=0
 # Jets are unnecessary: ANY rational nonnegative multiplier is sound.
 Fints={p:(Q(v.lo,S),Q(v.hi,S))for p,v in fp.items()};cints=(Q(c.lo,S),Q(c.hi,S))
 report={'status':'PREREQUISITES_REBUILT_SAVED_ROOT_NOT_REPLAYED','global_bound_claimed_by_this_run':False,'decimal_target':str(decimal),'energy_E_star':E.bounds(),'independent_energy':EC.bounds(),'delta':str(delta),'PSD_interval_LDL_rebuilt':True,'F_c_interval_rebuilt_bitwise':True,'pair_exclusion_reproved':True,'local_terminals':0,'local_and_Hermite_theorems_used':False,'exact_contact_theorem_used':False,'jets_theorem_used':False,'nonnegative_boundary_multipliers_checked':True,'manifest_sha256':hashlib.sha256((BASE/'analytic10_2026_dependencies.json').read_bytes()).hexdigest(),'root_replay_command':manifest['root_replay_command'],'mathematical_identity':'For 9 points, sum R over84 unordered triples>=0 and total ordered PSD kernel sum>=0 imply E>=12(c-delta/12)-3F111/2=E_star-delta. Distinct-pair diagonals F(1,t,t) are counted7 times. Kernel PSD follows the S2 anchored-circle Chebyshev addition theorem for Q_k and A_k=N_k^T B_k N_k with rebuilt B_k positive definite.'}
 if args.replay_root:
  # This is a fresh root, NOT a saved-frontier continuation. No local input.
  replay=check_analytic(Fints,cints,[],boundary,budget=200000,seconds=180,delta=delta)
  assert replay['status']=='CONDITIONAL_NONSHARP_CLOSED'and replay['pending_count']==0 and replay['counts']['local_region']==0
  for k in ['visited_nodes','split_nodes','counts','boundary_counts','maxdepth','transcript_sha256']:assert replay[k]==saved[k],('root replay mismatch',k)
  # Recheck every frozen source/output after calculation, preventing in-run edits.
  check_hashes();report.update(status='VERIFIED_NONSHARP_DECIMAL_LOWER_BOUND',global_bound_claimed_by_this_run=True,replayed_root_seconds=replay['elapsed_seconds'],visited_nodes=replay['visited_nodes'],pending_count=0,root_transcript_sha256=replay['transcript_sha256'])
 report['seconds']=time.monotonic()-start;print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()

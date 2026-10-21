"""Export fixed-model data and independent 80-digit negative witnesses; discovery only."""
import json,itertools,time
import numpy as np
import mpmath as mp
from sharp_contact_refinement2026_core import ROOT,PREFIX,KEY
from sharp_contact_refinement2026_refine import IndependentActual

def mpR(A,c,point):
    p=[mp.mpf(str(v)) for v in point];AA=[[[mp.mpf(str(v)) for v in row] for row in a] for a in A];cc=mp.mpf(str(c))
    def FF(p):
        out=mp.mpf(0)
        for u,v,t in itertools.permutations(p):
            a=t-u*v;b=(1-u*u)*(1-v*v);Q=[mp.mpf(1),a]
            for k in range(1,len(AA)-1):Q.append(2*a*Q[-1]-b*Q[-2])
            for k,M in enumerate(AA):out+=Q[k]*sum(M[i][j]*u**i*v**j for i in range(len(M)) for j in range(len(M)))/6
        return out
    val=sum(1/mp.sqrt(2-2*s) for s in p)-7*FF(p)-sum(FF([mp.mpf(1),s,s]) for s in p)-cc
    gram=1+2*mp.fprod(p)-sum(s*s for s in p)
    return {'point_decimal':[str(v) for v in point],'R_decimal_80digit':mp.nstr(val,80),'gram_decimal_80digit':mp.nstr(gram,80),'precision_digits':80,'interpretation':'finite JSON decimal A,c,point interpreted exactly; high precision evaluation is numerical, not interval proof'}

def compact(row,N,case):
    return {'case':case,'warning':'DISCOVERY ONLY; NOT global nonnegative or exact PSD certificate','x':row['x'],'N':N,'B':row['B'],'A':row['A'],'c':row['c'],'F111':row['F111'],'objective_B':row['objective_B'],'trace':row['trace'],'min_B_eigenvalue':row['min_B_eigenvalue'],'worst_point':row['worst_point'],'independent_actual_min_R':row['independent_actual_min_R'],'solver_precision':row.get('solver_precision')}

def main():
    mp.mp.dps=80;start=time.time();run=json.loads((ROOT/(PREFIX+'results.json')).read_text());phase=json.loads((ROOT/(PREFIX+'contact_psd.json')).read_text())
    final=run['best_solution'];N=run['nullspace_bases'];old=phase['history'][0];aug=phase['history'][1];local=phase['history'][2]
    packet={'warning':'NUMERICAL DISCOVERY ONLY. Target minR>-1e-7 and PSD>=-1e-9 not jointly met. No Thomson counterexample or SDP impossibility conclusion.','status':'finite_three_round_search_exhausted','best_PSD_cutting_plane_solution':final,'best_low_trace_augmented_contact_solution':compact(aug,N,'contact_and_PSD_only; local jets fail'),'best_low_trace_contact_and_local_jets_solution':compact(local,N,'contact_PSD_and_all_local_first_second_order_conditions; global residual fails'),'starting_PSD_contact_solution':compact(old,N,'old rank32 contacts; missing boundary tangent'),'indices':run['indices'],'exact_r_approximation':run['r_approximation'],'contact_rank':32,'contact_plus_tangent_rank':33,'cutting_plane_rounds':len(run['history']),'new_CuttingPlane_solvers_after_budget':0,'high_precision_negative_witnesses':{},'training_audits':{},'history_metrics':[],'phase_metrics':[]}
    for row in run['history']:
        sol=row['solution'];actual=IndependentActual([np.array(a) for a in sol['A']],sol['c']);points=np.array(run['training_points']);values=np.concatenate([actual(points[i:i+512]) for i in range(0,len(points),512)]);i=int(np.argmin(values))
        packet['training_audits']['iteration_'+str(row['iteration'])]={'full_final_training_count':len(points),'minimum_R_independent_original_A':float(values[i]),'worst_point':points[i].tolist()}
        packet['history_metrics'].append({k:row[k] for k in ['iteration','training_count','solver_precision','tau','trace','min_B_eigenvalue','min_original_A_eigenvalue','contact_max_error','boundary_tangent_max_error','training_min_R','interior_H_min_eigenvalue','boundary_jets','independent_actual_min_R','worst_point','key_point_R_actual','independent_original_A_discrepancy','independent_design_crosscheck']})
    for row in phase['history']:
        packet['phase_metrics'].append({k:row[k] for k in ['case','solver_precision','trace','min_B_eigenvalue','contact_max_error','boundary_tangent_max_error','internal_Hessian_min_eigenvalue','boundary_jets','independent_actual_min_R','worst_point','key_point_R_actual','distance_from_original_projection']})
    for name,row in [('CP_final',final),('original_PSD',old),('augmented_contact_PSD',aug),('augmented_contact_PSD_local_Hessian',local)]:
        point=row['worst_point']['triangle']
        if name=='augmented_contact_PSD_local_Hessian':
            b=mp.mpf(str(point[1]));point=[mp.nstr(-1+2*b*b+mp.mpf('1e-11'),65),str(point[1]),str(point[1])]
        packet['high_precision_negative_witnesses'][name]=mpR(row['A'],row['c'],point)
        packet['high_precision_negative_witnesses'][name+'_key']=mpR(row['A'],row['c'],KEY)
    packet['source_training_counts']=run['source_training_counts'];packet['initial_training_count']=run['initial_training_count'];packet['final_training_count']=len(run['training_points']);packet['elapsed_export_seconds']=time.time()-start
    out=ROOT/(PREFIX+'best_original_data.json');assert not out.exists();out.write_text(json.dumps(packet,indent=2)+chr(10))
    metrics=ROOT/(PREFIX+'summary_metrics.json');assert not metrics.exists();metrics.write_text(json.dumps({k:v for k,v in packet.items() if k not in ['best_PSD_cutting_plane_solution','best_low_trace_augmented_contact_solution','best_low_trace_contact_and_local_jets_solution','starting_PSD_contact_solution','indices']},indent=2)+chr(10))
    print(json.dumps({k:packet[k] for k in ['high_precision_negative_witnesses','training_audits','elapsed_export_seconds']},indent=2),flush=True)
if __name__=='__main__':main()

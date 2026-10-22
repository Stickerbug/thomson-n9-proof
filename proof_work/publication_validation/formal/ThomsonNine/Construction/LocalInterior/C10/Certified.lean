import ThomsonNine.Construction.LocalInterior.C10.BoundsRow0
import ThomsonNine.Construction.LocalInterior.C10.BoundsRow1
import ThomsonNine.Construction.LocalInterior.C10.BoundsRow2
import ThomsonNine.Construction.LocalInterior.C10.PSDCertificate
import ThomsonNine.Construction.Algebra.HessianPSD
import ThomsonNine.Construction.LocalShift.Nonnegative
import ThomsonNine.Construction.Algebra.FixedMatrix

-- Isolated source: LocalInterior.C10.Certified
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C10
open ThomsonNine.FixedInterval ThomsonNine.ActualLocalAAA
open ThomsonNine.Interval.SparsePolynomial
open scoped BigOperators
attribute [local irreducible] entries
theorem computed_fields (i j : Fin 3) : (hessianComputed i j).lo=(hessianCache i j).lo ∧ (hessianComputed i j).hi=(hessianCache i j).hi := by
  fin_cases i <;> fin_cases j
  · exact fields00
  · exact fields01
  · exact fields02
  · exact fields10
  · exact fields11
  · exact fields12
  · exact fields20
  · exact fields21
  · exact fields22
theorem formal_hessian_mem (i j : Fin 3) (x : Fin 3 → ℝ)
    (hx : ∀ a, (relativeBox a).mem (x a)) :
    Mem LocalShift.scale (hessianCache i j)
      (formalHessianEntry Entry.exp (fun E => coefficient E.index) i j x entries) := by
  have h := hessianComputed_mem i j x hx
  have he : hessianComputed i j=hessianCache i j :=
    congrArg₂ Bounds.mk (computed_fields i j).1 (computed_fields i j).2
  rw [he] at h
  exact h
def WQ : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,0;1,1,0;2/5,-3/5,1]
def W : Matrix (Fin 3) (Fin 3) ℝ := fun i j => WQ i j
def WInput : Fin 3 → Fin 3 → Bounds := ![![⟨1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856,1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856⟩,
⟨0,0⟩,
⟨0,0⟩],
![⟨1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856,1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856⟩,
⟨1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856,1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856⟩,
⟨0,0⟩],
![⟨621007236920283574059591795385001022102754406846678644455620815210420381074550754532351363531458591180195092278852429282468632017645925756577714910016472455681781990408339962220106114252639377930105199677486587500357138741526423142,621007236920283574059591795385001022102754406846678644455620815210420381074550754532351363531458591180195092278852429282468632017645925756577714910016472455681781990408339962220106114252639377930105199677486587500357138741526423143⟩,
⟨(-931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634714),(-931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)⟩,
⟨1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856,1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856⟩]]
theorem W_bounds : ∀ i j, ((WInput i j).lo : ℚ)≤(LocalShift.scale : ℚ)*WQ i j ∧
    (LocalShift.scale : ℚ)*WQ i j≤((WInput i j).hi : ℚ) := by decide +kernel
theorem W_mem : ∀ i j, Mem LocalShift.scale (WInput i j) (W i j) := by
  intro i j
  constructor
  · change ((WInput i j).lo : ℝ)≤(LocalShift.scale : ℝ)*(WQ i j : ℝ)
    exact_mod_cast (W_bounds i j).1
  · change (LocalShift.scale : ℝ)*(WQ i j : ℝ)≤((WInput i j).hi : ℝ)
    exact_mod_cast (W_bounds i j).2
def transformedInput : Fin 3 → Fin 3 → Bounds :=
  matrixMul3 LocalShift.scale (matrixMul3 LocalShift.scale WInput hessianCache) (fun i j => WInput j i)
theorem transformed_fields : ∀ i j, (transformedInput i j).lo=(PSD0.matrix i j).lo ∧
    (transformedInput i j).hi=(PSD0.matrix i j).hi := by decide +kernel
theorem transformed_symmetric : ∀ i j, PSD0.matrix i j=PSD0.matrix j i := by
  intro i j
  apply congrArg₂ Bounds.mk <;> fin_cases i <;> fin_cases j <;> rfl
theorem directionalHessian_nonnegative (x velocity : Fin 3 → ℝ)
    (hx : ∀ a, (relativeBox a).mem (x a)) :
    0≤directionalHessian Entry.exp (fun E => coefficient E.index) x velocity entries := by
  let H : Matrix (Fin 3) (Fin 3) ℝ := fun i j => formalHessianEntry Entry.exp (fun E => coefficient E.index) i j x entries
  let P : Matrix (Fin 3) (Fin 3) ℝ := (W*H)*W.transpose
  have hP (i j : Fin 3) : Mem LocalShift.scale (PSD0.matrix i j) (P i j) := by
    have h := matrixMul3_mem LocalShift.scale_pos (matrixMul3 LocalShift.scale WInput hessianCache)
      (fun i j => WInput j i) (W*H) W.transpose
      (fun a b => matrixMul3_mem LocalShift.scale_pos WInput hessianCache W H W_mem
        (fun a b => formal_hessian_mem a b x hx) a b) (fun a b => W_mem b a) i j
    have he : transformedInput i j=PSD0.matrix i j :=
      congrArg₂ Bounds.mk (transformed_fields i j).1 (transformed_fields i j).2
    change Mem LocalShift.scale (transformedInput i j) (P i j) at h
    rw [he] at h
    exact h
  let v : Fin 3 → ℝ := ![velocity 0-velocity 1-velocity 2,velocity 1+3/5*velocity 2,velocity 2]
  have h := LocalQuadratic.nonnegative_of_certificate PSD0.matrix transformed_symmetric PSD0.certificate P hP v
  have he : (∑ i : Fin 3, ∑ j : Fin 3, P i j*v j*v i)=
      directionalHessian Entry.exp (fun E => coefficient E.index) x velocity entries := by
    simp only [P,v,W,WQ,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,directionalHessian,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    dsimp only [H]
    ring
  rw [he] at h
  exact h
theorem relative_zero : ∀ a, (relativeBox a).mem (0 : ℝ) := by
  intro a
  have h : (relativeBox a).lo≤0 ∧ 0≤(relativeBox a).hi := by fin_cases a <;> decide +kernel
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2
theorem actual_residual_nonnegative (x : Fin 3 → ℝ) (hx : ∀ a, (relativeBox a).mem (x a)) :
    0≤ActualR.residual (fun a => LocalShift.center localId a+x a) := by
  apply LocalShift.residual_nonnegative_of_hessian localId (by unfold LocalShift.IsInterior;decide +kernel)
    relativeBox relative_zero directionalHessian_nonnegative x hx
end ThomsonNine.ActualLocal.C10

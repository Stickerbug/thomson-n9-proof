import ThomsonNine.Construction.LocalShift.Inputs
import ThomsonNine.Construction.Contact.ResidualJet
import ThomsonNine.Construction.F.Symmetry

-- Isolated source: LocalShift.Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.LocalShift
open ThomsonNine.ActualContact ThomsonNine.ContactJet
open scoped BigOperators

theorem residual_swap12 (u v t : ℝ) :
    ActualR.residual ![u,v,t]=ActualR.residual ![v,u,t] := by
  simp only [ActualR.residual,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  rw [ActualF.swap12]
  ring

theorem residual_swap23 (u v t : ℝ) :
    ActualR.residual ![u,v,t]=ActualR.residual ![u,t,v] := by
  simp only [ActualR.residual,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  rw [ActualF.swap23]
  ring

attribute [local irreducible] ActualR.residual ActualF.F

theorem residual_permutation (σ : Fin 6) (x : Point) :
    ActualR.residual (fun a => x (ActualKernel.QCache.permutation σ a))=ActualR.residual x := by
  have hv (p : Point) : p=![p 0,p 1,p 2] := by funext a;fin_cases a <;> rfl
  calc
    ActualR.residual (fun a => x (ActualKernel.QCache.permutation σ a))=
        ActualR.residual ![x (ActualKernel.QCache.permutation σ 0),
          x (ActualKernel.QCache.permutation σ 1),x (ActualKernel.QCache.permutation σ 2)] :=
      congrArg ActualR.residual (hv _)
    _ = ActualR.residual ![x 0,x 1,x 2] := by
      fin_cases σ
      · rfl
      · exact residual_swap23 _ _ _
      · exact residual_swap12 _ _ _
      · exact (residual_swap23 _ _ _).trans (residual_swap12 _ _ _)
      · exact (residual_swap12 _ _ _).trans (residual_swap23 _ _ _)
      · exact ((residual_swap12 _ _ _).trans (residual_swap23 _ _ _)).trans (residual_swap12 _ _ _)
    _ = ActualR.residual x := congrArg ActualR.residual (hv x).symm

def toCanonical : Fin 12 → Fin 6 := ![0,5,4,0,3,0,4,0,1,0,0,3]
theorem center_nodes_canonical : ∀ localId a,
    labels localId (ActualKernel.QCache.permutation (toCanonical localId) a)=
      (ActualContact.rows (valueRows localId)).nodes a := by decide +kernel
theorem center_canonical (localId : Fin 12) :
    (fun a => center localId (ActualKernel.QCache.permutation (toCanonical localId) a))=
      point (valueRows localId) := by
  funext a
  exact congrArg ActualHermite.node (center_nodes_canonical localId a)

theorem center_value_zero (localId : Fin 12) : ActualR.residual (center localId)=0 := by
  rw [← residual_permutation (toCanonical localId),center_canonical]
  exact all_actual_contact_values localId

def IsInterior (localId : Fin 12) : Prop := localId≠6 ∧ localId≠7 ∧ localId≠9
def gradientRows : Fin 12 → Fin 3 → Fin 45 :=
  ![![1,2,3],![5,6,7],![9,10,11],![13,14,15],![17,18,19],![21,22,23],
    ![25,25,26],![28,28,29],![31,32,33],![35,35,36],![38,39,40],![42,43,44]]
theorem gradient_metadata : ∀ localId, IsInterior localId → ∀ a,
    (ActualContact.rows (gradientRows localId a)).kind=1 ∧ (ActualContact.rows (gradientRows localId a)).axis=a ∧
      (ActualContact.rows (gradientRows localId a)).nodes=(ActualContact.rows (valueRows localId)).nodes := by
  unfold IsInterior
  decide +kernel

theorem canonical_gradient_zero (localId : Fin 12) (hi : IsInterior localId) (a : Fin 3) :
    residualGradient (point (valueRows localId)) a=0 := by
  have hm := gradient_metadata localId hi a
  have h := actual_interior_gradient_zero (gradientRows localId a) hm.1
  have hp : point (gradientRows localId a)=point (valueRows localId) :=
    congrArg (fun n : Fin 3 → Fin 14 => fun j => ActualHermite.node (n j)) hm.2.2
  rw [hp,hm.2.1] at h
  exact h

theorem center_line_derivative_zero (localId : Fin 12) (hi : IsInterior localId)
    (velocity : Fin 3 → ℝ) :
    HasDerivAt (fun t => ActualR.residual (fun a => center localId a+t*velocity a)) 0 0 := by
  let σ := ActualKernel.QCache.permutation (toCanonical localId)
  let curve : ℝ → Point := fun t a => center localId (σ a)+t*velocity (σ a)
  have hc : curve 0=point (valueRows localId) := by
    simpa only [curve,zero_mul,add_zero] using center_canonical localId
  have hd (a : Fin 3) : HasDerivAt (fun t => curve t a) (velocity (σ a)) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (center localId (σ a))).add
      ((hasDerivAt_id' 0).mul_const (velocity (σ a))) using 1 <;> simp
  have h := residual_curve_derivative (point (valueRows localId)) curve (fun a => velocity (σ a)) 0 hc hd
  simp only [canonical_gradient_zero localId hi,zero_mul,Finset.sum_const_zero] at h
  have he : (fun t => ActualR.residual (curve t))=
      (fun t => ActualR.residual (fun a => center localId a+t*velocity a)) := by
    funext t
    exact residual_permutation (toCanonical localId) (fun a => center localId a+t*velocity a)
  rw [he] at h
  exact h
end ThomsonNine.LocalShift

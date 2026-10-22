import LocalShift.Contact
import Algebra.GramGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.LocalShift
open ThomsonNine.ActualContact ThomsonNine.ContactJet
open scoped BigOperators
attribute [local irreducible] ActualR.residual

def IsBoundary (localId : Fin 12) : Prop := localId=6 ∨ localId=7 ∨ localId=9
def boundaryRows : Fin 12 → Fin 2 → Fin 45 :=
  ![![0,0],![0,0],![0,0],![0,0],![0,0],![0,0],![25,26],![28,29],![0,0],![35,36],![0,0],![0,0]]
theorem boundary_metadata : ∀ localId, IsBoundary localId → ∀ a : Fin 2,
    (ActualContact.rows (boundaryRows localId a)).kind=2 ∧
    (ActualContact.rows (boundaryRows localId a)).axis=a.succ ∧
    (ActualContact.rows (boundaryRows localId a)).nodes=(ActualContact.rows (valueRows localId)).nodes := by
  unfold IsBoundary
  decide +kernel

theorem canonical_boundary_tangent (localId : Fin 12) (hb : IsBoundary localId) (a : Fin 2) :
    gramGradient (point (valueRows localId)) 0*residualGradient (point (valueRows localId)) a.succ-
      gramGradient (point (valueRows localId)) a.succ*residualGradient (point (valueRows localId)) 0=0 := by
  have hm := boundary_metadata localId hb a
  have h := actual_boundary_tangent_zero (boundaryRows localId a) hm.1
  have hp : point (boundaryRows localId a)=point (valueRows localId) :=
    congrArg (fun n : Fin 3 → Fin 14 => fun j => ActualHermite.node (n j)) hm.2.2
  rw [hp,hm.2.1] at h
  exact h

theorem canonical_normal_pos (localId : Fin 12) (hb : IsBoundary localId) :
    0<gramGradient (point (valueRows localId)) 0 := by
  have hr := RefinedRadius.radius_pos
  have hr1 := RefinedRadius.radius_lt_one
  have hr2 : RefinedRadius.radius^2<1 := by nlinarith
  rcases hb with h | h | h <;> subst localId <;>
    norm_num [gramGradient,point,valueRows,ActualContact.rows,ActualHermite.node] <;> nlinarith

theorem gram_dot_permutation (σ : Fin 6) (p v : Point) :
    (∑ a : Fin 3, gramGradient (fun j => p (ActualKernel.QCache.permutation σ j)) a*
      v (ActualKernel.QCache.permutation σ a))=
      ∑ a : Fin 3, gramGradient p a*v a := by
  fin_cases σ <;>
    simp [Fin.sum_univ_three,gramGradient,ActualKernel.QCache.permutation] <;> ring

theorem center_curve_derivative_zero_of_tangent (localId : Fin 12) (hb : IsBoundary localId)
    (curve : ℝ → Point) (velocity : Point)
    (hc : curve 0=center localId) (hd : ∀ a, HasDerivAt (fun t => curve t a) (velocity a) 0)
    (htan : (∑ a : Fin 3, gramGradient (center localId) a*velocity a)=0) :
    HasDerivAt (fun t => ActualR.residual (curve t)) 0 0 := by
  let σ := ActualKernel.QCache.permutation (toCanonical localId)
  let p := point (valueRows localId)
  let w : Point := fun a => velocity (σ a)
  let R : Fin 3 → ℝ := residualGradient p
  let G : Fin 3 → ℝ := gramGradient p
  have ht₁ : G 0*R 1-G 1*R 0=0 := canonical_boundary_tangent localId hb 0
  have ht₂ : G 0*R 2-G 2*R 0=0 := canonical_boundary_tangent localId hb 1
  have hg : (∑ a : Fin 3, G a*w a)=0 := by
    dsimp only [G,w,p]
    rw [← center_canonical]
    rw [gram_dot_permutation]
    exact htan
  have he : G 0*(∑ a : Fin 3, R a*w a)=R 0*(∑ a : Fin 3, G a*w a) := by
    simp only [Fin.sum_univ_three]
    linear_combination w 1*ht₁+w 2*ht₂
  have hr : (∑ a : Fin 3, R a*w a)=0 := by
    rw [hg,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (canonical_normal_pos localId hb))
  have hcp : (fun a => curve 0 (σ a))=p := by rw [hc];exact center_canonical localId
  have h := residual_curve_derivative p (fun t a => curve t (σ a)) w 0 hcp (fun a => hd (σ a))
  change HasDerivAt (fun t => ActualR.residual (fun a => curve t (σ a))) (∑ a : Fin 3, R a*w a) 0 at h
  rw [hr] at h
  have heq : (fun t => ActualR.residual (fun a => curve t (σ a)))=(fun t => ActualR.residual (curve t)) := by
    funext t
    exact residual_permutation (toCanonical localId) (curve t)
  rw [heq] at h
  exact h
end ThomsonNine.LocalShift

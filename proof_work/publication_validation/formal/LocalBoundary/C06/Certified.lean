import LocalBoundary.C06.Bounds00
import LocalBoundary.C06.Bounds01
import LocalBoundary.C06.Bounds02
import LocalBoundary.C06.Bounds10
import LocalBoundary.C06.Bounds11
import LocalBoundary.C06.Bounds12
import LocalBoundary.C06.Bounds20
import LocalBoundary.C06.Bounds21
import LocalBoundary.C06.Bounds22
import LocalBoundary.C06.Gradient0
import LocalBoundary.C06.Gradient1
import LocalBoundary.C06.Gradient2
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C06
open ThomsonNine.FixedInterval ThomsonNine.ActualLocalAAA
open ThomsonNine.Interval.SparsePolynomial
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
theorem computed_gradient_fields (i : Fin 3) : (gradientComputed i).lo=(gradientCache i).lo ∧
    (gradientComputed i).hi=(gradientCache i).hi := by
  fin_cases i
  · exact gradient_fields0
  · exact gradient_fields1
  · exact gradient_fields2
theorem formal_gradient_mem (i : Fin 3) (x : Fin 3 → ℝ)
    (hx : ∀ a, (relativeBox a).mem (x a)) :
    Mem LocalShift.scale (gradientCache i)
      (formalDerivative Entry.exp (fun E => coefficient E.index) i x entries) := by
  have h := gradientComputed_mem i x hx
  have he : gradientComputed i=gradientCache i :=
    congrArg₂ Bounds.mk (computed_gradient_fields i).1 (computed_gradient_fields i).2
  rw [he] at h
  exact h
theorem gradient_u_positive (x : Fin 3 → ℝ) (hx : ∀ a, (relativeBox a).mem (x a)) :
    0<formalDerivative Entry.exp (fun E => coefficient E.index) 0 x entries := by
  have h := formal_gradient_mem 0 x hx
  have hp : 0<(gradientCache 0).lo := by decide +kernel
  have hp' : (0 : ℝ)<(gradientCache 0).lo := by exact_mod_cast hp
  exact (mul_pos_iff_of_pos_left (show (0 : ℝ)<LocalShift.scale by exact_mod_cast LocalShift.scale_pos)).mp (hp'.trans_le h.1)
end ThomsonNine.ActualBoundary.C06

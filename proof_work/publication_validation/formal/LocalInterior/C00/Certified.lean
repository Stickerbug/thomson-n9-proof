import LocalInterior.C00.Bounds00
import LocalInterior.C00.Bounds01
import LocalInterior.C00.Bounds02
import LocalInterior.C00.Bounds10
import LocalInterior.C00.Bounds11
import LocalInterior.C00.Bounds12
import LocalInterior.C00.Bounds20
import LocalInterior.C00.Bounds21
import LocalInterior.C00.Bounds22
import LocalInterior.C00.PSD0
import Algebra.HessianPSD
import LocalShift.Nonnegative
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C00
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
theorem cache_symmetric : ∀ i j, hessianCache i j=hessianCache j i := by
  intro i j
  apply congrArg₂ Bounds.mk <;> fin_cases i <;> fin_cases j <;> rfl
theorem cache_psd : FixedInterval.Schur.PSDSound LocalShift.scale hessianCache := PSD0.certificate
theorem directionalHessian_nonnegative (x velocity : Fin 3 → ℝ)
    (hx : ∀ a, (relativeBox a).mem (x a)) :
    0≤directionalHessian Entry.exp (fun E => coefficient E.index) x velocity entries :=
  LocalQuadratic.nonnegative_of_certificate hessianCache cache_symmetric cache_psd
    (fun i j => formalHessianEntry Entry.exp (fun E => coefficient E.index) i j x entries)
    (fun i j => formal_hessian_mem i j x hx) velocity
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
end ThomsonNine.ActualLocal.C00

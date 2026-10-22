import ThomsonNine.Construction.LocalShift.Contact
import ThomsonNine.Construction.LocalShift.EntryModel
import ThomsonNine.Construction.Algebra.SparseCurve
import ThomsonNine.LocalNonneg

-- Isolated source: LocalShift.Nonnegative
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.LocalShift
open ThomsonNine.Interval.SparsePolynomial ThomsonNine.ActualLocalAAA
open scoped BigOperators
attribute [local irreducible] entries ActualR.residual

theorem residual_nonnegative_of_hessian (localId : Fin 12) (hi : IsInterior localId)
    (box : Fin 3 → Interval.RatInterval) (hz : ∀ a, (box a).mem (0 : ℝ))
    (hH : ∀ x velocity : Fin 3 → ℝ, (∀ a, (box a).mem (x a)) →
      0≤directionalHessian Entry.exp (fun E => family3 localId E.index) x velocity entries)
    (x : Fin 3 → ℝ) (hx : ∀ a, (box a).mem (x a)) :
    0≤ActualR.residual (fun a => center localId a+x a) := by
  let curve : ℝ → (Fin 3 → ℝ) := fun t a => t*x a
  let f : ℝ → ℝ := fun t => eval Entry.exp (fun E => family3 localId E.index) (curve t) entries
  let f' : ℝ → ℝ := fun t => directionalDerivative Entry.exp (fun E => family3 localId E.index) (curve t) x entries
  let f'' : ℝ → ℝ := fun t => directionalHessian Entry.exp (fun E => family3 localId E.index) (curve t) x entries
  have hcurve (s : ℝ) (a : Fin 3) : HasDerivAt (fun t => curve t a) (x a) s := by
    simpa only [curve,one_mul] using (hasDerivAt_id' s).mul_const (x a)
  have hd (s : ℝ) : HasDerivAt f (f' s) s :=
    eval_curve_derivative Entry.exp (fun E => family3 localId E.index) entries curve x s (hcurve s)
  have hdd (s : ℝ) : HasDerivAt f' (f'' s) s :=
    directionalDerivative_curve Entry.exp (fun E => family3 localId E.index) entries curve x s (hcurve s)
  have he : f=(fun t => ActualR.residual (fun a => center localId a+t*x a)) := by
    funext t
    exact congrFun (entries_function_eq localId) (curve t)
  have hfzero : f 0=0 := by
    rw [he]
    simpa only [zero_mul,add_zero] using center_value_zero localId
  have hderzero : HasDerivAt f 0 0 := by
    rw [he]
    exact center_line_derivative_zero localId hi x
  have hseg (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) (a : Fin 3) : (box a).mem (curve s a) := by
    have h := (convex_Icc ((box a).lo : ℝ) ((box a).hi : ℝ)).smul_mem_of_zero_mem (hz a) (hx a) hs
    change ((box a).lo : ℝ)≤s*x a ∧ s*x a≤((box a).hi : ℝ)
    simpa only [smul_eq_mul,Set.mem_Icc] using h
  have h := LocalLDL.segment_nonneg_of_second_derivative
    (f:=f) (f':=f') (f'':=f'')
    (fun s hs => (hd s).continuousAt.continuousWithinAt)
    (fun s hs => hd s) (fun s hs => hdd s)
    (fun s hs => hH (curve s) x (hseg s (interior_subset hs))) hfzero hderzero
    1 (by constructor <;> norm_num)
  rw [he] at h
  simpa only [one_mul] using h
end ThomsonNine.LocalShift

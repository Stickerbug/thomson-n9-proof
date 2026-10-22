import PairAddition.PolynomialModel
import PairAddition.HomogeneousComplete

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PairAddition
open Polynomial
open scoped BigOperators

def phi (f : Fin 138) (x : ℝ) : ℝ :=
  (IntegerListPolynomial.realPolynomial (features f).coefficients).eval x
def termCoefficient (h : Fin 38) (f : Fin 138) (u v : ℝ) : ℝ :=
  ((features f).weight : ℝ)*(qCoefficient (features f).order h : ℝ)*phi f u*phi f v*
    ((1-u^2)*(1-v^2))^(((features f).order.val-h.val)/2)

theorem oneMinusSquare_eval (x : ℝ) :
    (IntegerListPolynomial.realPolynomial [1,0,-1]).eval x=1-x^2 := by
  simp [IntegerListPolynomial.realPolynomial,ListPolynomial.polynomial]
  ring

theorem contribution_eval (h : Fin 38) (c : Contribution) (hc : Valid h c) (u v : ℝ) :
    (c.weight : ℝ)*(IntegerListPolynomial.realPolynomial c.coefficients).eval u*
      (IntegerListPolynomial.realPolynomial c.coefficients).eval v=
      (denominator h : ℝ)*termCoefficient h c.feature u v := by
  have hp : c.power=((features c.feature).order.val-h.val)/2 := by
    have he := hc.1
    omega
  have hw := congrArg (fun q : ℚ => (q : ℝ)) hc.2.1
  push_cast at hw
  have he (x : ℝ) : (IntegerListPolynomial.realPolynomial c.coefficients).eval x=
      phi c.feature x*(1-x^2)^c.power := by
    rw [hc.2.2,IntegerListPolynomial.mul_sound,IntegerListPolynomial.pow_sound,
      eval_mul,eval_pow,oneMinusSquare_eval]
    rfl
  rw [he u,he v,hw]
  simp only [termCoefficient,mul_pow,← hp]
  ring

theorem sum_filter_if {α : Type*} (l : List α) (p : α → Bool) (f : α → ℝ) :
    ((l.filter p).map f).sum=(l.map (fun a => if p a then f a else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases hp : p a <;> simp [List.filter_cons,hp,ih]

theorem sum_finRange {n : ℕ} (f : Fin n → ℝ) :
    ((List.finRange n).map f).sum=∑ i : Fin n, f i := by
  have he : (List.finRange n).toFinset=(Finset.univ : Finset (Fin n)) := by ext i;simp
  rw [← List.sum_toFinset f (List.nodup_finRange n),he]

theorem contribution_terms (h : Fin 38) (u v : ℝ) :
    ((contributions h).map (fun c => termCoefficient h c.feature u v)).sum=
      ∑ f : Fin 138, termCoefficient h f u v := by
  have he : (contributions h).map (fun c => termCoefficient h c.feature u v)=
      ((contributions h).map Contribution.feature).map (fun f => termCoefficient h f u v) := by
    rw [List.map_map]
    rfl
  rw [he,all_complete,sum_filter_if]
  have hm : ((List.finRange 138).map (fun f =>
      if decide (h.val≤(features f).order.val ∧ ((features f).order.val-h.val)%2=0)
      then termCoefficient h f u v else 0))=
      ((List.finRange 138).map (fun f => termCoefficient h f u v)) := by
    apply List.map_congr_left
    intro f hf
    by_cases hp : h.val≤(features f).order.val ∧ ((features f).order.val-h.val)%2=0
    · simp [hp]
    · have hq : qCoefficient (features f).order h=0 := by
        by_contra hq
        exact hp ((qCoefficient_nonzero_iff _ _).mp hq)
      simp [hp,termCoefficient,hq]
  rw [hm,sum_finRange]

theorem coefficient_identity (h : Fin 38) (u v : ℝ) :
    (∑ f : Fin 138, termCoefficient h f u v)=(hasseDeriv h.val P).eval (u*v) := by
  have hD : (denominator h : ℝ)≠0 := ne_of_gt (by exact_mod_cast denominators_positive h)
  have hm := coefficient_matrix_eval h u v
  have he : ((contributions h).map (fun c =>
      (c.weight : ℝ)*(IntegerListPolynomial.realPolynomial c.coefficients).eval u*
        (IntegerListPolynomial.realPolynomial c.coefficients).eval v))=
      (contributions h).map (fun c => (denominator h : ℝ)*termCoefficient h c.feature u v) := by
    apply List.map_congr_left
    intro c hc
    have hv : Valid h c := of_decide_eq_true (List.all_eq_true.mp (all_valid h) c hc)
    exact contribution_eval h c hv u v
  rw [he,List.sum_map_mul_left,contribution_terms] at hm
  exact mul_left_cancel₀ hD hm
end ThomsonNine.PairAddition

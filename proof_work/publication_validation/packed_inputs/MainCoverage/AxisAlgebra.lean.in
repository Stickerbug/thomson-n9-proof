import MainCoverage.TaylorLower
import PackedTensor.IntegerBasis

noncomputable section
namespace ThomsonNine.MainAxis
open scoped BigOperators
open ThomsonNine

def powers (d : ℕ) (c : Fin d → ℝ) (s : ℝ) : ℝ := ∑ i, c i*s^i.val
def tail (ad : Fin 21 → ℝ) : ℝ := ∑ j : Fin 10, max (ad (Fin.natAdd 11 j)) 0
def truncated (af : Fin 11 → ℝ) (ad : Fin 21 → ℝ) (i : Fin 11) : ℝ :=
  af i-ad (Fin.castAdd 10 i)-(if i=0 then tail ad else 0)

theorem weighted_power_le_max (a s : ℝ) (hs : 0≤s ∧ s≤1) (n : ℕ) : a*s^n≤max a 0 := by
  have hp := pow_nonneg hs.1 n
  have h1 := pow_le_one₀ hs.1 hs.2 (n:=n)
  by_cases ha : 0≤a
  · rw [max_eq_left ha]
    nlinarith
  · rw [max_eq_right (le_of_not_ge ha)]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hp

theorem truncate_lower (af : Fin 11 → ℝ) (ad : Fin 21 → ℝ) (s : ℝ) (hs : 0≤s ∧ s≤1) :
    powers 11 (truncated af ad) s≤powers 11 af s-powers 21 ad s := by
  have htail : (∑ j : Fin 10, ad (Fin.natAdd 11 j)*s^(Fin.natAdd 11 j).val)≤tail ad :=
    Finset.sum_le_sum (fun j _ => weighted_power_le_max _ s hs _)
  have hsplit : powers 21 ad s=powers 11 (fun i => ad (Fin.castAdd 10 i)) s+
      ∑ j : Fin 10, ad (Fin.natAdd 11 j)*s^(Fin.natAdd 11 j).val := by
    exact Fin.sum_univ_add (a:=11) (b:=10) (fun i : Fin 21 => ad i*s^i.val)
  have hq : powers 11 (truncated af ad) s=
      powers 11 af s-powers 11 (fun i => ad (Fin.castAdd 10 i)) s-tail ad := by
    simp only [powers,truncated,sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul]
    simp
  rw [hsplit,hq]
  linarith

def taylorCoefficient (k : Fin 11) : ℚ := ((2*k.val).choose k.val : ℚ)/(4:ℚ)^k.val
theorem taylor_fields : ∀ k : Fin 11, ((MainCoulombTaylor.coefficients[k.val]?).getD 0 : ℚ)=taylorCoefficient k := by decide +kernel

theorem taylor_eval (s : ℝ) : MainCoulombTaylor.T.eval s=powers 11 (fun k => (taylorCoefficient k : ℝ)) s := by
  have h := RationalListPolynomial.eval_fin_sum 11 MainCoulombTaylor.coefficients
    (le_of_eq MainCoulombTaylor.length_coefficients) s
  simpa only [MainCoulombTaylor.T,powers,taylor_fields] using h

theorem finite_taylor_lower (af : Fin 11 → ℝ) (n lam s : ℝ) (hs : 0≤s)
    (h : ∀ k, af k≤n*(taylorCoefficient k : ℝ)*lam^k.val) :
    powers 11 af s≤n*MainCoulombTaylor.T.eval (lam*s) := by
  rw [taylor_eval]
  unfold powers
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have he : n*(taylorCoefficient k : ℝ)*(lam*s)^k.val=(n*(taylorCoefficient k : ℝ)*lam^k.val)*s^k.val := by
    rw [mul_pow];ring
  simp only [← mul_assoc]
  rw [he]
  exact mul_le_mul_of_nonneg_right (h k) (pow_nonneg hs _)

theorem scaled_square_minorant (d n S : ℝ) (hd : 0<d) (hS : 0<S) (h : d*n^2≤S^2) :
    n/S≤(Real.sqrt d)⁻¹ := by
  apply MainCoulombTaylor.square_minorant d (n/S) hd
  have he : d*(n/S)^2=(d*n^2)/S^2 := by ring
  rw [he]
  exact (div_le_one (sq_pos_of_pos hS)).mpr h
end ThomsonNine.MainAxis

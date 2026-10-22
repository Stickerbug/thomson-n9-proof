import PairBounds.BernsteinData

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PairBernstein75
open Polynomial ThomsonNine.IntegerListPolynomial
open scoped BigOperators

theorem oneMinusX_polynomial : realPolynomial [1,-1]=(1 : ℝ[X])-X := by
  simp [realPolynomial,ListPolynomial.polynomial]
  ring

theorem power_polynomial : ∀ n : ℕ, ∀ hn : n<76,
    realPolynomial (powerCache ⟨n,hn⟩)=((1 : ℝ[X])-X)^n := by
  intro n
  induction n with
  | zero => intro hn;rw [show (⟨0,hn⟩ : Fin 76)=0 from rfl,power_zero];simp
  | succ n ih =>
    intro hn
    have he := power_step ⟨n,by omega⟩
    change powerCache ⟨n+1,by omega⟩=IntegerListPolynomial.mul [1,-1] (powerCache ⟨n,by omega⟩) at he
    rw [he,mul_sound,oneMinusX_polynomial,ih (by omega),pow_succ']

theorem basis_polynomial (i : Fin 76) : realPolynomial (basis i)=bernsteinPolynomial ℝ 75 i.val := by
  rw [basis_fields,scale_sound,append,zeroes,power_polynomial]
  simp only [List.length_replicate,zero_add,Int.cast_natCast,C_eq_natCast,bernsteinPolynomial]
  ring

def combination (b : Fin 76 → ℚ) : List ℚ :=
  ListPolynomial.sumCoefficients (·+·) ((List.finRange 76).map
    (fun i => ((basis i).map (fun z : ℤ => (z : ℚ))).map (b i*·)))

theorem combination_polynomial (b : Fin 76 → ℚ) :
    RationalListPolynomial.realPolynomial (combination b)=
      ∑ i : Fin 76, C (b i : ℝ)*bernsteinPolynomial ℝ 75 i.val := by
  rw [combination,RationalListPolynomial.sum,List.map_map]
  have he : ((List.finRange 76).map (fun i =>
      RationalListPolynomial.realPolynomial (((basis i).map (fun z : ℤ => (z : ℚ))).map (b i*·))))=
      ((List.finRange 76).map (fun i => C (b i : ℝ)*bernsteinPolynomial ℝ 75 i.val)) := by
    apply List.map_congr_left
    intro i hi
    rw [RationalListPolynomial.scale,IntegerListPolynomial.rational_map,basis_polynomial]
  change (((List.finRange 76).map (fun i =>
      RationalListPolynomial.realPolynomial (((basis i).map (fun z : ℤ => (z : ℚ))).map (b i*·)))).sum)=_
  rw [he,← List.sum_toFinset _ (List.nodup_finRange 76)]
  have hs : (List.finRange 76).toFinset=(Finset.univ : Finset (Fin 76)) := by ext i;simp
  rw [hs]

theorem basis_nonnegative (i : Fin 76) (s : ℝ) (hs : 0≤s ∧ s≤1) :
    0≤(bernsteinPolynomial ℝ 75 i.val).eval s := by
  simp only [bernsteinPolynomial,eval_mul,eval_pow,eval_natCast,eval_X,eval_sub,eval_one]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs.1 _)) (pow_nonneg (sub_nonneg.mpr hs.2) _)

theorem basis_sum_one (s : ℝ) : (∑ i : Fin 76, (bernsteinPolynomial ℝ 75 i.val).eval s)=1 := by
  have hp : (∑ i : Fin 76, bernsteinPolynomial ℝ 75 i.val)=1 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact bernsteinPolynomial.sum ℝ 75
  have he := congrArg (fun p : ℝ[X] => p.eval s) hp
  simpa only [eval_finsetSum,eval_one] using he

theorem combination_lower (b : Fin 76 → ℚ) (c s : ℝ) (hs : 0≤s ∧ s≤1)
    (hb : ∀ i, c≤(b i : ℝ)) : c≤(RationalListPolynomial.realPolynomial (combination b)).eval s := by
  rw [combination_polynomial]
  simp only [eval_finsetSum,eval_mul,eval_C]
  calc
    c=∑ i : Fin 76, c*(bernsteinPolynomial ℝ 75 i.val).eval s := by rw [← Finset.mul_sum,basis_sum_one,mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hb i) (basis_nonnegative i s hs))
end ThomsonNine.PairBernstein75

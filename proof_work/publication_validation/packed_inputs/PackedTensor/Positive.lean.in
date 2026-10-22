import PackedTensor.LowerBound
import PackedTensor.BernsteinList
import PackedRadix.Sum

noncomputable section
namespace ThomsonNine.PackedTensor
open scoped BigOperators
open ThomsonNine.PackedRadix ThomsonNine.Semantics Polynomial

theorem bernstein_sum_one (n : ℕ) (s : ℝ) : (∑ i : Fin (n+1), bernstein n i.val s)=1 := by
  have hp : (∑ i : Fin (n+1), bernsteinPolynomial ℝ n i.val)=1 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact bernsteinPolynomial.sum ℝ n
  have he := congrArg (fun p : ℝ[X] => p.eval s) hp
  simpa only [eval_finsetSum,eval_one,basis_eval] using he

theorem product_sums (d : ℕ) (A B C : Fin d → ℝ) :
    (∑ i, ∑ j, ∑ k, A i*B j*C k)=(∑ i, A i)*(∑ j, B j)*(∑ k, C k) := by
  simp only [← Finset.mul_sum,← Finset.sum_mul]

theorem tensor_axis0 (n : ℕ) (h : Fin (n+1) → ℝ) (x : Fin 3 → ℝ) :
    tensorValue n (fun p => h p.1) x=curve n h (x 0) := by
  have he := product_sums (n+1) (fun i => h i*bernstein n i.val (x 0))
    (fun j => bernstein n j.val (x 1)) (fun k => bernstein n k.val (x 2))
  simpa only [tensorValue,tensor,curve,bernstein_sum_one,mul_one] using he

theorem tensor_axis1 (n : ℕ) (h : Fin (n+1) → ℝ) (x : Fin 3 → ℝ) :
    tensorValue n (fun p => h p.2.1) x=curve n h (x 1) := by
  have he := product_sums (n+1) (fun i => bernstein n i.val (x 0))
    (fun j => h j*bernstein n j.val (x 1)) (fun k => bernstein n k.val (x 2))
  simp only [bernstein_sum_one,one_mul,mul_one] at he
  unfold curve
  rw [← he]
  unfold tensorValue tensor
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  apply Finset.sum_congr rfl;intro k hk
  ring

theorem tensor_axis2 (n : ℕ) (h : Fin (n+1) → ℝ) (x : Fin 3 → ℝ) :
    tensorValue n (fun p => h p.2.2) x=curve n h (x 2) := by
  have he := product_sums (n+1) (fun i => bernstein n i.val (x 0))
    (fun j => bernstein n j.val (x 1)) (fun k => h k*bernstein n k.val (x 2))
  simp only [bernstein_sum_one,one_mul,mul_one] at he
  unfold curve
  rw [← he]
  unfold tensorValue tensor
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  apply Finset.sum_congr rfl;intro k hk
  ring

theorem tensor_axis (n : ℕ) (h : Fin (n+1) → ℝ) (a : Fin 3) (x : Fin 3 → ℝ) :
    tensorValue n (fun p => h (coord a p)) x=curve n h (x a) := by
  fin_cases a
  · exact tensor_axis0 n h x
  · exact tensor_axis1 n h x
  · exact tensor_axis2 n h x

theorem decoded_sum_nonnegative (n lanes g offset scale k : ℕ) (packets : Fin k → ℕ)
    (hg : k*g<2^128) (hbias : k*offset<2^128)
    (h : positiveSumOK 128 lanes g (k*offset) k packets=true)
    (hs : (0 : ℝ)<scale) (hn : (n+1)*(n+1)*(n+1)≤lanes) (p : CubeIndex (n+1)) :
    0≤∑ a, packetCoefficients n offset scale (packets a) p := by
  have hp := positiveSumOK_sound 128 lanes g (k*offset) k packets (by omega) hg hbias h
    (flat p) ((flat_lt p).trans_le hn)
  have hr : (k : ℝ)*(offset : ℝ)≤∑ a, (limb 128 (packets a) (flat p) : ℝ) := by exact_mod_cast hp
  simp only [packetCoefficients,decode]
  rw [← Finset.sum_div]
  apply div_nonneg _ (le_of_lt hs)
  rw [Finset.sum_sub_distrib]
  simpa using sub_nonneg.mpr hr

theorem packet_sum_nonnegative (n lanes g offset scale k : ℕ) (packets : Fin k → ℕ)
    (hg : k*g<2^128) (hbias : k*offset<2^128)
    (h : positiveSumOK 128 lanes g (k*offset) k packets=true)
    (hs : (0 : ℝ)<scale) (hn : (n+1)*(n+1)*(n+1)≤lanes)
    (x : Fin 3 → ℝ) (hx : ∀ a, 0≤x a ∧ x a≤1) :
    0≤tensorValue n (fun p => ∑ a, packetCoefficients n offset scale (packets a) p) x := by
  exact tensor_nonneg n _ (fun i j k => decoded_sum_nonnegative n lanes g offset scale _ packets
    hg hbias h hs hn (i,j,k)) (hx 0).1 (hx 0).2 (hx 1).1 (hx 1).2 (hx 2).1 (hx 2).2
end ThomsonNine.PackedTensor

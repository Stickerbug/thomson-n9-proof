import PackedTensor.BernsteinModel
import PackedTensor.AffineHalf

noncomputable section
namespace ThomsonNine.PackedTensor
open scoped BigOperators
open ThomsonNine.Semantics

def tensorValue (n : ℕ) (b : CubeIndex (n+1) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  tensor n (fun i j k => b (i,j,k)) (x 0) (x 1) (x 2)

def realHalf (n : ℕ) (b : CubeIndex (n+1) → ℝ) (axis : Fin 3) (right : Bool)
    (p : CubeIndex (n+1)) : ℝ :=
  if right then realRow (line b axis p) (n-(coord axis p).val) (coord axis p).val
  else realRow (line b axis p) (coord axis p).val 0

def halfPoint (axis : Fin 3) (right : Bool) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Function.update x axis ((if right then 1+x axis else x axis)/2)

theorem line_axis0 (n : ℕ) (b : CubeIndex (n+1) → ℝ) (i j k : Fin (n+1)) :
    line b 0 (i,j,k)=(fun m => b (Fin.ofNat (n+1) m,j,k)) := rfl
theorem line_axis1 (n : ℕ) (b : CubeIndex (n+1) → ℝ) (i j k : Fin (n+1)) :
    line b 1 (i,j,k)=(fun m => b (i,Fin.ofNat (n+1) m,k)) := rfl
theorem line_axis2 (n : ℕ) (b : CubeIndex (n+1) → ℝ) (i j k : Fin (n+1)) :
    line b 2 (i,j,k)=(fun m => b (i,j,Fin.ofNat (n+1) m)) := rfl

theorem curve_half (n : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (b : ℕ → ℝ) (right : Bool) (s : ℝ) :
    (∑ i : Fin (n+1), (if right then realRow b (n-i.val) i.val else realRow b i.val 0)*bernstein n i.val s)=
      curve n (fun j => b j.val) ((if right then 1+s else s)/2) := by
  cases right
  · exact left_curve n hr hb b s
  · exact right_curve n hr hb b s

theorem tensor_half_axis0 (n : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (b : CubeIndex (n+1) → ℝ) (right : Bool) (x : Fin 3 → ℝ) :
    tensorValue n (realHalf n b 0 right) x=tensorValue n b (halfPoint 0 right x) := by
  unfold tensorValue tensor
  rw [Finset.sum_comm]
  conv_lhs => arg 2;ext j;rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm];arg 2;ext j;rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [realHalf,coord,coordinate,ite_true,Fin.isValue,halfPoint,
    Function.update_self,Function.update_of_ne (by decide : (1 : Fin 3)≠0),
    Function.update_of_ne (by decide : (2 : Fin 3)≠0)]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul]
  congr 2
  simp only [line_axis0]
  have hc := curve_half n hr hb (fun m => b (Fin.ofNat (n+1) m,j,k)) right (x 0)
  simpa only [curve,Fin.ofNat_val_eq_self] using hc

theorem tensor_half_axis1 (n : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (b : CubeIndex (n+1) → ℝ) (right : Bool) (x : Fin 3 → ℝ) :
    tensorValue n (realHalf n b 1 right) x=tensorValue n b (halfPoint 1 right x) := by
  unfold tensorValue tensor
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [realHalf,coord,coordinate,Fin.isValue,show (1 : Fin 3)≠0 by decide,ite_false,
    ite_true,line_axis1,halfPoint,Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 3)≠1),
    Function.update_of_ne (by decide : (2 : Fin 3)≠1)]
  have hc := congrArg (fun y : ℝ => y*bernstein n i.val (x 0)*bernstein n k.val (x 2))
    (curve_half n hr hb (fun m => b (i,Fin.ofNat (n+1) m,k)) right (x 1))
  simp only [curve,Fin.ofNat_val_eq_self,Finset.sum_mul] at hc
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hc

theorem tensor_half_axis2 (n : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (b : CubeIndex (n+1) → ℝ) (right : Bool) (x : Fin 3 → ℝ) :
    tensorValue n (realHalf n b 2 right) x=tensorValue n b (halfPoint 2 right x) := by
  unfold tensorValue tensor
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [realHalf,coord,coordinate,Fin.isValue,show (2 : Fin 3)≠0 by decide,
    show (2 : Fin 3)≠1 by decide,ite_false,line_axis2,halfPoint,Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 3)≠2),
    Function.update_of_ne (by decide : (1 : Fin 3)≠2)]
  have hc := congrArg (fun y : ℝ => y*bernstein n i.val (x 0)*bernstein n j.val (x 1))
    (curve_half n hr hb (fun m => b (i,j,Fin.ofNat (n+1) m)) right (x 2))
  simp only [curve,Fin.ofNat_val_eq_self,Finset.sum_mul] at hc
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hc

theorem tensor_half (n : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (b : CubeIndex (n+1) → ℝ) (axis : Fin 3) (right : Bool) (x : Fin 3 → ℝ) :
    tensorValue n (realHalf n b axis right) x=tensorValue n b (halfPoint axis right x) := by
  fin_cases axis
  · exact tensor_half_axis0 n hr hb b right x
  · exact tensor_half_axis1 n hr hb b right x
  · exact tensor_half_axis2 n hr hb b right x

theorem tensor_mono (n : ℕ) (b c : CubeIndex (n+1) → ℝ) (hbc : ∀ p, b p≤c p)
    (x : Fin 3 → ℝ) (hx : ∀ a, 0≤x a ∧ x a≤1) : tensorValue n b x≤tensorValue n c x := by
  unfold tensorValue tensor
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbc (i,j,k)) (bernstein_nonneg n i.val (hx 0).1 (hx 0).2))
      (bernstein_nonneg n j.val (hx 1).1 (hx 1).2))
    (bernstein_nonneg n k.val (hx 2).1 (hx 2).2)

end ThomsonNine.PackedTensor

import PackedTensor.BernsteinList
import PackedTensor.DenseTransform

noncomputable section
namespace ThomsonNine.PackedTensor
open Polynomial ThomsonNine.RationalListPolynomial
open scoped BigOperators

def affineMatrixSpec (n : ℕ) (M : Fin (n+1) → Fin (n+1) → ℚ) (l w : ℚ) : Prop :=
  ∀ k : Fin (n+1), exactCombination n (fun i => M i k)=ExactPolynomial.pow [l,w] k.val
instance (n : ℕ) (M : Fin (n+1) → Fin (n+1) → ℚ) (l w : ℚ) : Decidable (affineMatrixSpec n M l w) :=
  inferInstanceAs (Decidable (∀ _ : Fin (n+1), _))

theorem affineMatrixSpec_sound (n : ℕ) (M : Fin (n+1) → Fin (n+1) → ℚ) (l w : ℚ)
    (h : affineMatrixSpec n M l w) (k : Fin (n+1)) (s : ℝ) :
    matrixAction (fun i j => (M i j : ℝ)) (fun i => Semantics.bernstein n i.val s) k=
      ((l : ℝ)+(w : ℝ)*s)^k.val := by
  have hp := congrArg realPolynomial (h k)
  rw [exactCombination_polynomial,ExactPolynomial.pow_sound] at hp
  have he := congrArg (fun p : ℝ[X] => p.eval s) hp
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,basis_eval] at he
  simpa only [matrixAction,cons,nil,eval_add,eval_C,eval_mul,eval_X,eval_zero,
    mul_zero,add_zero,mul_comm] using he

theorem affine_tensor_transform (n : ℕ) (M : Fin (n+1) → Fin (n+1) → ℚ) (l w : ℚ)
    (h : affineMatrixSpec n M l w) (b : CubeIndex (n+1) → ℝ) (z : Fin 3 → ℝ) :
    tensorValue n (mapAxis (fun i j => (M i j : ℝ)) 2
      (mapAxis (fun i j => (M i j : ℝ)) 1 (mapAxis (fun i j => (M i j : ℝ)) 0 b))) z=
      tri b (fun i => ((l : ℝ)+(w : ℝ)*z 0)^i.val)
        (fun j => ((l : ℝ)+(w : ℝ)*z 1)^j.val) (fun k => ((l : ℝ)+(w : ℝ)*z 2)^k.val) := by
  change tri _ _ _ _=_
  rw [tri_map2,tri_map1,tri_map0]
  have hM (s : ℝ) : matrixAction (fun i j => (M i j : ℝ)) (fun i => Semantics.bernstein n i.val s)=
      fun k => ((l : ℝ)+(w : ℝ)*s)^k.val := funext (fun k => affineMatrixSpec_sound n M l w h k s)
  rw [hM (z 0),hM (z 1),hM (z 2)]

def mapAxisInt {d : ℕ} (M : Fin d → Fin d → ℤ) (axis : Fin 3) (b : CubeIndex d → ℤ)
    (p : CubeIndex d) : ℤ := ∑ j : Fin d, M (coord axis p) j*b (replace axis p j)

theorem mapAxis_cast {d : ℕ} (M : Fin d → Fin d → ℤ) (axis : Fin 3) (b : CubeIndex d → ℤ)
    (mDen bDen : ℕ) (p : CubeIndex d) :
    mapAxis (fun i j => (M i j : ℝ)/(mDen : ℝ)) axis (fun q => (b q : ℝ)/(bDen : ℝ)) p=
      (mapAxisInt M axis b p : ℝ)/((mDen : ℝ)*(bDen : ℝ)) := by
  unfold mapAxis mapAxisInt
  simp only [div_mul_div_comm]
  rw [← Finset.sum_div]
  norm_cast

theorem curve_map (n : ℕ) (M : Fin (n+1) → Fin (n+1) → ℝ) (b : Fin (n+1) → ℝ) (s : ℝ) :
    curve n (fun i => ∑ j, M i j*b j) s=
      ∑ j, b j*matrixAction M (fun i => Semantics.bernstein n i.val s) j := by
  simp only [curve,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro j hj
  simp only [matrixAction,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i hi
  ring

end ThomsonNine.PackedTensor

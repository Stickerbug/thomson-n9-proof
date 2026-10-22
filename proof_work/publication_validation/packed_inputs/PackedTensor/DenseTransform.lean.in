import PackedTensor.TensorModel

noncomputable section
namespace ThomsonNine.PackedTensor
open scoped BigOperators

def tri {d : ℕ} (b : CubeIndex d → ℝ) (A B C : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, b (i,j,k)*A i*B j*C k
def mapAxis {d : ℕ} (M : Fin d → Fin d → ℝ) (axis : Fin 3) (b : CubeIndex d → ℝ)
    (p : CubeIndex d) : ℝ := ∑ j : Fin d, M (coord axis p) j*b (replace axis p j)
def matrixAction {d : ℕ} (M : Fin d → Fin d → ℝ) (A : Fin d → ℝ) (j : Fin d) : ℝ := ∑ i, M i j*A i

theorem tri_add {d : ℕ} (b c : CubeIndex d → ℝ) (A B C : Fin d → ℝ) :
    tri (fun p => b p+c p) A B C=tri b A B C+tri c A B C := by
  simp only [tri,add_mul,Finset.sum_add_distrib]
theorem tri_sub {d : ℕ} (b c : CubeIndex d → ℝ) (A B C : Fin d → ℝ) :
    tri (fun p => b p-c p) A B C=tri b A B C-tri c A B C := by
  simp only [tri,sub_mul,Finset.sum_sub_distrib]
theorem tri_scale {d : ℕ} (s : ℝ) (b : CubeIndex d → ℝ) (A B C : Fin d → ℝ) :
    tri (fun p => s*b p) A B C=s*tri b A B C := by
  simp only [tri,Finset.mul_sum,mul_assoc]
theorem tri_neg {d : ℕ} (b : CubeIndex d → ℝ) (A B C : Fin d → ℝ) :
    tri (fun p => -b p) A B C= -tri b A B C := by
  simp only [tri,neg_mul,Finset.sum_neg_distrib]

theorem tri_single {d : ℕ} (p : CubeIndex d) (v : ℝ) (A B C : Fin d → ℝ) :
    tri (fun q => if q=p then v else 0) A B C=v*A p.1*B p.2.1*C p.2.2 := by
  rcases p with ⟨i,j,k⟩
  simp [tri,Prod.mk.injEq,ite_and,ite_mul]

theorem tri_map0 {d : ℕ} (M : Fin d → Fin d → ℝ) (b : CubeIndex d → ℝ) (A B C : Fin d → ℝ) :
    tri (mapAxis M 0 b) A B C=tri b (matrixAction M A) B C := by
  simp only [tri,mapAxis,coord,coordinate,replace,ite_true,Fin.isValue,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2;ext j;rw [Finset.sum_comm];arg 2;ext k;rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm];arg 2;ext j;rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro j hj
  apply Finset.sum_congr rfl;intro k hk
  unfold matrixAction
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro q hq
  apply Finset.sum_congr rfl;intro i hi
  ring

theorem tri_map1 {d : ℕ} (M : Fin d → Fin d → ℝ) (b : CubeIndex d → ℝ) (A B C : Fin d → ℝ) :
    tri (mapAxis M 1 b) A B C=tri b A (matrixAction M B) C := by
  simp only [tri,mapAxis,coord,coordinate,replace,show (1 : Fin 3)≠0 by decide,ite_false,ite_true,
    Fin.isValue,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro i hi
  rw [Finset.sum_comm]
  conv_lhs => arg 2;ext k;rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro q hq
  unfold matrixAction
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro j hj
  apply Finset.sum_congr rfl;intro k hk
  ring

theorem tri_map2 {d : ℕ} (M : Fin d → Fin d → ℝ) (b : CubeIndex d → ℝ) (A B C : Fin d → ℝ) :
    tri (mapAxis M 2 b) A B C=tri b A B (matrixAction M C) := by
  simp only [tri,mapAxis,coord,coordinate,replace,show (2 : Fin 3)≠0 by decide,
    show (2 : Fin 3)≠1 by decide,ite_false,Fin.isValue,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  rw [Finset.sum_comm]
  unfold matrixAction
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro q hq
  apply Finset.sum_congr rfl;intro k hk
  ring
end ThomsonNine.PackedTensor

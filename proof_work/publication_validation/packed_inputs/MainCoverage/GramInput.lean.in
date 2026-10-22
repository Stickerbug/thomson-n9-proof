import PackedTensor.DenseTransform
import ThomsonNine.LeafSemantics

noncomputable section
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor

def deltaInt {d : ℕ} (p q : CubeIndex d) : ℤ := if q=p then 1 else 0
def gramInput (d : ℕ) [NeZero d] (p : CubeIndex d) : ℤ :=
  -deltaInt (0,0,0) p-2*deltaInt (1,1,1) p+deltaInt (2,0,0) p+deltaInt (0,2,0) p+deltaInt (0,0,2) p

theorem gramInput_cast {d : ℕ} [NeZero d] (p : CubeIndex d) :
    (gramInput d p : ℝ)= -(if p=(0,0,0) then (1:ℝ) else 0)-2*(if p=(1,1,1) then (1:ℝ) else 0)+
      (if p=(2,0,0) then (1:ℝ) else 0)+(if p=(0,2,0) then (1:ℝ) else 0)+(if p=(0,0,2) then (1:ℝ) else 0) := by
  unfold gramInput deltaInt
  split_ifs <;> norm_num

theorem tri_gramInput (d : ℕ) [NeZero d] (A B C : Fin d → ℝ) :
    tri (fun p => (gramInput d p : ℝ)) A B C=
      -A 0*B 0*C 0-2*A 1*B 1*C 1+A 2*B 0*C 0+A 0*B 2*C 0+A 0*B 0*C 2 := by
  simp_rw [gramInput_cast]
  simp only [tri_add,tri_sub,tri_neg,tri_scale,tri_single,one_mul]
  ring

attribute [local irreducible] tri

theorem gramInput_polynomial3 (x : Fin 3 → ℝ) :
    tri (fun p => (gramInput 3 p : ℝ)) (fun i => (x 0)^i.val)
      (fun j => (x 1)^j.val) (fun k => (x 2)^k.val)= -Semantics.gram (x 0) (x 1) (x 2) := by
  rw [tri_gramInput]
  norm_num [Semantics.gram]
  ring

theorem gramInput_polynomial11 (x : Fin 3 → ℝ) :
    tri (fun p => (gramInput 11 p : ℝ)) (fun i => (x 0)^i.val)
      (fun j => (x 1)^j.val) (fun k => (x 2)^k.val)= -Semantics.gram (x 0) (x 1) (x 2) := by
  rw [tri_gramInput]
  norm_num [Semantics.gram]
  ring
end ThomsonNine.PackedMain

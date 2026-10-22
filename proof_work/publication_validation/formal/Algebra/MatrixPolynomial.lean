import Matrices.Model

noncomputable section
namespace ThomsonNine.MatrixPolynomial
open Polynomial Matrix
open scoped BigOperators

def bilinear {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (P Q : Fin m → ℝ[X]) : ℝ[X] :=
  ∑ a, ∑ b, C (A a b)*P a*Q b

theorem bilinear_eval {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (P Q : Fin m → ℝ[X]) (r : ℝ) :
    (bilinear A P Q).eval r =
      (fun a => (P a).eval r) ⬝ᵥ Matrix.mulVec A (fun b => (Q b).eval r) := by
  simp only [bilinear,eval_finsetSum,eval_mul,eval_C,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem bilinear_derivative {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (P Q : Fin m → ℝ[X]) :
    (bilinear A P Q).derivative =
      bilinear A (fun a => (P a).derivative) Q+bilinear A P (fun b => (Q b).derivative) := by
  simp only [bilinear,derivative_sum,derivative_mul,derivative_C,zero_mul,zero_add,Finset.sum_add_distrib]

theorem bilinear_comm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hs : ∀ a b, A a b=A b a) (P Q : Fin m → ℝ[X]) :
    bilinear A P Q=bilinear A Q P := by
  rw [bilinear,bilinear,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hs b a]
  ring

theorem quadratic_zero {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (P : Fin m → ℝ[X]) (r : ℝ)
    (hp : Matrix.mulVec A (fun a => (P a).eval r)=0) :
    (bilinear A P P).eval r=0 := by rw [bilinear_eval,hp,dotProduct_zero]

theorem quadratic_derivative_zero {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hs : ∀ a b, A a b=A b a) (P : Fin m → ℝ[X]) (r : ℝ)
    (hp : Matrix.mulVec A (fun a => (P a).eval r)=0) :
    (bilinear A P P).derivative.eval r=0 := by
  rw [bilinear_derivative,eval_add,bilinear_comm A hs P (fun a => (P a).derivative)]
  rw [bilinear_eval,hp,dotProduct_zero]
  simp
theorem sum_bilinear {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (∑ a, ∑ b, A a b*x a*y b)=x ⬝ᵥ Matrix.mulVec A y := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem sum_NBN {m n : ℕ} (N : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin m → ℝ) :
    (∑ a, ∑ b, (N*B*N.transpose) a b*x a*y b)=
      ∑ i, ∑ j, B i j*(∑ a, N a i*x a)*(∑ b, N b j*y b) := by
  rw [sum_bilinear]
  have h : (fun i => ∑ a, N a i*x a)=Matrix.mulVec N.transpose x := rfl
  have h' : (fun j => ∑ b, N b j*y b)=Matrix.mulVec N.transpose y := rfl
  change x ⬝ᵥ Matrix.mulVec (N*B*N.transpose) y =
    ∑ i, ∑ j, B i j*(Matrix.mulVec N.transpose x i)*(Matrix.mulVec N.transpose y j)
  rw [sum_bilinear,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_transpose]
end ThomsonNine.MatrixPolynomial

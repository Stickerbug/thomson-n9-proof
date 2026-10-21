import Mathlib.LinearAlgebra.Matrix.PosDef

namespace ThomsonNine.Semantics

/-- The algebraic PSD bridge; positivity of the concrete B remains a separate certificate. -/
theorem reduced_matrix_psd {m n : Type*} [Fintype m] [Fintype n]
    {B : Matrix n n ℝ} (hB : B.PosSemidef) (N : Matrix m n ℝ) :
    (N * B * N.transpose).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hB.mul_mul_conjTranspose_same N

end ThomsonNine.Semantics

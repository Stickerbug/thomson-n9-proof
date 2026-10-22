import ThomsonNine.Construction.Algebra.IntervalPSD
import ThomsonNine.Construction.Algebra.SparseCurve

-- Isolated source: Algebra.HessianPSD
noncomputable section
namespace ThomsonNine.LocalQuadratic
open ThomsonNine.FixedInterval ThomsonNine.FixedInterval.Schur
open scoped BigOperators

def symmetricPart (H : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (H i j+H j i)/2

theorem symmetricPart_symmetric (H : Matrix (Fin 3) (Fin 3) ℝ) :
    ∀ i j, symmetricPart H i j=symmetricPart H j i := by
  intro i j
  simp only [symmetricPart]
  ring

theorem symmetricPart_mem {s : ℤ} (I : Fin 3 → Fin 3 → Bounds)
    (hI : ∀ i j, I i j=I j i) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ∀ i j, Mem s (I i j) (H i j)) (i j : Fin 3) :
    Mem s (I i j) (symmetricPart H i j) := by
  have h₁ := hH i j
  have h₂ := hH j i
  rw [← hI i j] at h₂
  constructor <;> dsimp [symmetricPart] <;> nlinarith [h₁.1,h₁.2,h₂.1,h₂.2]

theorem quadratic_symmetricPart (H : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (symmetricPart H).mulVec v=
      ∑ i : Fin 3, ∑ j : Fin 3, H i j*v j*v i := by
  simp only [dotProduct,Matrix.mulVec,symmetricPart,Fin.sum_univ_three]
  ring

theorem nonnegative_of_certificate {s : ℤ} (I : Fin 3 → Fin 3 → Bounds)
    (hI : ∀ i j, I i j=I j i) (hP : PSDSound s I)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : ∀ i j, Mem s (I i j) (H i j))
    (v : Fin 3 → ℝ) : 0≤∑ i : Fin 3, ∑ j : Fin 3, H i j*v j*v i := by
  have h := (hP (symmetricPart H) (symmetricPart_symmetric H) (symmetricPart_mem I hI H hH)).dotProduct_mulVec_nonneg v
  simpa only [star_trivial,quadratic_symmetricPart] using h
end ThomsonNine.LocalQuadratic

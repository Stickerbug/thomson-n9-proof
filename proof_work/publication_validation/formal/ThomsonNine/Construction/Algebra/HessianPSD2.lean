import ThomsonNine.Construction.Algebra.IntervalPSD
import ThomsonNine.Construction.Algebra.SparseCurve

-- Isolated source: Algebra.HessianPSD2
noncomputable section
namespace ThomsonNine.LocalQuadratic2
open ThomsonNine.FixedInterval ThomsonNine.FixedInterval.Schur
open scoped BigOperators

def symmetricPart (H : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (H i j+H j i)/2

theorem symmetricPart_symmetric (H : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ i j, symmetricPart H i j=symmetricPart H j i := by
  intro i j
  simp only [symmetricPart]
  ring

theorem symmetricPart_mem {s : ℤ} (I : Fin 2 → Fin 2 → Bounds)
    (hI : ∀ i j, I i j=I j i) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, Mem s (I i j) (H i j)) (i j : Fin 2) :
    Mem s (I i j) (symmetricPart H i j) := by
  have h₁ := hH i j
  have h₂ := hH j i
  rw [← hI i j] at h₂
  constructor <;> dsimp [symmetricPart] <;> nlinarith [h₁.1,h₁.2,h₂.1,h₂.2]

theorem quadratic_symmetricPart (H : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    v ⬝ᵥ (symmetricPart H).mulVec v=
      ∑ i : Fin 2, ∑ j : Fin 2, H i j*v j*v i := by
  simp only [dotProduct,Matrix.mulVec,symmetricPart,Fin.sum_univ_two]
  ring

theorem nonnegative_of_certificate {s : ℤ} (I : Fin 2 → Fin 2 → Bounds)
    (hI : ∀ i j, I i j=I j i) (hP : PSDSound s I)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Mem s (I i j) (H i j))
    (v : Fin 2 → ℝ) : 0≤∑ i : Fin 2, ∑ j : Fin 2, H i j*v j*v i := by
  have h := (hP (symmetricPart H) (symmetricPart_symmetric H) (symmetricPart_mem I hI H hH)).dotProduct_mulVec_nonneg v
  simpa only [star_trivial,quadratic_symmetricPart] using h
end ThomsonNine.LocalQuadratic2

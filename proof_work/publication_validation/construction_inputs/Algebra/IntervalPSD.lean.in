import ThomsonNine.Construction.Algebra.SchurPSD
import ThomsonNine.Construction.Algebra.SchurCertificate

-- Isolated source: Algebra.IntervalPSD
noncomputable section
namespace ThomsonNine.FixedInterval.Schur

def PSDSound {n : ℕ} (s : ℤ) (I : Fin n → Fin n → Bounds) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, A i j=A j i) →
    (∀ i j, Mem s (I i j) (A i j)) → A.PosSemidef
theorem empty_psdSound (s : ℤ) (I : Fin 0 → Fin 0 → Bounds) : PSDSound s I := by
  intro A hSym hMem
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    exact Fin.elim0 i
  · intro x
    simp [dotProduct]

theorem step_psdSound {n : ℕ} {s : ℤ} (hs : 0<s)
    (I : Fin (n+1) → Fin (n+1) → Bounds) (J : Fin n → Fin n → Bounds) (iv : Bounds)
    (hPos : 0<(I 0 0).lo) (hInv : InverseRule s (I 0 0) iv)
    (hNext : ∀ i j, Contains (J i j) (reducedMatrix s I iv i j))
    (hChild : PSDSound s J) : PSDSound s I := by
  intro A hSym hMem
  have hI := hInv (A 0 0) (hMem 0 0)
  have hl : (0 : ℝ)<(I 0 0).lo := by exact_mod_cast hPos
  have hs' : (0 : ℝ)<s := by exact_mod_cast hs
  have hA : 0<A 0 0 := (mul_pos_iff_of_pos_left hs').mp (hl.trans_le (hMem 0 0).1)
  apply SchurSolve.psd_of_reduced A hSym hA
  apply hChild _ (SchurSolve.reducedMatrix_symmetric A hSym)
  intro i j
  exact mem_contains (hNext i j) (reducedMatrix_mem hs I A hMem iv hI.2 i j)
end ThomsonNine.FixedInterval.Schur

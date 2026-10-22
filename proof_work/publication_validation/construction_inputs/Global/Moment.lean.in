import ThomsonNine.Construction.R.Model
import ThomsonNine.Construction.Matrices.Actual
import ThomsonNine.Construction.F.Symmetry
import ThomsonNine.ThreePointBound
import Mathlib.Analysis.InnerProductSpace.Positive

-- Isolated source: Global.Moment
noncomputable section
namespace ThomsonNine.ActualGlobal
open ThomsonNine.ThreePoint ThomsonNine.CertificateMatrices
open scoped BigOperators RealInnerProductSpace

theorem actual_moment_nonnegative {n : ℕ} (x : Fin n → R3) (hx : ∀ i, ‖x i‖=1) :
    0≤∑ i, ∑ j, ∑ l, ActualF.F ActualR.X ⟪x i,x j⟫ ⟪x i,x l⟫ ⟪x j,x l⟫ := by
  simp only [ActualF.F_eq_matrix_pairing]
  rw [sum4_swap (s := Finset.univ)]
  apply Finset.sum_nonneg
  intro k hk
  obtain ⟨r,v,hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (actual_A_psd k)
  have hvr : A ActualR.X k=∑ s, Matrix.vecMulVec (v s) (v s) := by
    simpa only [star_trivial] using hv
  rw [hvr]
  exact matDot_moment_nonneg_sos (ambientDim k) k x hx r v
end ThomsonNine.ActualGlobal

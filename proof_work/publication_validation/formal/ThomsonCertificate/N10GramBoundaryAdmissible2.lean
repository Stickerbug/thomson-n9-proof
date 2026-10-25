import ThomsonCertificate.N10TripleBoundary

namespace ThomsonTen
open ThomsonNine.ThreePoint

private theorem gramOK_uses_det {u v t : ℝ} :
    GramOK u v t ↔ u ^ 2 ≤ 1 ∧ v ^ 2 ≤ 1 ∧ t ^ 2 ≤ 1 ∧
      0 ≤ gramDet u v t := by
  simp [GramOK, gramDet]

theorem gramOK_pole_opposite_lower {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    GramOK (-h) (-h) (2 * h^2 - 1) := by
  rw [gramOK_uses_det]
  have hsq : h^2 ≤ 1 := by nlinarith [sq_nonneg (h - 1), sq_nonneg (h + 1)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith [sq_nonneg (h^2 - 1)]
  · rw [gramDet_pole_opposite_lower]

theorem gramOK_pole_opposite_lower_bottom {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    GramOK (2 * h^2 - 1) h h := by
  rw [gramOK_uses_det]
  have hsq : h^2 ≤ 1 := by nlinarith [sq_nonneg (h - 1), sq_nonneg (h + 1)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · rw [gramDet_pole_opposite_lower_bottom]

end ThomsonTen

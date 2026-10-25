import ThomsonCertificate.N10ThreePointAdapter

/-!
Exact algebraic boundary types for the D4d n=10 candidate.  The three
identically singular Gram triples are kept as small Lean lemmas so later local
boundary certificates can refer to a kernel-checked statement rather than a
floating classification.
-/

namespace ThomsonTen

open ThomsonNine.ThreePoint

def gramDet (u v t : ℝ) : ℝ := 1 + 2*u*v*t - u^2 - v^2 - t^2

theorem gramDet_poles_ring (h : ℝ) : gramDet (-1) (-h) h = 0 := by
  simp [gramDet]
  ring

theorem gramDet_pole_opposite_lower (h : ℝ) :
    gramDet (-h) (-h) (2*h^2 - 1) = 0 := by
  simp [gramDet]
  ring

theorem gramDet_pole_opposite_lower_bottom (h : ℝ) :
    gramDet (2*h^2 - 1) h h = 0 := by
  simp [gramDet]
  ring

theorem gramDet_lower_ring_type (h : ℝ) :
    gramDet (-h) (-h) (h^2) = (1-h^2)^2 := by
  simp [gramDet]
  ring

theorem gramOK_uses_gramDet {u v t : ℝ} :
    GramOK u v t ↔
      u ^ 2 ≤ 1 ∧ v ^ 2 ≤ 1 ∧ t ^ 2 ≤ 1 ∧ 0 ≤ gramDet u v t := by
  simp [GramOK, gramDet]

theorem gramDet_radical_type_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < -h^2 * (-3 + 2 * Real.sqrt 2) * (h - 1)^2 * (h + 1)^2 := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hcoef : 0 < 3 - 2 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 3 / 2)]
  have hsq : 0 < (h - 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hsq2 : 0 < (h + 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hh2 : 0 < h^2 := sq_pos_of_pos hh0
  have hA : 0 < h^2 * (3 - 2 * Real.sqrt 2) := mul_pos hh2 hcoef
  have hB : 0 < h^2 * (3 - 2 * Real.sqrt 2) * (h - 1)^2 :=
    mul_pos hA hsq
  have hC : 0 < h^2 * (3 - 2 * Real.sqrt 2) * (h - 1)^2 * (h + 1)^2 :=
    mul_pos hB hsq2
  nlinarith [hC]

end ThomsonTen

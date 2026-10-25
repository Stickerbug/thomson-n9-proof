import ThomsonCertificate.N10TripleBoundary

namespace ThomsonTen

theorem gramDet_type_two_h2_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < 2 * h^2 * (h - 1)^2 * (h + 1)^2 := by
  have h2 : 0 < h^2 := sq_pos_of_pos hh0
  have hm : 0 < (h - 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hp : 0 < (h + 1)^2 := sq_pos_of_ne_zero (by linarith)
  positivity

theorem gramDet_type_h2_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < h^2 * (h - 1)^2 * (h + 1)^2 := by
  have h2 : 0 < h^2 := sq_pos_of_pos hh0
  have hm : 0 < (h - 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hp : 0 < (h + 1)^2 := sq_pos_of_ne_zero (by linarith)
  positivity

theorem gramDet_type_radical_plus_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < h^2 * (2 * Real.sqrt 2 + 3) * (h - 1)^2 * (h + 1)^2 := by
  have h2 : 0 < h^2 := sq_pos_of_pos hh0
  have hm : 0 < (h - 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hp : 0 < (h + 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hs : 0 < 2 * Real.sqrt 2 + 3 := by positivity
  positivity

theorem gramDet_type_half_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < (h - 1)^2 * (h + 1)^2 / 2 := by
  have hm : 0 < (h - 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hp : 0 < (h + 1)^2 := sq_pos_of_ne_zero (by linarith)
  positivity

theorem gramDet_type_one_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < (h - 1)^2 * (h + 1)^2 := by
  have hm : 0 < (h - 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hp : 0 < (h + 1)^2 := sq_pos_of_ne_zero (by linarith)
  positivity

theorem gramDet_type_four_h2_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < 4 * h^2 * (h - 1)^2 * (h + 1)^2 := by
  have h2 : 0 < h^2 := sq_pos_of_pos hh0
  have hm : 0 < (h - 1)^2 := sq_pos_of_ne_zero (by linarith)
  have hp : 0 < (h + 1)^2 := sq_pos_of_ne_zero (by linarith)
  positivity

end ThomsonTen

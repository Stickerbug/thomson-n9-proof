import ThomsonNine.TwoSourceBindings
import ThomsonNine.GatheredBinding
import ThomsonNine.SparseTranslation

set_option maxRecDepth 100000

open ThomsonNine
open ThomsonNine.LocalSparseHessianAAA
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval
open ThomsonNine.Interval.SparsePolynomial

namespace ThomsonNine.GatheredTwoSource

theorem t026_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_0_0_26.mem (c .t026))
    (h1 : ThomsonNine.TwoSourceBinding.R2_0_0_26.mem (c .t027))
    (ha : ThomsonNine.TwoSourceBinding.A_0_0_26.mem (a 2)) :
    (coefficientInterval .t026).mem (ThomsonNine.GatheredBinding.gathered (exponents .t026) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t026 i ≤ exponents t i)) = [.t026, .t027] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t026) (exponents .t026) (c .t026) a = c .t026 := by
    have h : exponents .t026 = ![0, 0, 26] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t027) (exponents .t026) (c .t027) a = (27 * c .t027) * a 2 := by
    have hk : exponents .t026 = ![0, 0, 26] := rfl
    have h : exponents .t027 = ![0, 0, 27] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t026_0_0_26_interval_bound (c .t026) (c .t027) (a 2) h0 h1 ha

theorem t136_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_0_10_9.mem (c .t136))
    (h1 : ThomsonNine.TwoSourceBinding.R2_0_10_9.mem (c .t137))
    (ha : ThomsonNine.TwoSourceBinding.A_0_10_9.mem (a 2)) :
    (coefficientInterval .t136).mem (ThomsonNine.GatheredBinding.gathered (exponents .t136) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t136 i ≤ exponents t i)) = [.t136, .t137] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t136) (exponents .t136) (c .t136) a = c .t136 := by
    have h : exponents .t136 = ![0, 10, 9] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t137) (exponents .t136) (c .t137) a = (10 * c .t137) * a 2 := by
    have hk : exponents .t136 = ![0, 10, 9] := rfl
    have h : exponents .t137 = ![0, 10, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t136_0_10_9_interval_bound (c .t136) (c .t137) (a 2) h0 h1 ha

theorem t153_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_0_26_0.mem (c .t153))
    (h1 : ThomsonNine.TwoSourceBinding.R2_0_26_0.mem (c .t154))
    (ha : ThomsonNine.TwoSourceBinding.A_0_26_0.mem (a 1)) :
    (coefficientInterval .t153).mem (ThomsonNine.GatheredBinding.gathered (exponents .t153) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t153 i ≤ exponents t i)) = [.t153, .t154] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t153) (exponents .t153) (c .t153) a = c .t153 := by
    have h : exponents .t153 = ![0, 26, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t154) (exponents .t153) (c .t154) a = (27 * c .t154) * a 1 := by
    have hk : exponents .t153 = ![0, 26, 0] := rfl
    have h : exponents .t154 = ![0, 27, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t153_0_26_0_interval_bound (c .t153) (c .t154) (a 1) h0 h1 ha

theorem t245_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_1_8_9.mem (c .t245))
    (h1 : ThomsonNine.TwoSourceBinding.R2_1_8_9.mem (c .t255))
    (ha : ThomsonNine.TwoSourceBinding.A_1_8_9.mem (a 1)) :
    (coefficientInterval .t245).mem (ThomsonNine.GatheredBinding.gathered (exponents .t245) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t245 i ≤ exponents t i)) = [.t245, .t255] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t245) (exponents .t245) (c .t245) a = c .t245 := by
    have h : exponents .t245 = ![1, 8, 9] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t255) (exponents .t245) (c .t255) a = (9 * c .t255) * a 1 := by
    have hk : exponents .t245 = ![1, 8, 9] := rfl
    have h : exponents .t255 = ![1, 9, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t245_1_8_9_interval_bound (c .t245) (c .t255) (a 1) h0 h1 ha

theorem t254_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_1_9_8.mem (c .t254))
    (h1 : ThomsonNine.TwoSourceBinding.R2_1_9_8.mem (c .t255))
    (ha : ThomsonNine.TwoSourceBinding.A_1_9_8.mem (a 2)) :
    (coefficientInterval .t254).mem (ThomsonNine.GatheredBinding.gathered (exponents .t254) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t254 i ≤ exponents t i)) = [.t254, .t255] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t254) (exponents .t254) (c .t254) a = c .t254 := by
    have h : exponents .t254 = ![1, 9, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t255) (exponents .t254) (c .t255) a = (9 * c .t255) * a 2 := by
    have hk : exponents .t254 = ![1, 9, 8] := rfl
    have h : exponents .t255 = ![1, 9, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t254_1_9_8_interval_bound (c .t254) (c .t255) (a 2) h0 h1 ha

theorem t331_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_2_7_8.mem (c .t331))
    (h1 : ThomsonNine.TwoSourceBinding.R2_2_7_8.mem (c .t340))
    (ha : ThomsonNine.TwoSourceBinding.A_2_7_8.mem (a 1)) :
    (coefficientInterval .t331).mem (ThomsonNine.GatheredBinding.gathered (exponents .t331) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t331 i ≤ exponents t i)) = [.t331, .t340] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t331) (exponents .t331) (c .t331) a = c .t331 := by
    have h : exponents .t331 = ![2, 7, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t340) (exponents .t331) (c .t340) a = (8 * c .t340) * a 1 := by
    have hk : exponents .t331 = ![2, 7, 8] := rfl
    have h : exponents .t340 = ![2, 8, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t331_2_7_8_interval_bound (c .t331) (c .t340) (a 1) h0 h1 ha

theorem t339_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_2_8_7.mem (c .t339))
    (h1 : ThomsonNine.TwoSourceBinding.R2_2_8_7.mem (c .t340))
    (ha : ThomsonNine.TwoSourceBinding.A_2_8_7.mem (a 2)) :
    (coefficientInterval .t339).mem (ThomsonNine.GatheredBinding.gathered (exponents .t339) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t339 i ≤ exponents t i)) = [.t339, .t340] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t339) (exponents .t339) (c .t339) a = c .t339 := by
    have h : exponents .t339 = ![2, 8, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t340) (exponents .t339) (c .t340) a = (8 * c .t340) * a 2 := by
    have hk : exponents .t339 = ![2, 8, 7] := rfl
    have h : exponents .t340 = ![2, 8, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t339_2_8_7_interval_bound (c .t339) (c .t340) (a 2) h0 h1 ha

theorem t405_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_3_6_7.mem (c .t405))
    (h1 : ThomsonNine.TwoSourceBinding.R2_3_6_7.mem (c .t413))
    (ha : ThomsonNine.TwoSourceBinding.A_3_6_7.mem (a 1)) :
    (coefficientInterval .t405).mem (ThomsonNine.GatheredBinding.gathered (exponents .t405) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t405 i ≤ exponents t i)) = [.t405, .t413] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t405) (exponents .t405) (c .t405) a = c .t405 := by
    have h : exponents .t405 = ![3, 6, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t413) (exponents .t405) (c .t413) a = (7 * c .t413) * a 1 := by
    have hk : exponents .t405 = ![3, 6, 7] := rfl
    have h : exponents .t413 = ![3, 7, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t405_3_6_7_interval_bound (c .t405) (c .t413) (a 1) h0 h1 ha

theorem t412_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_3_7_6.mem (c .t412))
    (h1 : ThomsonNine.TwoSourceBinding.R2_3_7_6.mem (c .t413))
    (ha : ThomsonNine.TwoSourceBinding.A_3_7_6.mem (a 2)) :
    (coefficientInterval .t412).mem (ThomsonNine.GatheredBinding.gathered (exponents .t412) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t412 i ≤ exponents t i)) = [.t412, .t413] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t412) (exponents .t412) (c .t412) a = c .t412 := by
    have h : exponents .t412 = ![3, 7, 6] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t413) (exponents .t412) (c .t413) a = (7 * c .t413) * a 2 := by
    have hk : exponents .t412 = ![3, 7, 6] := rfl
    have h : exponents .t413 = ![3, 7, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t412_3_7_6_interval_bound (c .t412) (c .t413) (a 2) h0 h1 ha

theorem t471_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_4_5_6.mem (c .t471))
    (h1 : ThomsonNine.TwoSourceBinding.R2_4_5_6.mem (c .t478))
    (ha : ThomsonNine.TwoSourceBinding.A_4_5_6.mem (a 1)) :
    (coefficientInterval .t471).mem (ThomsonNine.GatheredBinding.gathered (exponents .t471) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t471 i ≤ exponents t i)) = [.t471, .t478] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t471) (exponents .t471) (c .t471) a = c .t471 := by
    have h : exponents .t471 = ![4, 5, 6] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t478) (exponents .t471) (c .t478) a = (6 * c .t478) * a 1 := by
    have hk : exponents .t471 = ![4, 5, 6] := rfl
    have h : exponents .t478 = ![4, 6, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t471_4_5_6_interval_bound (c .t471) (c .t478) (a 1) h0 h1 ha

theorem t477_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_4_6_5.mem (c .t477))
    (h1 : ThomsonNine.TwoSourceBinding.R2_4_6_5.mem (c .t478))
    (ha : ThomsonNine.TwoSourceBinding.A_4_6_5.mem (a 2)) :
    (coefficientInterval .t477).mem (ThomsonNine.GatheredBinding.gathered (exponents .t477) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t477 i ≤ exponents t i)) = [.t477, .t478] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t477) (exponents .t477) (c .t477) a = c .t477 := by
    have h : exponents .t477 = ![4, 6, 5] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t478) (exponents .t477) (c .t478) a = (6 * c .t478) * a 2 := by
    have hk : exponents .t477 = ![4, 6, 5] := rfl
    have h : exponents .t478 = ![4, 6, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t477_4_6_5_interval_bound (c .t477) (c .t478) (a 2) h0 h1 ha

theorem t533_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_5_4_6.mem (c .t533))
    (h1 : ThomsonNine.TwoSourceBinding.R2_5_4_6.mem (c .t599))
    (ha : ThomsonNine.TwoSourceBinding.A_5_4_6.mem (a 0)) :
    (coefficientInterval .t533).mem (ThomsonNine.GatheredBinding.gathered (exponents .t533) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t533 i ≤ exponents t i)) = [.t533, .t599] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t533) (exponents .t533) (c .t533) a = c .t533 := by
    have h : exponents .t533 = ![5, 4, 6] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t599) (exponents .t533) (c .t599) a = (6 * c .t599) * a 0 := by
    have hk : exponents .t533 = ![5, 4, 6] := rfl
    have h : exponents .t599 = ![6, 4, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t533_5_4_6_interval_bound (c .t533) (c .t599) (a 0) h0 h1 ha

theorem t544_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_5_6_4.mem (c .t544))
    (h1 : ThomsonNine.TwoSourceBinding.R2_5_6_4.mem (c .t609))
    (ha : ThomsonNine.TwoSourceBinding.A_5_6_4.mem (a 0)) :
    (coefficientInterval .t544).mem (ThomsonNine.GatheredBinding.gathered (exponents .t544) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t544 i ≤ exponents t i)) = [.t544, .t609] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t544) (exponents .t544) (c .t544) a = c .t544 := by
    have h : exponents .t544 = ![5, 6, 4] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t609) (exponents .t544) (c .t609) a = (6 * c .t609) * a 0 := by
    have hk : exponents .t544 = ![5, 6, 4] := rfl
    have h : exponents .t609 = ![6, 6, 4] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t544_5_6_4_interval_bound (c .t544) (c .t609) (a 0) h0 h1 ha

theorem t592_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_6_3_7.mem (c .t592))
    (h1 : ThomsonNine.TwoSourceBinding.R2_6_3_7.mem (c .t657))
    (ha : ThomsonNine.TwoSourceBinding.A_6_3_7.mem (a 0)) :
    (coefficientInterval .t592).mem (ThomsonNine.GatheredBinding.gathered (exponents .t592) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t592 i ≤ exponents t i)) = [.t592, .t657] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t592) (exponents .t592) (c .t592) a = c .t592 := by
    have h : exponents .t592 = ![6, 3, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t657) (exponents .t592) (c .t657) a = (7 * c .t657) * a 0 := by
    have hk : exponents .t592 = ![6, 3, 7] := rfl
    have h : exponents .t657 = ![7, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t592_6_3_7_interval_bound (c .t592) (c .t657) (a 0) h0 h1 ha

theorem t598_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_6_4_5.mem (c .t598))
    (h1 : ThomsonNine.TwoSourceBinding.R2_6_4_5.mem (c .t599))
    (ha : ThomsonNine.TwoSourceBinding.A_6_4_5.mem (a 2)) :
    (coefficientInterval .t598).mem (ThomsonNine.GatheredBinding.gathered (exponents .t598) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t598 i ≤ exponents t i)) = [.t598, .t599] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t598) (exponents .t598) (c .t598) a = c .t598 := by
    have h : exponents .t598 = ![6, 4, 5] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t599) (exponents .t598) (c .t599) a = (6 * c .t599) * a 2 := by
    have hk : exponents .t598 = ![6, 4, 5] := rfl
    have h : exponents .t599 = ![6, 4, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t598_6_4_5_interval_bound (c .t598) (c .t599) (a 2) h0 h1 ha

theorem t604_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_6_5_4.mem (c .t604))
    (h1 : ThomsonNine.TwoSourceBinding.R2_6_5_4.mem (c .t609))
    (ha : ThomsonNine.TwoSourceBinding.A_6_5_4.mem (a 1)) :
    (coefficientInterval .t604).mem (ThomsonNine.GatheredBinding.gathered (exponents .t604) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t604 i ≤ exponents t i)) = [.t604, .t609] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t604) (exponents .t604) (c .t604) a = c .t604 := by
    have h : exponents .t604 = ![6, 5, 4] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t609) (exponents .t604) (c .t609) a = (6 * c .t609) * a 1 := by
    have hk : exponents .t604 = ![6, 5, 4] := rfl
    have h : exponents .t609 = ![6, 6, 4] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t604_6_5_4_interval_bound (c .t604) (c .t609) (a 1) h0 h1 ha

theorem t613_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_6_7_3.mem (c .t613))
    (h1 : ThomsonNine.TwoSourceBinding.R2_6_7_3.mem (c .t673))
    (ha : ThomsonNine.TwoSourceBinding.A_6_7_3.mem (a 0)) :
    (coefficientInterval .t613).mem (ThomsonNine.GatheredBinding.gathered (exponents .t613) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t613 i ≤ exponents t i)) = [.t613, .t673] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t613) (exponents .t613) (c .t613) a = c .t613 := by
    have h : exponents .t613 = ![6, 7, 3] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t673) (exponents .t613) (c .t673) a = (7 * c .t673) * a 0 := by
    have hk : exponents .t613 = ![6, 7, 3] := rfl
    have h : exponents .t673 = ![7, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t613_6_7_3_interval_bound (c .t613) (c .t673) (a 0) h0 h1 ha

theorem t649_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_7_2_8.mem (c .t649))
    (h1 : ThomsonNine.TwoSourceBinding.R2_7_2_8.mem (c .t709))
    (ha : ThomsonNine.TwoSourceBinding.A_7_2_8.mem (a 0)) :
    (coefficientInterval .t649).mem (ThomsonNine.GatheredBinding.gathered (exponents .t649) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t649 i ≤ exponents t i)) = [.t649, .t709] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t649) (exponents .t649) (c .t649) a = c .t649 := by
    have h : exponents .t649 = ![7, 2, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t709) (exponents .t649) (c .t709) a = (8 * c .t709) * a 0 := by
    have hk : exponents .t649 = ![7, 2, 8] := rfl
    have h : exponents .t709 = ![8, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t649_7_2_8_interval_bound (c .t649) (c .t709) (a 0) h0 h1 ha

theorem t656_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_7_3_6.mem (c .t656))
    (h1 : ThomsonNine.TwoSourceBinding.R2_7_3_6.mem (c .t657))
    (ha : ThomsonNine.TwoSourceBinding.A_7_3_6.mem (a 2)) :
    (coefficientInterval .t656).mem (ThomsonNine.GatheredBinding.gathered (exponents .t656) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t656 i ≤ exponents t i)) = [.t656, .t657] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t656) (exponents .t656) (c .t656) a = c .t656 := by
    have h : exponents .t656 = ![7, 3, 6] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t657) (exponents .t656) (c .t657) a = (7 * c .t657) * a 2 := by
    have hk : exponents .t656 = ![7, 3, 6] := rfl
    have h : exponents .t657 = ![7, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t656_7_3_6_interval_bound (c .t656) (c .t657) (a 2) h0 h1 ha

theorem t669_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_7_6_3.mem (c .t669))
    (h1 : ThomsonNine.TwoSourceBinding.R2_7_6_3.mem (c .t673))
    (ha : ThomsonNine.TwoSourceBinding.A_7_6_3.mem (a 1)) :
    (coefficientInterval .t669).mem (ThomsonNine.GatheredBinding.gathered (exponents .t669) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t669 i ≤ exponents t i)) = [.t669, .t673] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t669) (exponents .t669) (c .t669) a = c .t669 := by
    have h : exponents .t669 = ![7, 6, 3] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t673) (exponents .t669) (c .t673) a = (7 * c .t673) * a 1 := by
    have hk : exponents .t669 = ![7, 6, 3] := rfl
    have h : exponents .t673 = ![7, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t669_7_6_3_interval_bound (c .t669) (c .t673) (a 1) h0 h1 ha

theorem t676_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_7_8_2.mem (c .t676))
    (h1 : ThomsonNine.TwoSourceBinding.R2_7_8_2.mem (c .t727))
    (ha : ThomsonNine.TwoSourceBinding.A_7_8_2.mem (a 0)) :
    (coefficientInterval .t676).mem (ThomsonNine.GatheredBinding.gathered (exponents .t676) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t676 i ≤ exponents t i)) = [.t676, .t727] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t676) (exponents .t676) (c .t676) a = c .t676 := by
    have h : exponents .t676 = ![7, 8, 2] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t727) (exponents .t676) (c .t727) a = (8 * c .t727) * a 0 := by
    have hk : exponents .t676 = ![7, 8, 2] := rfl
    have h : exponents .t727 = ![8, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t676_7_8_2_interval_bound (c .t676) (c .t727) (a 0) h0 h1 ha

theorem t700_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_8_1_9.mem (c .t700))
    (h1 : ThomsonNine.TwoSourceBinding.R2_8_1_9.mem (c .t751))
    (ha : ThomsonNine.TwoSourceBinding.A_8_1_9.mem (a 0)) :
    (coefficientInterval .t700).mem (ThomsonNine.GatheredBinding.gathered (exponents .t700) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t700 i ≤ exponents t i)) = [.t700, .t751] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t700) (exponents .t700) (c .t700) a = c .t700 := by
    have h : exponents .t700 = ![8, 1, 9] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t751) (exponents .t700) (c .t751) a = (9 * c .t751) * a 0 := by
    have hk : exponents .t700 = ![8, 1, 9] := rfl
    have h : exponents .t751 = ![9, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t700_8_1_9_interval_bound (c .t700) (c .t751) (a 0) h0 h1 ha

theorem t708_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_8_2_7.mem (c .t708))
    (h1 : ThomsonNine.TwoSourceBinding.R2_8_2_7.mem (c .t709))
    (ha : ThomsonNine.TwoSourceBinding.A_8_2_7.mem (a 2)) :
    (coefficientInterval .t708).mem (ThomsonNine.GatheredBinding.gathered (exponents .t708) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t708 i ≤ exponents t i)) = [.t708, .t709] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t708) (exponents .t708) (c .t708) a = c .t708 := by
    have h : exponents .t708 = ![8, 2, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t709) (exponents .t708) (c .t709) a = (8 * c .t709) * a 2 := by
    have hk : exponents .t708 = ![8, 2, 7] := rfl
    have h : exponents .t709 = ![8, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t708_8_2_7_interval_bound (c .t708) (c .t709) (a 2) h0 h1 ha

theorem t724_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_8_7_2.mem (c .t724))
    (h1 : ThomsonNine.TwoSourceBinding.R2_8_7_2.mem (c .t727))
    (ha : ThomsonNine.TwoSourceBinding.A_8_7_2.mem (a 1)) :
    (coefficientInterval .t724).mem (ThomsonNine.GatheredBinding.gathered (exponents .t724) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t724 i ≤ exponents t i)) = [.t724, .t727] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t724) (exponents .t724) (c .t724) a = c .t724 := by
    have h : exponents .t724 = ![8, 7, 2] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t727) (exponents .t724) (c .t727) a = (8 * c .t727) * a 1 := by
    have hk : exponents .t724 = ![8, 7, 2] := rfl
    have h : exponents .t727 = ![8, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t724_8_7_2_interval_bound (c .t724) (c .t727) (a 1) h0 h1 ha

theorem t729_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_8_9_1.mem (c .t729))
    (h1 : ThomsonNine.TwoSourceBinding.R2_8_9_1.mem (c .t767))
    (ha : ThomsonNine.TwoSourceBinding.A_8_9_1.mem (a 0)) :
    (coefficientInterval .t729).mem (ThomsonNine.GatheredBinding.gathered (exponents .t729) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t729 i ≤ exponents t i)) = [.t729, .t767] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t729) (exponents .t729) (c .t729) a = c .t729 := by
    have h : exponents .t729 = ![8, 9, 1] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t767) (exponents .t729) (c .t767) a = (9 * c .t767) * a 0 := by
    have hk : exponents .t729 = ![8, 9, 1] := rfl
    have h : exponents .t767 = ![9, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t729_8_9_1_interval_bound (c .t729) (c .t767) (a 0) h0 h1 ha

theorem t741_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_9_0_10.mem (c .t741))
    (h1 : ThomsonNine.TwoSourceBinding.R2_9_0_10.mem (c .t779))
    (ha : ThomsonNine.TwoSourceBinding.A_9_0_10.mem (a 0)) :
    (coefficientInterval .t741).mem (ThomsonNine.GatheredBinding.gathered (exponents .t741) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t741 i ≤ exponents t i)) = [.t741, .t779] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t741) (exponents .t741) (c .t741) a = c .t741 := by
    have h : exponents .t741 = ![9, 0, 10] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t779) (exponents .t741) (c .t779) a = (10 * c .t779) * a 0 := by
    have hk : exponents .t741 = ![9, 0, 10] := rfl
    have h : exponents .t779 = ![10, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t741_9_0_10_interval_bound (c .t741) (c .t779) (a 0) h0 h1 ha

theorem t750_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_9_1_8.mem (c .t750))
    (h1 : ThomsonNine.TwoSourceBinding.R2_9_1_8.mem (c .t751))
    (ha : ThomsonNine.TwoSourceBinding.A_9_1_8.mem (a 2)) :
    (coefficientInterval .t750).mem (ThomsonNine.GatheredBinding.gathered (exponents .t750) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t750 i ≤ exponents t i)) = [.t750, .t751] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t750) (exponents .t750) (c .t750) a = c .t750 := by
    have h : exponents .t750 = ![9, 1, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t751) (exponents .t750) (c .t751) a = (9 * c .t751) * a 2 := by
    have hk : exponents .t750 = ![9, 1, 8] := rfl
    have h : exponents .t751 = ![9, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t750_9_1_8_interval_bound (c .t750) (c .t751) (a 2) h0 h1 ha

theorem t765_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_9_8_1.mem (c .t765))
    (h1 : ThomsonNine.TwoSourceBinding.R2_9_8_1.mem (c .t767))
    (ha : ThomsonNine.TwoSourceBinding.A_9_8_1.mem (a 1)) :
    (coefficientInterval .t765).mem (ThomsonNine.GatheredBinding.gathered (exponents .t765) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t765 i ≤ exponents t i)) = [.t765, .t767] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t765) (exponents .t765) (c .t765) a = c .t765 := by
    have h : exponents .t765 = ![9, 8, 1] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t767) (exponents .t765) (c .t767) a = (9 * c .t767) * a 1 := by
    have hk : exponents .t765 = ![9, 8, 1] := rfl
    have h : exponents .t767 = ![9, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t765_9_8_1_interval_bound (c .t765) (c .t767) (a 1) h0 h1 ha

theorem t768_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_9_10_0.mem (c .t768))
    (h1 : ThomsonNine.TwoSourceBinding.R2_9_10_0.mem (c .t789))
    (ha : ThomsonNine.TwoSourceBinding.A_9_10_0.mem (a 0)) :
    (coefficientInterval .t768).mem (ThomsonNine.GatheredBinding.gathered (exponents .t768) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t768 i ≤ exponents t i)) = [.t768, .t789] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t768) (exponents .t768) (c .t768) a = c .t768 := by
    have h : exponents .t768 = ![9, 10, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t789) (exponents .t768) (c .t789) a = (10 * c .t789) * a 0 := by
    have hk : exponents .t768 = ![9, 10, 0] := rfl
    have h : exponents .t789 = ![10, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t768_9_10_0_interval_bound (c .t768) (c .t789) (a 0) h0 h1 ha

theorem t778_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_10_0_9.mem (c .t778))
    (h1 : ThomsonNine.TwoSourceBinding.R2_10_0_9.mem (c .t779))
    (ha : ThomsonNine.TwoSourceBinding.A_10_0_9.mem (a 2)) :
    (coefficientInterval .t778).mem (ThomsonNine.GatheredBinding.gathered (exponents .t778) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t778 i ≤ exponents t i)) = [.t778, .t779] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t778) (exponents .t778) (c .t778) a = c .t778 := by
    have h : exponents .t778 = ![10, 0, 9] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t779) (exponents .t778) (c .t779) a = (10 * c .t779) * a 2 := by
    have hk : exponents .t778 = ![10, 0, 9] := rfl
    have h : exponents .t779 = ![10, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t778_10_0_9_interval_bound (c .t778) (c .t779) (a 2) h0 h1 ha

theorem t788_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_10_9_0.mem (c .t788))
    (h1 : ThomsonNine.TwoSourceBinding.R2_10_9_0.mem (c .t789))
    (ha : ThomsonNine.TwoSourceBinding.A_10_9_0.mem (a 1)) :
    (coefficientInterval .t788).mem (ThomsonNine.GatheredBinding.gathered (exponents .t788) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t788 i ≤ exponents t i)) = [.t788, .t789] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t788) (exponents .t788) (c .t788) a = c .t788 := by
    have h : exponents .t788 = ![10, 9, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t789) (exponents .t788) (c .t789) a = (10 * c .t789) * a 1 := by
    have hk : exponents .t788 = ![10, 9, 0] := rfl
    have h : exponents .t789 = ![10, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t788_10_9_0_interval_bound (c .t788) (c .t789) (a 1) h0 h1 ha

theorem t805_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_26_0_0.mem (c .t805))
    (h1 : ThomsonNine.TwoSourceBinding.R2_26_0_0.mem (c .t806))
    (ha : ThomsonNine.TwoSourceBinding.A_26_0_0.mem (a 0)) :
    (coefficientInterval .t805).mem (ThomsonNine.GatheredBinding.gathered (exponents .t805) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t805 i ≤ exponents t i)) = [.t805, .t806] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t805) (exponents .t805) (c .t805) a = c .t805 := by
    have h : exponents .t805 = ![26, 0, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t806) (exponents .t805) (c .t806) a = (27 * c .t806) * a 0 := by
    have hk : exponents .t805 = ![26, 0, 0] := rfl
    have h : exponents .t806 = ![27, 0, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t805_26_0_0_interval_bound (c .t805) (c .t806) (a 0) h0 h1 ha

end ThomsonNine.GatheredTwoSource

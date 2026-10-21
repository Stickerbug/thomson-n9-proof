import ThomsonNine.ChainBindings
import ThomsonNine.GatheredBinding
import ThomsonNine.SparseTranslation

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open ThomsonNine
open ThomsonNine.LocalSparseHessianAAA
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval
open ThomsonNine.Interval.SparsePolynomial

namespace ThomsonNine.GatheredChain

theorem t024_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_0_0_24.mem (c .t024))
    (h1 : ThomsonNine.ChainBinding.R1_0_0_24.mem (c .t025))
    (h2 : ThomsonNine.ChainBinding.R2_0_0_24.mem (c .t026))
    (h3 : ThomsonNine.ChainBinding.R3_0_0_24.mem (c .t027))
    (ha : ThomsonNine.ChainBinding.A_0_0_24.mem (a 2)) :
    (coefficientInterval .t024).mem (ThomsonNine.GatheredBinding.gathered (exponents .t024) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t024 i ≤ exponents t i)) = [.t024, .t025, .t026, .t027] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t024) (exponents .t024) (c .t024) a = c .t024 := by
    have h : exponents .t024 = ![0, 0, 24] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t025) (exponents .t024) (c .t025) a = ((25 * c .t025) * a 2) := by
    have hk : exponents .t024 = ![0, 0, 24] := rfl
    have h : exponents .t025 = ![0, 0, 25] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t026) (exponents .t024) (c .t026) a = (((325 * c .t026) * a 2) * a 2) := by
    have hk : exponents .t024 = ![0, 0, 24] := rfl
    have h : exponents .t026 = ![0, 0, 26] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 26 24 = 325 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t027) (exponents .t024) (c .t027) a = ((((2925 * c .t027) * a 2) * a 2) * a 2) := by
    have hk : exponents .t024 = ![0, 0, 24] := rfl
    have h : exponents .t027 = ![0, 0, 27] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 27 24 = 2925 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t024_0_0_24_interval_bound (c .t024) (c .t025) (c .t026) (c .t027) (a := a 2) h0 h1 h2 h3 ha

theorem t025_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_0_0_25.mem (c .t025))
    (h1 : ThomsonNine.ChainBinding.R1_0_0_25.mem (c .t026))
    (h2 : ThomsonNine.ChainBinding.R2_0_0_25.mem (c .t027))
    (ha : ThomsonNine.ChainBinding.A_0_0_25.mem (a 2)) :
    (coefficientInterval .t025).mem (ThomsonNine.GatheredBinding.gathered (exponents .t025) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t025 i ≤ exponents t i)) = [.t025, .t026, .t027] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t025) (exponents .t025) (c .t025) a = c .t025 := by
    have h : exponents .t025 = ![0, 0, 25] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t026) (exponents .t025) (c .t026) a = ((26 * c .t026) * a 2) := by
    have hk : exponents .t025 = ![0, 0, 25] := rfl
    have h : exponents .t026 = ![0, 0, 26] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t027) (exponents .t025) (c .t027) a = (((351 * c .t027) * a 2) * a 2) := by
    have hk : exponents .t025 = ![0, 0, 25] := rfl
    have h : exponents .t027 = ![0, 0, 27] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 27 25 = 351 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t025_0_0_25_interval_bound (c .t025) (c .t026) (c .t027) (a := a 2) h0 h1 h2 ha

theorem t104_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_0_7_10.mem (c .t104))
    (h1 : ThomsonNine.ChainBinding.R1_0_7_10.mem (c .t115))
    (h2 : ThomsonNine.ChainBinding.R2_0_7_10.mem (c .t126))
    (h3 : ThomsonNine.ChainBinding.R3_0_7_10.mem (c .t137))
    (ha : ThomsonNine.ChainBinding.A_0_7_10.mem (a 1)) :
    (coefficientInterval .t104).mem (ThomsonNine.GatheredBinding.gathered (exponents .t104) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t104 i ≤ exponents t i)) = [.t104, .t115, .t126, .t137] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t104) (exponents .t104) (c .t104) a = c .t104 := by
    have h : exponents .t104 = ![0, 7, 10] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t115) (exponents .t104) (c .t115) a = ((8 * c .t115) * a 1) := by
    have hk : exponents .t104 = ![0, 7, 10] := rfl
    have h : exponents .t115 = ![0, 8, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t126) (exponents .t104) (c .t126) a = (((36 * c .t126) * a 1) * a 1) := by
    have hk : exponents .t104 = ![0, 7, 10] := rfl
    have h : exponents .t126 = ![0, 9, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t137) (exponents .t104) (c .t137) a = ((((120 * c .t137) * a 1) * a 1) * a 1) := by
    have hk : exponents .t104 = ![0, 7, 10] := rfl
    have h : exponents .t137 = ![0, 10, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 7 = 120 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t104_0_7_10_interval_bound (c .t104) (c .t115) (c .t126) (c .t137) (a := a 1) h0 h1 h2 h3 ha

theorem t115_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_0_8_10.mem (c .t115))
    (h1 : ThomsonNine.ChainBinding.R1_0_8_10.mem (c .t126))
    (h2 : ThomsonNine.ChainBinding.R2_0_8_10.mem (c .t137))
    (ha : ThomsonNine.ChainBinding.A_0_8_10.mem (a 1)) :
    (coefficientInterval .t115).mem (ThomsonNine.GatheredBinding.gathered (exponents .t115) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t115 i ≤ exponents t i)) = [.t115, .t126, .t137] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t115) (exponents .t115) (c .t115) a = c .t115 := by
    have h : exponents .t115 = ![0, 8, 10] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t126) (exponents .t115) (c .t126) a = ((9 * c .t126) * a 1) := by
    have hk : exponents .t115 = ![0, 8, 10] := rfl
    have h : exponents .t126 = ![0, 9, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t137) (exponents .t115) (c .t137) a = (((45 * c .t137) * a 1) * a 1) := by
    have hk : exponents .t115 = ![0, 8, 10] := rfl
    have h : exponents .t137 = ![0, 10, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 8 = 45 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t115_0_8_10_interval_bound (c .t115) (c .t126) (c .t137) (a := a 1) h0 h1 h2 ha

theorem t134_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_0_10_7.mem (c .t134))
    (h1 : ThomsonNine.ChainBinding.R1_0_10_7.mem (c .t135))
    (h2 : ThomsonNine.ChainBinding.R2_0_10_7.mem (c .t136))
    (h3 : ThomsonNine.ChainBinding.R3_0_10_7.mem (c .t137))
    (ha : ThomsonNine.ChainBinding.A_0_10_7.mem (a 2)) :
    (coefficientInterval .t134).mem (ThomsonNine.GatheredBinding.gathered (exponents .t134) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t134 i ≤ exponents t i)) = [.t134, .t135, .t136, .t137] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t134) (exponents .t134) (c .t134) a = c .t134 := by
    have h : exponents .t134 = ![0, 10, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t135) (exponents .t134) (c .t135) a = ((8 * c .t135) * a 2) := by
    have hk : exponents .t134 = ![0, 10, 7] := rfl
    have h : exponents .t135 = ![0, 10, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t136) (exponents .t134) (c .t136) a = (((36 * c .t136) * a 2) * a 2) := by
    have hk : exponents .t134 = ![0, 10, 7] := rfl
    have h : exponents .t136 = ![0, 10, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t137) (exponents .t134) (c .t137) a = ((((120 * c .t137) * a 2) * a 2) * a 2) := by
    have hk : exponents .t134 = ![0, 10, 7] := rfl
    have h : exponents .t137 = ![0, 10, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 7 = 120 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t134_0_10_7_interval_bound (c .t134) (c .t135) (c .t136) (c .t137) (a := a 2) h0 h1 h2 h3 ha

theorem t135_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_0_10_8.mem (c .t135))
    (h1 : ThomsonNine.ChainBinding.R1_0_10_8.mem (c .t136))
    (h2 : ThomsonNine.ChainBinding.R2_0_10_8.mem (c .t137))
    (ha : ThomsonNine.ChainBinding.A_0_10_8.mem (a 2)) :
    (coefficientInterval .t135).mem (ThomsonNine.GatheredBinding.gathered (exponents .t135) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t135 i ≤ exponents t i)) = [.t135, .t136, .t137] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t135) (exponents .t135) (c .t135) a = c .t135 := by
    have h : exponents .t135 = ![0, 10, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t136) (exponents .t135) (c .t136) a = ((9 * c .t136) * a 2) := by
    have hk : exponents .t135 = ![0, 10, 8] := rfl
    have h : exponents .t136 = ![0, 10, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t137) (exponents .t135) (c .t137) a = (((45 * c .t137) * a 2) * a 2) := by
    have hk : exponents .t135 = ![0, 10, 8] := rfl
    have h : exponents .t137 = ![0, 10, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 8 = 45 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t135_0_10_8_interval_bound (c .t135) (c .t136) (c .t137) (a := a 2) h0 h1 h2 ha

theorem t151_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_0_24_0.mem (c .t151))
    (h1 : ThomsonNine.ChainBinding.R1_0_24_0.mem (c .t152))
    (h2 : ThomsonNine.ChainBinding.R2_0_24_0.mem (c .t153))
    (h3 : ThomsonNine.ChainBinding.R3_0_24_0.mem (c .t154))
    (ha : ThomsonNine.ChainBinding.A_0_24_0.mem (a 1)) :
    (coefficientInterval .t151).mem (ThomsonNine.GatheredBinding.gathered (exponents .t151) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t151 i ≤ exponents t i)) = [.t151, .t152, .t153, .t154] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t151) (exponents .t151) (c .t151) a = c .t151 := by
    have h : exponents .t151 = ![0, 24, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t152) (exponents .t151) (c .t152) a = ((25 * c .t152) * a 1) := by
    have hk : exponents .t151 = ![0, 24, 0] := rfl
    have h : exponents .t152 = ![0, 25, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t153) (exponents .t151) (c .t153) a = (((325 * c .t153) * a 1) * a 1) := by
    have hk : exponents .t151 = ![0, 24, 0] := rfl
    have h : exponents .t153 = ![0, 26, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 26 24 = 325 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t154) (exponents .t151) (c .t154) a = ((((2925 * c .t154) * a 1) * a 1) * a 1) := by
    have hk : exponents .t151 = ![0, 24, 0] := rfl
    have h : exponents .t154 = ![0, 27, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 27 24 = 2925 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t151_0_24_0_interval_bound (c .t151) (c .t152) (c .t153) (c .t154) (a := a 1) h0 h1 h2 h3 ha

theorem t152_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_0_25_0.mem (c .t152))
    (h1 : ThomsonNine.ChainBinding.R1_0_25_0.mem (c .t153))
    (h2 : ThomsonNine.ChainBinding.R2_0_25_0.mem (c .t154))
    (ha : ThomsonNine.ChainBinding.A_0_25_0.mem (a 1)) :
    (coefficientInterval .t152).mem (ThomsonNine.GatheredBinding.gathered (exponents .t152) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t152 i ≤ exponents t i)) = [.t152, .t153, .t154] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t152) (exponents .t152) (c .t152) a = c .t152 := by
    have h : exponents .t152 = ![0, 25, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t153) (exponents .t152) (c .t153) a = ((26 * c .t153) * a 1) := by
    have hk : exponents .t152 = ![0, 25, 0] := rfl
    have h : exponents .t153 = ![0, 26, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t154) (exponents .t152) (c .t154) a = (((351 * c .t154) * a 1) * a 1) := by
    have hk : exponents .t152 = ![0, 25, 0] := rfl
    have h : exponents .t154 = ![0, 27, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 27 25 = 351 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t152_0_25_0_interval_bound (c .t152) (c .t153) (c .t154) (a := a 1) h0 h1 h2 ha

theorem t225_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_1_6_9.mem (c .t225))
    (h1 : ThomsonNine.ChainBinding.R1_1_6_9.mem (c .t235))
    (h2 : ThomsonNine.ChainBinding.R2_1_6_9.mem (c .t245))
    (h3 : ThomsonNine.ChainBinding.R3_1_6_9.mem (c .t255))
    (ha : ThomsonNine.ChainBinding.A_1_6_9.mem (a 1)) :
    (coefficientInterval .t225).mem (ThomsonNine.GatheredBinding.gathered (exponents .t225) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t225 i ≤ exponents t i)) = [.t225, .t235, .t245, .t255] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t225) (exponents .t225) (c .t225) a = c .t225 := by
    have h : exponents .t225 = ![1, 6, 9] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t235) (exponents .t225) (c .t235) a = ((7 * c .t235) * a 1) := by
    have hk : exponents .t225 = ![1, 6, 9] := rfl
    have h : exponents .t235 = ![1, 7, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t245) (exponents .t225) (c .t245) a = (((28 * c .t245) * a 1) * a 1) := by
    have hk : exponents .t225 = ![1, 6, 9] := rfl
    have h : exponents .t245 = ![1, 8, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t255) (exponents .t225) (c .t255) a = ((((84 * c .t255) * a 1) * a 1) * a 1) := by
    have hk : exponents .t225 = ![1, 6, 9] := rfl
    have h : exponents .t255 = ![1, 9, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 6 = 84 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t225_1_6_9_interval_bound (c .t225) (c .t235) (c .t245) (c .t255) (a := a 1) h0 h1 h2 h3 ha

theorem t235_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_1_7_9.mem (c .t235))
    (h1 : ThomsonNine.ChainBinding.R1_1_7_9.mem (c .t245))
    (h2 : ThomsonNine.ChainBinding.R2_1_7_9.mem (c .t255))
    (ha : ThomsonNine.ChainBinding.A_1_7_9.mem (a 1)) :
    (coefficientInterval .t235).mem (ThomsonNine.GatheredBinding.gathered (exponents .t235) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t235 i ≤ exponents t i)) = [.t235, .t245, .t255] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t235) (exponents .t235) (c .t235) a = c .t235 := by
    have h : exponents .t235 = ![1, 7, 9] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t245) (exponents .t235) (c .t245) a = ((8 * c .t245) * a 1) := by
    have hk : exponents .t235 = ![1, 7, 9] := rfl
    have h : exponents .t245 = ![1, 8, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t255) (exponents .t235) (c .t255) a = (((36 * c .t255) * a 1) * a 1) := by
    have hk : exponents .t235 = ![1, 7, 9] := rfl
    have h : exponents .t255 = ![1, 9, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t235_1_7_9_interval_bound (c .t235) (c .t245) (c .t255) (a := a 1) h0 h1 h2 ha

theorem t252_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_1_9_6.mem (c .t252))
    (h1 : ThomsonNine.ChainBinding.R1_1_9_6.mem (c .t253))
    (h2 : ThomsonNine.ChainBinding.R2_1_9_6.mem (c .t254))
    (h3 : ThomsonNine.ChainBinding.R3_1_9_6.mem (c .t255))
    (ha : ThomsonNine.ChainBinding.A_1_9_6.mem (a 2)) :
    (coefficientInterval .t252).mem (ThomsonNine.GatheredBinding.gathered (exponents .t252) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t252 i ≤ exponents t i)) = [.t252, .t253, .t254, .t255] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t252) (exponents .t252) (c .t252) a = c .t252 := by
    have h : exponents .t252 = ![1, 9, 6] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t253) (exponents .t252) (c .t253) a = ((7 * c .t253) * a 2) := by
    have hk : exponents .t252 = ![1, 9, 6] := rfl
    have h : exponents .t253 = ![1, 9, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t254) (exponents .t252) (c .t254) a = (((28 * c .t254) * a 2) * a 2) := by
    have hk : exponents .t252 = ![1, 9, 6] := rfl
    have h : exponents .t254 = ![1, 9, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t255) (exponents .t252) (c .t255) a = ((((84 * c .t255) * a 2) * a 2) * a 2) := by
    have hk : exponents .t252 = ![1, 9, 6] := rfl
    have h : exponents .t255 = ![1, 9, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 6 = 84 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t252_1_9_6_interval_bound (c .t252) (c .t253) (c .t254) (c .t255) (a := a 2) h0 h1 h2 h3 ha

theorem t253_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_1_9_7.mem (c .t253))
    (h1 : ThomsonNine.ChainBinding.R1_1_9_7.mem (c .t254))
    (h2 : ThomsonNine.ChainBinding.R2_1_9_7.mem (c .t255))
    (ha : ThomsonNine.ChainBinding.A_1_9_7.mem (a 2)) :
    (coefficientInterval .t253).mem (ThomsonNine.GatheredBinding.gathered (exponents .t253) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t253 i ≤ exponents t i)) = [.t253, .t254, .t255] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t253) (exponents .t253) (c .t253) a = c .t253 := by
    have h : exponents .t253 = ![1, 9, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t254) (exponents .t253) (c .t254) a = ((8 * c .t254) * a 2) := by
    have hk : exponents .t253 = ![1, 9, 7] := rfl
    have h : exponents .t254 = ![1, 9, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t255) (exponents .t253) (c .t255) a = (((36 * c .t255) * a 2) * a 2) := by
    have hk : exponents .t253 = ![1, 9, 7] := rfl
    have h : exponents .t255 = ![1, 9, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t253_1_9_7_interval_bound (c .t253) (c .t254) (c .t255) (a := a 2) h0 h1 h2 ha

theorem t313_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_2_5_8.mem (c .t313))
    (h1 : ThomsonNine.ChainBinding.R1_2_5_8.mem (c .t322))
    (h2 : ThomsonNine.ChainBinding.R2_2_5_8.mem (c .t331))
    (h3 : ThomsonNine.ChainBinding.R3_2_5_8.mem (c .t340))
    (ha : ThomsonNine.ChainBinding.A_2_5_8.mem (a 1)) :
    (coefficientInterval .t313).mem (ThomsonNine.GatheredBinding.gathered (exponents .t313) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t313 i ≤ exponents t i)) = [.t313, .t322, .t331, .t340] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t313) (exponents .t313) (c .t313) a = c .t313 := by
    have h : exponents .t313 = ![2, 5, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t322) (exponents .t313) (c .t322) a = ((6 * c .t322) * a 1) := by
    have hk : exponents .t313 = ![2, 5, 8] := rfl
    have h : exponents .t322 = ![2, 6, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t331) (exponents .t313) (c .t331) a = (((21 * c .t331) * a 1) * a 1) := by
    have hk : exponents .t313 = ![2, 5, 8] := rfl
    have h : exponents .t331 = ![2, 7, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t340) (exponents .t313) (c .t340) a = ((((56 * c .t340) * a 1) * a 1) * a 1) := by
    have hk : exponents .t313 = ![2, 5, 8] := rfl
    have h : exponents .t340 = ![2, 8, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 5 = 56 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t313_2_5_8_interval_bound (c .t313) (c .t322) (c .t331) (c .t340) (a := a 1) h0 h1 h2 h3 ha

theorem t322_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_2_6_8.mem (c .t322))
    (h1 : ThomsonNine.ChainBinding.R1_2_6_8.mem (c .t331))
    (h2 : ThomsonNine.ChainBinding.R2_2_6_8.mem (c .t340))
    (ha : ThomsonNine.ChainBinding.A_2_6_8.mem (a 1)) :
    (coefficientInterval .t322).mem (ThomsonNine.GatheredBinding.gathered (exponents .t322) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t322 i ≤ exponents t i)) = [.t322, .t331, .t340] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t322) (exponents .t322) (c .t322) a = c .t322 := by
    have h : exponents .t322 = ![2, 6, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t331) (exponents .t322) (c .t331) a = ((7 * c .t331) * a 1) := by
    have hk : exponents .t322 = ![2, 6, 8] := rfl
    have h : exponents .t331 = ![2, 7, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t340) (exponents .t322) (c .t340) a = (((28 * c .t340) * a 1) * a 1) := by
    have hk : exponents .t322 = ![2, 6, 8] := rfl
    have h : exponents .t340 = ![2, 8, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t322_2_6_8_interval_bound (c .t322) (c .t331) (c .t340) (a := a 1) h0 h1 h2 ha

theorem t337_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_2_8_5.mem (c .t337))
    (h1 : ThomsonNine.ChainBinding.R1_2_8_5.mem (c .t338))
    (h2 : ThomsonNine.ChainBinding.R2_2_8_5.mem (c .t339))
    (h3 : ThomsonNine.ChainBinding.R3_2_8_5.mem (c .t340))
    (ha : ThomsonNine.ChainBinding.A_2_8_5.mem (a 2)) :
    (coefficientInterval .t337).mem (ThomsonNine.GatheredBinding.gathered (exponents .t337) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t337 i ≤ exponents t i)) = [.t337, .t338, .t339, .t340] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t337) (exponents .t337) (c .t337) a = c .t337 := by
    have h : exponents .t337 = ![2, 8, 5] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t338) (exponents .t337) (c .t338) a = ((6 * c .t338) * a 2) := by
    have hk : exponents .t337 = ![2, 8, 5] := rfl
    have h : exponents .t338 = ![2, 8, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t339) (exponents .t337) (c .t339) a = (((21 * c .t339) * a 2) * a 2) := by
    have hk : exponents .t337 = ![2, 8, 5] := rfl
    have h : exponents .t339 = ![2, 8, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t340) (exponents .t337) (c .t340) a = ((((56 * c .t340) * a 2) * a 2) * a 2) := by
    have hk : exponents .t337 = ![2, 8, 5] := rfl
    have h : exponents .t340 = ![2, 8, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 5 = 56 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t337_2_8_5_interval_bound (c .t337) (c .t338) (c .t339) (c .t340) (a := a 2) h0 h1 h2 h3 ha

theorem t338_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_2_8_6.mem (c .t338))
    (h1 : ThomsonNine.ChainBinding.R1_2_8_6.mem (c .t339))
    (h2 : ThomsonNine.ChainBinding.R2_2_8_6.mem (c .t340))
    (ha : ThomsonNine.ChainBinding.A_2_8_6.mem (a 2)) :
    (coefficientInterval .t338).mem (ThomsonNine.GatheredBinding.gathered (exponents .t338) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t338 i ≤ exponents t i)) = [.t338, .t339, .t340] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t338) (exponents .t338) (c .t338) a = c .t338 := by
    have h : exponents .t338 = ![2, 8, 6] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t339) (exponents .t338) (c .t339) a = ((7 * c .t339) * a 2) := by
    have hk : exponents .t338 = ![2, 8, 6] := rfl
    have h : exponents .t339 = ![2, 8, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t340) (exponents .t338) (c .t340) a = (((28 * c .t340) * a 2) * a 2) := by
    have hk : exponents .t338 = ![2, 8, 6] := rfl
    have h : exponents .t340 = ![2, 8, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t338_2_8_6_interval_bound (c .t338) (c .t339) (c .t340) (a := a 2) h0 h1 h2 ha

theorem t389_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_3_4_7.mem (c .t389))
    (h1 : ThomsonNine.ChainBinding.R1_3_4_7.mem (c .t397))
    (h2 : ThomsonNine.ChainBinding.R2_3_4_7.mem (c .t405))
    (h3 : ThomsonNine.ChainBinding.R3_3_4_7.mem (c .t413))
    (ha : ThomsonNine.ChainBinding.A_3_4_7.mem (a 1)) :
    (coefficientInterval .t389).mem (ThomsonNine.GatheredBinding.gathered (exponents .t389) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t389 i ≤ exponents t i)) = [.t389, .t397, .t405, .t413] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t389) (exponents .t389) (c .t389) a = c .t389 := by
    have h : exponents .t389 = ![3, 4, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t397) (exponents .t389) (c .t397) a = ((5 * c .t397) * a 1) := by
    have hk : exponents .t389 = ![3, 4, 7] := rfl
    have h : exponents .t397 = ![3, 5, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t405) (exponents .t389) (c .t405) a = (((15 * c .t405) * a 1) * a 1) := by
    have hk : exponents .t389 = ![3, 4, 7] := rfl
    have h : exponents .t405 = ![3, 6, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 6 4 = 15 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t413) (exponents .t389) (c .t413) a = ((((35 * c .t413) * a 1) * a 1) * a 1) := by
    have hk : exponents .t389 = ![3, 4, 7] := rfl
    have h : exponents .t413 = ![3, 7, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 4 = 35 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t389_3_4_7_interval_bound (c .t389) (c .t397) (c .t405) (c .t413) (a := a 1) h0 h1 h2 h3 ha

theorem t397_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_3_5_7.mem (c .t397))
    (h1 : ThomsonNine.ChainBinding.R1_3_5_7.mem (c .t405))
    (h2 : ThomsonNine.ChainBinding.R2_3_5_7.mem (c .t413))
    (ha : ThomsonNine.ChainBinding.A_3_5_7.mem (a 1)) :
    (coefficientInterval .t397).mem (ThomsonNine.GatheredBinding.gathered (exponents .t397) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t397 i ≤ exponents t i)) = [.t397, .t405, .t413] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t397) (exponents .t397) (c .t397) a = c .t397 := by
    have h : exponents .t397 = ![3, 5, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t405) (exponents .t397) (c .t405) a = ((6 * c .t405) * a 1) := by
    have hk : exponents .t397 = ![3, 5, 7] := rfl
    have h : exponents .t405 = ![3, 6, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t413) (exponents .t397) (c .t413) a = (((21 * c .t413) * a 1) * a 1) := by
    have hk : exponents .t397 = ![3, 5, 7] := rfl
    have h : exponents .t413 = ![3, 7, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t397_3_5_7_interval_bound (c .t397) (c .t405) (c .t413) (a := a 1) h0 h1 h2 ha

theorem t410_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_3_7_4.mem (c .t410))
    (h1 : ThomsonNine.ChainBinding.R1_3_7_4.mem (c .t411))
    (h2 : ThomsonNine.ChainBinding.R2_3_7_4.mem (c .t412))
    (h3 : ThomsonNine.ChainBinding.R3_3_7_4.mem (c .t413))
    (ha : ThomsonNine.ChainBinding.A_3_7_4.mem (a 2)) :
    (coefficientInterval .t410).mem (ThomsonNine.GatheredBinding.gathered (exponents .t410) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t410 i ≤ exponents t i)) = [.t410, .t411, .t412, .t413] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t410) (exponents .t410) (c .t410) a = c .t410 := by
    have h : exponents .t410 = ![3, 7, 4] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t411) (exponents .t410) (c .t411) a = ((5 * c .t411) * a 2) := by
    have hk : exponents .t410 = ![3, 7, 4] := rfl
    have h : exponents .t411 = ![3, 7, 5] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t412) (exponents .t410) (c .t412) a = (((15 * c .t412) * a 2) * a 2) := by
    have hk : exponents .t410 = ![3, 7, 4] := rfl
    have h : exponents .t412 = ![3, 7, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 6 4 = 15 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t413) (exponents .t410) (c .t413) a = ((((35 * c .t413) * a 2) * a 2) * a 2) := by
    have hk : exponents .t410 = ![3, 7, 4] := rfl
    have h : exponents .t413 = ![3, 7, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 4 = 35 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t410_3_7_4_interval_bound (c .t410) (c .t411) (c .t412) (c .t413) (a := a 2) h0 h1 h2 h3 ha

theorem t411_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_3_7_5.mem (c .t411))
    (h1 : ThomsonNine.ChainBinding.R1_3_7_5.mem (c .t412))
    (h2 : ThomsonNine.ChainBinding.R2_3_7_5.mem (c .t413))
    (ha : ThomsonNine.ChainBinding.A_3_7_5.mem (a 2)) :
    (coefficientInterval .t411).mem (ThomsonNine.GatheredBinding.gathered (exponents .t411) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t411 i ≤ exponents t i)) = [.t411, .t412, .t413] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t411) (exponents .t411) (c .t411) a = c .t411 := by
    have h : exponents .t411 = ![3, 7, 5] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t412) (exponents .t411) (c .t412) a = ((6 * c .t412) * a 2) := by
    have hk : exponents .t411 = ![3, 7, 5] := rfl
    have h : exponents .t412 = ![3, 7, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t413) (exponents .t411) (c .t413) a = (((21 * c .t413) * a 2) * a 2) := by
    have hk : exponents .t411 = ![3, 7, 5] := rfl
    have h : exponents .t413 = ![3, 7, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t411_3_7_5_interval_bound (c .t411) (c .t412) (c .t413) (a := a 2) h0 h1 h2 ha

theorem t457_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_4_3_7.mem (c .t457))
    (h1 : ThomsonNine.ChainBinding.R1_4_3_7.mem (c .t526))
    (h2 : ThomsonNine.ChainBinding.R2_4_3_7.mem (c .t592))
    (h3 : ThomsonNine.ChainBinding.R3_4_3_7.mem (c .t657))
    (ha : ThomsonNine.ChainBinding.A_4_3_7.mem (a 0)) :
    (coefficientInterval .t457).mem (ThomsonNine.GatheredBinding.gathered (exponents .t457) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t457 i ≤ exponents t i)) = [.t457, .t526, .t592, .t657] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t457) (exponents .t457) (c .t457) a = c .t457 := by
    have h : exponents .t457 = ![4, 3, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t526) (exponents .t457) (c .t526) a = ((5 * c .t526) * a 0) := by
    have hk : exponents .t457 = ![4, 3, 7] := rfl
    have h : exponents .t526 = ![5, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t592) (exponents .t457) (c .t592) a = (((15 * c .t592) * a 0) * a 0) := by
    have hk : exponents .t457 = ![4, 3, 7] := rfl
    have h : exponents .t592 = ![6, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 6 4 = 15 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t657) (exponents .t457) (c .t657) a = ((((35 * c .t657) * a 0) * a 0) * a 0) := by
    have hk : exponents .t457 = ![4, 3, 7] := rfl
    have h : exponents .t657 = ![7, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 4 = 35 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t457_4_3_7_interval_bound (c .t457) (c .t526) (c .t592) (c .t657) (a := a 0) h0 h1 h2 h3 ha

theorem t482_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_4_7_3.mem (c .t482))
    (h1 : ThomsonNine.ChainBinding.R1_4_7_3.mem (c .t548))
    (h2 : ThomsonNine.ChainBinding.R2_4_7_3.mem (c .t613))
    (h3 : ThomsonNine.ChainBinding.R3_4_7_3.mem (c .t673))
    (ha : ThomsonNine.ChainBinding.A_4_7_3.mem (a 0)) :
    (coefficientInterval .t482).mem (ThomsonNine.GatheredBinding.gathered (exponents .t482) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t482 i ≤ exponents t i)) = [.t482, .t548, .t613, .t673] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t482) (exponents .t482) (c .t482) a = c .t482 := by
    have h : exponents .t482 = ![4, 7, 3] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t548) (exponents .t482) (c .t548) a = ((5 * c .t548) * a 0) := by
    have hk : exponents .t482 = ![4, 7, 3] := rfl
    have h : exponents .t548 = ![5, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t613) (exponents .t482) (c .t613) a = (((15 * c .t613) * a 0) * a 0) := by
    have hk : exponents .t482 = ![4, 7, 3] := rfl
    have h : exponents .t613 = ![6, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 6 4 = 15 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t673) (exponents .t482) (c .t673) a = ((((35 * c .t673) * a 0) * a 0) * a 0) := by
    have hk : exponents .t482 = ![4, 7, 3] := rfl
    have h : exponents .t673 = ![7, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 4 = 35 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t482_4_7_3_interval_bound (c .t482) (c .t548) (c .t613) (c .t673) (a := a 0) h0 h1 h2 h3 ha

theorem t518_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_5_2_8.mem (c .t518))
    (h1 : ThomsonNine.ChainBinding.R1_5_2_8.mem (c .t584))
    (h2 : ThomsonNine.ChainBinding.R2_5_2_8.mem (c .t649))
    (h3 : ThomsonNine.ChainBinding.R3_5_2_8.mem (c .t709))
    (ha : ThomsonNine.ChainBinding.A_5_2_8.mem (a 0)) :
    (coefficientInterval .t518).mem (ThomsonNine.GatheredBinding.gathered (exponents .t518) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t518 i ≤ exponents t i)) = [.t518, .t584, .t649, .t709] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t518) (exponents .t518) (c .t518) a = c .t518 := by
    have h : exponents .t518 = ![5, 2, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t584) (exponents .t518) (c .t584) a = ((6 * c .t584) * a 0) := by
    have hk : exponents .t518 = ![5, 2, 8] := rfl
    have h : exponents .t584 = ![6, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t649) (exponents .t518) (c .t649) a = (((21 * c .t649) * a 0) * a 0) := by
    have hk : exponents .t518 = ![5, 2, 8] := rfl
    have h : exponents .t649 = ![7, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t709) (exponents .t518) (c .t709) a = ((((56 * c .t709) * a 0) * a 0) * a 0) := by
    have hk : exponents .t518 = ![5, 2, 8] := rfl
    have h : exponents .t709 = ![8, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 5 = 56 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t518_5_2_8_interval_bound (c .t518) (c .t584) (c .t649) (c .t709) (a := a 0) h0 h1 h2 h3 ha

theorem t526_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_5_3_7.mem (c .t526))
    (h1 : ThomsonNine.ChainBinding.R1_5_3_7.mem (c .t592))
    (h2 : ThomsonNine.ChainBinding.R2_5_3_7.mem (c .t657))
    (ha : ThomsonNine.ChainBinding.A_5_3_7.mem (a 0)) :
    (coefficientInterval .t526).mem (ThomsonNine.GatheredBinding.gathered (exponents .t526) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t526 i ≤ exponents t i)) = [.t526, .t592, .t657] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t526) (exponents .t526) (c .t526) a = c .t526 := by
    have h : exponents .t526 = ![5, 3, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t592) (exponents .t526) (c .t592) a = ((6 * c .t592) * a 0) := by
    have hk : exponents .t526 = ![5, 3, 7] := rfl
    have h : exponents .t592 = ![6, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t657) (exponents .t526) (c .t657) a = (((21 * c .t657) * a 0) * a 0) := by
    have hk : exponents .t526 = ![5, 3, 7] := rfl
    have h : exponents .t657 = ![7, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t526_5_3_7_interval_bound (c .t526) (c .t592) (c .t657) (a := a 0) h0 h1 h2 ha

theorem t548_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_5_7_3.mem (c .t548))
    (h1 : ThomsonNine.ChainBinding.R1_5_7_3.mem (c .t613))
    (h2 : ThomsonNine.ChainBinding.R2_5_7_3.mem (c .t673))
    (ha : ThomsonNine.ChainBinding.A_5_7_3.mem (a 0)) :
    (coefficientInterval .t548).mem (ThomsonNine.GatheredBinding.gathered (exponents .t548) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t548 i ≤ exponents t i)) = [.t548, .t613, .t673] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t548) (exponents .t548) (c .t548) a = c .t548 := by
    have h : exponents .t548 = ![5, 7, 3] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t613) (exponents .t548) (c .t613) a = ((6 * c .t613) * a 0) := by
    have hk : exponents .t548 = ![5, 7, 3] := rfl
    have h : exponents .t613 = ![6, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t673) (exponents .t548) (c .t673) a = (((21 * c .t673) * a 0) * a 0) := by
    have hk : exponents .t548 = ![5, 7, 3] := rfl
    have h : exponents .t673 = ![7, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t548_5_7_3_interval_bound (c .t548) (c .t613) (c .t673) (a := a 0) h0 h1 h2 ha

theorem t551_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_5_8_2.mem (c .t551))
    (h1 : ThomsonNine.ChainBinding.R1_5_8_2.mem (c .t616))
    (h2 : ThomsonNine.ChainBinding.R2_5_8_2.mem (c .t676))
    (h3 : ThomsonNine.ChainBinding.R3_5_8_2.mem (c .t727))
    (ha : ThomsonNine.ChainBinding.A_5_8_2.mem (a 0)) :
    (coefficientInterval .t551).mem (ThomsonNine.GatheredBinding.gathered (exponents .t551) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t551 i ≤ exponents t i)) = [.t551, .t616, .t676, .t727] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t551) (exponents .t551) (c .t551) a = c .t551 := by
    have h : exponents .t551 = ![5, 8, 2] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t616) (exponents .t551) (c .t616) a = ((6 * c .t616) * a 0) := by
    have hk : exponents .t551 = ![5, 8, 2] := rfl
    have h : exponents .t616 = ![6, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t676) (exponents .t551) (c .t676) a = (((21 * c .t676) * a 0) * a 0) := by
    have hk : exponents .t551 = ![5, 8, 2] := rfl
    have h : exponents .t676 = ![7, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t727) (exponents .t551) (c .t727) a = ((((56 * c .t727) * a 0) * a 0) * a 0) := by
    have hk : exponents .t551 = ![5, 8, 2] := rfl
    have h : exponents .t727 = ![8, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 5 = 56 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t551_5_8_2_interval_bound (c .t551) (c .t616) (c .t676) (c .t727) (a := a 0) h0 h1 h2 h3 ha

theorem t575_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_6_1_9.mem (c .t575))
    (h1 : ThomsonNine.ChainBinding.R1_6_1_9.mem (c .t640))
    (h2 : ThomsonNine.ChainBinding.R2_6_1_9.mem (c .t700))
    (h3 : ThomsonNine.ChainBinding.R3_6_1_9.mem (c .t751))
    (ha : ThomsonNine.ChainBinding.A_6_1_9.mem (a 0)) :
    (coefficientInterval .t575).mem (ThomsonNine.GatheredBinding.gathered (exponents .t575) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t575 i ≤ exponents t i)) = [.t575, .t640, .t700, .t751] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t575) (exponents .t575) (c .t575) a = c .t575 := by
    have h : exponents .t575 = ![6, 1, 9] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t640) (exponents .t575) (c .t640) a = ((7 * c .t640) * a 0) := by
    have hk : exponents .t575 = ![6, 1, 9] := rfl
    have h : exponents .t640 = ![7, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t700) (exponents .t575) (c .t700) a = (((28 * c .t700) * a 0) * a 0) := by
    have hk : exponents .t575 = ![6, 1, 9] := rfl
    have h : exponents .t700 = ![8, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t751) (exponents .t575) (c .t751) a = ((((84 * c .t751) * a 0) * a 0) * a 0) := by
    have hk : exponents .t575 = ![6, 1, 9] := rfl
    have h : exponents .t751 = ![9, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 6 = 84 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t575_6_1_9_interval_bound (c .t575) (c .t640) (c .t700) (c .t751) (a := a 0) h0 h1 h2 h3 ha

theorem t584_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_6_2_8.mem (c .t584))
    (h1 : ThomsonNine.ChainBinding.R1_6_2_8.mem (c .t649))
    (h2 : ThomsonNine.ChainBinding.R2_6_2_8.mem (c .t709))
    (ha : ThomsonNine.ChainBinding.A_6_2_8.mem (a 0)) :
    (coefficientInterval .t584).mem (ThomsonNine.GatheredBinding.gathered (exponents .t584) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t584 i ≤ exponents t i)) = [.t584, .t649, .t709] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t584) (exponents .t584) (c .t584) a = c .t584 := by
    have h : exponents .t584 = ![6, 2, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t649) (exponents .t584) (c .t649) a = ((7 * c .t649) * a 0) := by
    have hk : exponents .t584 = ![6, 2, 8] := rfl
    have h : exponents .t649 = ![7, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t709) (exponents .t584) (c .t709) a = (((28 * c .t709) * a 0) * a 0) := by
    have hk : exponents .t584 = ![6, 2, 8] := rfl
    have h : exponents .t709 = ![8, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t584_6_2_8_interval_bound (c .t584) (c .t649) (c .t709) (a := a 0) h0 h1 h2 ha

theorem t616_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_6_8_2.mem (c .t616))
    (h1 : ThomsonNine.ChainBinding.R1_6_8_2.mem (c .t676))
    (h2 : ThomsonNine.ChainBinding.R2_6_8_2.mem (c .t727))
    (ha : ThomsonNine.ChainBinding.A_6_8_2.mem (a 0)) :
    (coefficientInterval .t616).mem (ThomsonNine.GatheredBinding.gathered (exponents .t616) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t616 i ≤ exponents t i)) = [.t616, .t676, .t727] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t616) (exponents .t616) (c .t616) a = c .t616 := by
    have h : exponents .t616 = ![6, 8, 2] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t676) (exponents .t616) (c .t676) a = ((7 * c .t676) * a 0) := by
    have hk : exponents .t616 = ![6, 8, 2] := rfl
    have h : exponents .t676 = ![7, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t727) (exponents .t616) (c .t727) a = (((28 * c .t727) * a 0) * a 0) := by
    have hk : exponents .t616 = ![6, 8, 2] := rfl
    have h : exponents .t727 = ![8, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t616_6_8_2_interval_bound (c .t616) (c .t676) (c .t727) (a := a 0) h0 h1 h2 ha

theorem t618_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_6_9_1.mem (c .t618))
    (h1 : ThomsonNine.ChainBinding.R1_6_9_1.mem (c .t678))
    (h2 : ThomsonNine.ChainBinding.R2_6_9_1.mem (c .t729))
    (h3 : ThomsonNine.ChainBinding.R3_6_9_1.mem (c .t767))
    (ha : ThomsonNine.ChainBinding.A_6_9_1.mem (a 0)) :
    (coefficientInterval .t618).mem (ThomsonNine.GatheredBinding.gathered (exponents .t618) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t618 i ≤ exponents t i)) = [.t618, .t678, .t729, .t767] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t618) (exponents .t618) (c .t618) a = c .t618 := by
    have h : exponents .t618 = ![6, 9, 1] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t678) (exponents .t618) (c .t678) a = ((7 * c .t678) * a 0) := by
    have hk : exponents .t618 = ![6, 9, 1] := rfl
    have h : exponents .t678 = ![7, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t729) (exponents .t618) (c .t729) a = (((28 * c .t729) * a 0) * a 0) := by
    have hk : exponents .t618 = ![6, 9, 1] := rfl
    have h : exponents .t729 = ![8, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t767) (exponents .t618) (c .t767) a = ((((84 * c .t767) * a 0) * a 0) * a 0) := by
    have hk : exponents .t618 = ![6, 9, 1] := rfl
    have h : exponents .t767 = ![9, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 6 = 84 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t618_6_9_1_interval_bound (c .t618) (c .t678) (c .t729) (c .t767) (a := a 0) h0 h1 h2 h3 ha

theorem t630_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_7_0_10.mem (c .t630))
    (h1 : ThomsonNine.ChainBinding.R1_7_0_10.mem (c .t690))
    (h2 : ThomsonNine.ChainBinding.R2_7_0_10.mem (c .t741))
    (h3 : ThomsonNine.ChainBinding.R3_7_0_10.mem (c .t779))
    (ha : ThomsonNine.ChainBinding.A_7_0_10.mem (a 0)) :
    (coefficientInterval .t630).mem (ThomsonNine.GatheredBinding.gathered (exponents .t630) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t630 i ≤ exponents t i)) = [.t630, .t690, .t741, .t779] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t630) (exponents .t630) (c .t630) a = c .t630 := by
    have h : exponents .t630 = ![7, 0, 10] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t690) (exponents .t630) (c .t690) a = ((8 * c .t690) * a 0) := by
    have hk : exponents .t630 = ![7, 0, 10] := rfl
    have h : exponents .t690 = ![8, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t741) (exponents .t630) (c .t741) a = (((36 * c .t741) * a 0) * a 0) := by
    have hk : exponents .t630 = ![7, 0, 10] := rfl
    have h : exponents .t741 = ![9, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t779) (exponents .t630) (c .t779) a = ((((120 * c .t779) * a 0) * a 0) * a 0) := by
    have hk : exponents .t630 = ![7, 0, 10] := rfl
    have h : exponents .t779 = ![10, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 7 = 120 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t630_7_0_10_interval_bound (c .t630) (c .t690) (c .t741) (c .t779) (a := a 0) h0 h1 h2 h3 ha

theorem t640_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_7_1_9.mem (c .t640))
    (h1 : ThomsonNine.ChainBinding.R1_7_1_9.mem (c .t700))
    (h2 : ThomsonNine.ChainBinding.R2_7_1_9.mem (c .t751))
    (ha : ThomsonNine.ChainBinding.A_7_1_9.mem (a 0)) :
    (coefficientInterval .t640).mem (ThomsonNine.GatheredBinding.gathered (exponents .t640) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t640 i ≤ exponents t i)) = [.t640, .t700, .t751] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t640) (exponents .t640) (c .t640) a = c .t640 := by
    have h : exponents .t640 = ![7, 1, 9] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t700) (exponents .t640) (c .t700) a = ((8 * c .t700) * a 0) := by
    have hk : exponents .t640 = ![7, 1, 9] := rfl
    have h : exponents .t700 = ![8, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t751) (exponents .t640) (c .t751) a = (((36 * c .t751) * a 0) * a 0) := by
    have hk : exponents .t640 = ![7, 1, 9] := rfl
    have h : exponents .t751 = ![9, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t640_7_1_9_interval_bound (c .t640) (c .t700) (c .t751) (a := a 0) h0 h1 h2 ha

theorem t654_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_7_3_4.mem (c .t654))
    (h1 : ThomsonNine.ChainBinding.R1_7_3_4.mem (c .t655))
    (h2 : ThomsonNine.ChainBinding.R2_7_3_4.mem (c .t656))
    (h3 : ThomsonNine.ChainBinding.R3_7_3_4.mem (c .t657))
    (ha : ThomsonNine.ChainBinding.A_7_3_4.mem (a 2)) :
    (coefficientInterval .t654).mem (ThomsonNine.GatheredBinding.gathered (exponents .t654) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t654 i ≤ exponents t i)) = [.t654, .t655, .t656, .t657] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t654) (exponents .t654) (c .t654) a = c .t654 := by
    have h : exponents .t654 = ![7, 3, 4] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t655) (exponents .t654) (c .t655) a = ((5 * c .t655) * a 2) := by
    have hk : exponents .t654 = ![7, 3, 4] := rfl
    have h : exponents .t655 = ![7, 3, 5] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t656) (exponents .t654) (c .t656) a = (((15 * c .t656) * a 2) * a 2) := by
    have hk : exponents .t654 = ![7, 3, 4] := rfl
    have h : exponents .t656 = ![7, 3, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 6 4 = 15 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t657) (exponents .t654) (c .t657) a = ((((35 * c .t657) * a 2) * a 2) * a 2) := by
    have hk : exponents .t654 = ![7, 3, 4] := rfl
    have h : exponents .t657 = ![7, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 4 = 35 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t654_7_3_4_interval_bound (c .t654) (c .t655) (c .t656) (c .t657) (a := a 2) h0 h1 h2 h3 ha

theorem t655_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_7_3_5.mem (c .t655))
    (h1 : ThomsonNine.ChainBinding.R1_7_3_5.mem (c .t656))
    (h2 : ThomsonNine.ChainBinding.R2_7_3_5.mem (c .t657))
    (ha : ThomsonNine.ChainBinding.A_7_3_5.mem (a 2)) :
    (coefficientInterval .t655).mem (ThomsonNine.GatheredBinding.gathered (exponents .t655) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t655 i ≤ exponents t i)) = [.t655, .t656, .t657] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t655) (exponents .t655) (c .t655) a = c .t655 := by
    have h : exponents .t655 = ![7, 3, 5] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t656) (exponents .t655) (c .t656) a = ((6 * c .t656) * a 2) := by
    have hk : exponents .t655 = ![7, 3, 5] := rfl
    have h : exponents .t656 = ![7, 3, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t657) (exponents .t655) (c .t657) a = (((21 * c .t657) * a 2) * a 2) := by
    have hk : exponents .t655 = ![7, 3, 5] := rfl
    have h : exponents .t657 = ![7, 3, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t655_7_3_5_interval_bound (c .t655) (c .t656) (c .t657) (a := a 2) h0 h1 h2 ha

theorem t661_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_7_4_3.mem (c .t661))
    (h1 : ThomsonNine.ChainBinding.R1_7_4_3.mem (c .t665))
    (h2 : ThomsonNine.ChainBinding.R2_7_4_3.mem (c .t669))
    (h3 : ThomsonNine.ChainBinding.R3_7_4_3.mem (c .t673))
    (ha : ThomsonNine.ChainBinding.A_7_4_3.mem (a 1)) :
    (coefficientInterval .t661).mem (ThomsonNine.GatheredBinding.gathered (exponents .t661) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t661 i ≤ exponents t i)) = [.t661, .t665, .t669, .t673] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t661) (exponents .t661) (c .t661) a = c .t661 := by
    have h : exponents .t661 = ![7, 4, 3] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t665) (exponents .t661) (c .t665) a = ((5 * c .t665) * a 1) := by
    have hk : exponents .t661 = ![7, 4, 3] := rfl
    have h : exponents .t665 = ![7, 5, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t669) (exponents .t661) (c .t669) a = (((15 * c .t669) * a 1) * a 1) := by
    have hk : exponents .t661 = ![7, 4, 3] := rfl
    have h : exponents .t669 = ![7, 6, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 6 4 = 15 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t673) (exponents .t661) (c .t673) a = ((((35 * c .t673) * a 1) * a 1) * a 1) := by
    have hk : exponents .t661 = ![7, 4, 3] := rfl
    have h : exponents .t673 = ![7, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 4 = 35 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t661_7_4_3_interval_bound (c .t661) (c .t665) (c .t669) (c .t673) (a := a 1) h0 h1 h2 h3 ha

theorem t665_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_7_5_3.mem (c .t665))
    (h1 : ThomsonNine.ChainBinding.R1_7_5_3.mem (c .t669))
    (h2 : ThomsonNine.ChainBinding.R2_7_5_3.mem (c .t673))
    (ha : ThomsonNine.ChainBinding.A_7_5_3.mem (a 1)) :
    (coefficientInterval .t665).mem (ThomsonNine.GatheredBinding.gathered (exponents .t665) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t665 i ≤ exponents t i)) = [.t665, .t669, .t673] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t665) (exponents .t665) (c .t665) a = c .t665 := by
    have h : exponents .t665 = ![7, 5, 3] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t669) (exponents .t665) (c .t669) a = ((6 * c .t669) * a 1) := by
    have hk : exponents .t665 = ![7, 5, 3] := rfl
    have h : exponents .t669 = ![7, 6, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t673) (exponents .t665) (c .t673) a = (((21 * c .t673) * a 1) * a 1) := by
    have hk : exponents .t665 = ![7, 5, 3] := rfl
    have h : exponents .t673 = ![7, 7, 3] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t665_7_5_3_interval_bound (c .t665) (c .t669) (c .t673) (a := a 1) h0 h1 h2 ha

theorem t678_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_7_9_1.mem (c .t678))
    (h1 : ThomsonNine.ChainBinding.R1_7_9_1.mem (c .t729))
    (h2 : ThomsonNine.ChainBinding.R2_7_9_1.mem (c .t767))
    (ha : ThomsonNine.ChainBinding.A_7_9_1.mem (a 0)) :
    (coefficientInterval .t678).mem (ThomsonNine.GatheredBinding.gathered (exponents .t678) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t678 i ≤ exponents t i)) = [.t678, .t729, .t767] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t678) (exponents .t678) (c .t678) a = c .t678 := by
    have h : exponents .t678 = ![7, 9, 1] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t729) (exponents .t678) (c .t729) a = ((8 * c .t729) * a 0) := by
    have hk : exponents .t678 = ![7, 9, 1] := rfl
    have h : exponents .t729 = ![8, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t767) (exponents .t678) (c .t767) a = (((36 * c .t767) * a 0) * a 0) := by
    have hk : exponents .t678 = ![7, 9, 1] := rfl
    have h : exponents .t767 = ![9, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t678_7_9_1_interval_bound (c .t678) (c .t729) (c .t767) (a := a 0) h0 h1 h2 ha

theorem t679_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_7_10_0.mem (c .t679))
    (h1 : ThomsonNine.ChainBinding.R1_7_10_0.mem (c .t730))
    (h2 : ThomsonNine.ChainBinding.R2_7_10_0.mem (c .t768))
    (h3 : ThomsonNine.ChainBinding.R3_7_10_0.mem (c .t789))
    (ha : ThomsonNine.ChainBinding.A_7_10_0.mem (a 0)) :
    (coefficientInterval .t679).mem (ThomsonNine.GatheredBinding.gathered (exponents .t679) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t679 i ≤ exponents t i)) = [.t679, .t730, .t768, .t789] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t679) (exponents .t679) (c .t679) a = c .t679 := by
    have h : exponents .t679 = ![7, 10, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t730) (exponents .t679) (c .t730) a = ((8 * c .t730) * a 0) := by
    have hk : exponents .t679 = ![7, 10, 0] := rfl
    have h : exponents .t730 = ![8, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t768) (exponents .t679) (c .t768) a = (((36 * c .t768) * a 0) * a 0) := by
    have hk : exponents .t679 = ![7, 10, 0] := rfl
    have h : exponents .t768 = ![9, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t789) (exponents .t679) (c .t789) a = ((((120 * c .t789) * a 0) * a 0) * a 0) := by
    have hk : exponents .t679 = ![7, 10, 0] := rfl
    have h : exponents .t789 = ![10, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 7 = 120 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t679_7_10_0_interval_bound (c .t679) (c .t730) (c .t768) (c .t789) (a := a 0) h0 h1 h2 h3 ha

theorem t690_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_8_0_10.mem (c .t690))
    (h1 : ThomsonNine.ChainBinding.R1_8_0_10.mem (c .t741))
    (h2 : ThomsonNine.ChainBinding.R2_8_0_10.mem (c .t779))
    (ha : ThomsonNine.ChainBinding.A_8_0_10.mem (a 0)) :
    (coefficientInterval .t690).mem (ThomsonNine.GatheredBinding.gathered (exponents .t690) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t690 i ≤ exponents t i)) = [.t690, .t741, .t779] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t690) (exponents .t690) (c .t690) a = c .t690 := by
    have h : exponents .t690 = ![8, 0, 10] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t741) (exponents .t690) (c .t741) a = ((9 * c .t741) * a 0) := by
    have hk : exponents .t690 = ![8, 0, 10] := rfl
    have h : exponents .t741 = ![9, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t779) (exponents .t690) (c .t779) a = (((45 * c .t779) * a 0) * a 0) := by
    have hk : exponents .t690 = ![8, 0, 10] := rfl
    have h : exponents .t779 = ![10, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 8 = 45 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t690_8_0_10_interval_bound (c .t690) (c .t741) (c .t779) (a := a 0) h0 h1 h2 ha

theorem t706_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_8_2_5.mem (c .t706))
    (h1 : ThomsonNine.ChainBinding.R1_8_2_5.mem (c .t707))
    (h2 : ThomsonNine.ChainBinding.R2_8_2_5.mem (c .t708))
    (h3 : ThomsonNine.ChainBinding.R3_8_2_5.mem (c .t709))
    (ha : ThomsonNine.ChainBinding.A_8_2_5.mem (a 2)) :
    (coefficientInterval .t706).mem (ThomsonNine.GatheredBinding.gathered (exponents .t706) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t706 i ≤ exponents t i)) = [.t706, .t707, .t708, .t709] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t706) (exponents .t706) (c .t706) a = c .t706 := by
    have h : exponents .t706 = ![8, 2, 5] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t707) (exponents .t706) (c .t707) a = ((6 * c .t707) * a 2) := by
    have hk : exponents .t706 = ![8, 2, 5] := rfl
    have h : exponents .t707 = ![8, 2, 6] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t708) (exponents .t706) (c .t708) a = (((21 * c .t708) * a 2) * a 2) := by
    have hk : exponents .t706 = ![8, 2, 5] := rfl
    have h : exponents .t708 = ![8, 2, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t709) (exponents .t706) (c .t709) a = ((((56 * c .t709) * a 2) * a 2) * a 2) := by
    have hk : exponents .t706 = ![8, 2, 5] := rfl
    have h : exponents .t709 = ![8, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 5 = 56 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t706_8_2_5_interval_bound (c .t706) (c .t707) (c .t708) (c .t709) (a := a 2) h0 h1 h2 h3 ha

theorem t707_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_8_2_6.mem (c .t707))
    (h1 : ThomsonNine.ChainBinding.R1_8_2_6.mem (c .t708))
    (h2 : ThomsonNine.ChainBinding.R2_8_2_6.mem (c .t709))
    (ha : ThomsonNine.ChainBinding.A_8_2_6.mem (a 2)) :
    (coefficientInterval .t707).mem (ThomsonNine.GatheredBinding.gathered (exponents .t707) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t707 i ≤ exponents t i)) = [.t707, .t708, .t709] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t707) (exponents .t707) (c .t707) a = c .t707 := by
    have h : exponents .t707 = ![8, 2, 6] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t708) (exponents .t707) (c .t708) a = ((7 * c .t708) * a 2) := by
    have hk : exponents .t707 = ![8, 2, 6] := rfl
    have h : exponents .t708 = ![8, 2, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t709) (exponents .t707) (c .t709) a = (((28 * c .t709) * a 2) * a 2) := by
    have hk : exponents .t707 = ![8, 2, 6] := rfl
    have h : exponents .t709 = ![8, 2, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t707_8_2_6_interval_bound (c .t707) (c .t708) (c .t709) (a := a 2) h0 h1 h2 ha

theorem t718_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_8_5_2.mem (c .t718))
    (h1 : ThomsonNine.ChainBinding.R1_8_5_2.mem (c .t721))
    (h2 : ThomsonNine.ChainBinding.R2_8_5_2.mem (c .t724))
    (h3 : ThomsonNine.ChainBinding.R3_8_5_2.mem (c .t727))
    (ha : ThomsonNine.ChainBinding.A_8_5_2.mem (a 1)) :
    (coefficientInterval .t718).mem (ThomsonNine.GatheredBinding.gathered (exponents .t718) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t718 i ≤ exponents t i)) = [.t718, .t721, .t724, .t727] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t718) (exponents .t718) (c .t718) a = c .t718 := by
    have h : exponents .t718 = ![8, 5, 2] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t721) (exponents .t718) (c .t721) a = ((6 * c .t721) * a 1) := by
    have hk : exponents .t718 = ![8, 5, 2] := rfl
    have h : exponents .t721 = ![8, 6, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t724) (exponents .t718) (c .t724) a = (((21 * c .t724) * a 1) * a 1) := by
    have hk : exponents .t718 = ![8, 5, 2] := rfl
    have h : exponents .t724 = ![8, 7, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t727) (exponents .t718) (c .t727) a = ((((56 * c .t727) * a 1) * a 1) * a 1) := by
    have hk : exponents .t718 = ![8, 5, 2] := rfl
    have h : exponents .t727 = ![8, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 5 = 56 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t718_8_5_2_interval_bound (c .t718) (c .t721) (c .t724) (c .t727) (a := a 1) h0 h1 h2 h3 ha

theorem t721_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_8_6_2.mem (c .t721))
    (h1 : ThomsonNine.ChainBinding.R1_8_6_2.mem (c .t724))
    (h2 : ThomsonNine.ChainBinding.R2_8_6_2.mem (c .t727))
    (ha : ThomsonNine.ChainBinding.A_8_6_2.mem (a 1)) :
    (coefficientInterval .t721).mem (ThomsonNine.GatheredBinding.gathered (exponents .t721) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t721 i ≤ exponents t i)) = [.t721, .t724, .t727] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t721) (exponents .t721) (c .t721) a = c .t721 := by
    have h : exponents .t721 = ![8, 6, 2] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t724) (exponents .t721) (c .t724) a = ((7 * c .t724) * a 1) := by
    have hk : exponents .t721 = ![8, 6, 2] := rfl
    have h : exponents .t724 = ![8, 7, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t727) (exponents .t721) (c .t727) a = (((28 * c .t727) * a 1) * a 1) := by
    have hk : exponents .t721 = ![8, 6, 2] := rfl
    have h : exponents .t727 = ![8, 8, 2] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t721_8_6_2_interval_bound (c .t721) (c .t724) (c .t727) (a := a 1) h0 h1 h2 ha

theorem t730_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_8_10_0.mem (c .t730))
    (h1 : ThomsonNine.ChainBinding.R1_8_10_0.mem (c .t768))
    (h2 : ThomsonNine.ChainBinding.R2_8_10_0.mem (c .t789))
    (ha : ThomsonNine.ChainBinding.A_8_10_0.mem (a 0)) :
    (coefficientInterval .t730).mem (ThomsonNine.GatheredBinding.gathered (exponents .t730) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t730 i ≤ exponents t i)) = [.t730, .t768, .t789] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t730) (exponents .t730) (c .t730) a = c .t730 := by
    have h : exponents .t730 = ![8, 10, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t768) (exponents .t730) (c .t768) a = ((9 * c .t768) * a 0) := by
    have hk : exponents .t730 = ![8, 10, 0] := rfl
    have h : exponents .t768 = ![9, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t789) (exponents .t730) (c .t789) a = (((45 * c .t789) * a 0) * a 0) := by
    have hk : exponents .t730 = ![8, 10, 0] := rfl
    have h : exponents .t789 = ![10, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 8 = 45 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t730_8_10_0_interval_bound (c .t730) (c .t768) (c .t789) (a := a 0) h0 h1 h2 ha

theorem t748_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_9_1_6.mem (c .t748))
    (h1 : ThomsonNine.ChainBinding.R1_9_1_6.mem (c .t749))
    (h2 : ThomsonNine.ChainBinding.R2_9_1_6.mem (c .t750))
    (h3 : ThomsonNine.ChainBinding.R3_9_1_6.mem (c .t751))
    (ha : ThomsonNine.ChainBinding.A_9_1_6.mem (a 2)) :
    (coefficientInterval .t748).mem (ThomsonNine.GatheredBinding.gathered (exponents .t748) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t748 i ≤ exponents t i)) = [.t748, .t749, .t750, .t751] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t748) (exponents .t748) (c .t748) a = c .t748 := by
    have h : exponents .t748 = ![9, 1, 6] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t749) (exponents .t748) (c .t749) a = ((7 * c .t749) * a 2) := by
    have hk : exponents .t748 = ![9, 1, 6] := rfl
    have h : exponents .t749 = ![9, 1, 7] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t750) (exponents .t748) (c .t750) a = (((28 * c .t750) * a 2) * a 2) := by
    have hk : exponents .t748 = ![9, 1, 6] := rfl
    have h : exponents .t750 = ![9, 1, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t751) (exponents .t748) (c .t751) a = ((((84 * c .t751) * a 2) * a 2) * a 2) := by
    have hk : exponents .t748 = ![9, 1, 6] := rfl
    have h : exponents .t751 = ![9, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 6 = 84 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t748_9_1_6_interval_bound (c .t748) (c .t749) (c .t750) (c .t751) (a := a 2) h0 h1 h2 h3 ha

theorem t749_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_9_1_7.mem (c .t749))
    (h1 : ThomsonNine.ChainBinding.R1_9_1_7.mem (c .t750))
    (h2 : ThomsonNine.ChainBinding.R2_9_1_7.mem (c .t751))
    (ha : ThomsonNine.ChainBinding.A_9_1_7.mem (a 2)) :
    (coefficientInterval .t749).mem (ThomsonNine.GatheredBinding.gathered (exponents .t749) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t749 i ≤ exponents t i)) = [.t749, .t750, .t751] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t749) (exponents .t749) (c .t749) a = c .t749 := by
    have h : exponents .t749 = ![9, 1, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t750) (exponents .t749) (c .t750) a = ((8 * c .t750) * a 2) := by
    have hk : exponents .t749 = ![9, 1, 7] := rfl
    have h : exponents .t750 = ![9, 1, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t751) (exponents .t749) (c .t751) a = (((36 * c .t751) * a 2) * a 2) := by
    have hk : exponents .t749 = ![9, 1, 7] := rfl
    have h : exponents .t751 = ![9, 1, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t749_9_1_7_interval_bound (c .t749) (c .t750) (c .t751) (a := a 2) h0 h1 h2 ha

theorem t761_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_9_6_1.mem (c .t761))
    (h1 : ThomsonNine.ChainBinding.R1_9_6_1.mem (c .t763))
    (h2 : ThomsonNine.ChainBinding.R2_9_6_1.mem (c .t765))
    (h3 : ThomsonNine.ChainBinding.R3_9_6_1.mem (c .t767))
    (ha : ThomsonNine.ChainBinding.A_9_6_1.mem (a 1)) :
    (coefficientInterval .t761).mem (ThomsonNine.GatheredBinding.gathered (exponents .t761) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t761 i ≤ exponents t i)) = [.t761, .t763, .t765, .t767] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t761) (exponents .t761) (c .t761) a = c .t761 := by
    have h : exponents .t761 = ![9, 6, 1] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t763) (exponents .t761) (c .t763) a = ((7 * c .t763) * a 1) := by
    have hk : exponents .t761 = ![9, 6, 1] := rfl
    have h : exponents .t763 = ![9, 7, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t765) (exponents .t761) (c .t765) a = (((28 * c .t765) * a 1) * a 1) := by
    have hk : exponents .t761 = ![9, 6, 1] := rfl
    have h : exponents .t765 = ![9, 8, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 8 6 = 28 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t767) (exponents .t761) (c .t767) a = ((((84 * c .t767) * a 1) * a 1) * a 1) := by
    have hk : exponents .t761 = ![9, 6, 1] := rfl
    have h : exponents .t767 = ![9, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 6 = 84 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t761_9_6_1_interval_bound (c .t761) (c .t763) (c .t765) (c .t767) (a := a 1) h0 h1 h2 h3 ha

theorem t763_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_9_7_1.mem (c .t763))
    (h1 : ThomsonNine.ChainBinding.R1_9_7_1.mem (c .t765))
    (h2 : ThomsonNine.ChainBinding.R2_9_7_1.mem (c .t767))
    (ha : ThomsonNine.ChainBinding.A_9_7_1.mem (a 1)) :
    (coefficientInterval .t763).mem (ThomsonNine.GatheredBinding.gathered (exponents .t763) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t763 i ≤ exponents t i)) = [.t763, .t765, .t767] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t763) (exponents .t763) (c .t763) a = c .t763 := by
    have h : exponents .t763 = ![9, 7, 1] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t765) (exponents .t763) (c .t765) a = ((8 * c .t765) * a 1) := by
    have hk : exponents .t763 = ![9, 7, 1] := rfl
    have h : exponents .t765 = ![9, 8, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t767) (exponents .t763) (c .t767) a = (((36 * c .t767) * a 1) * a 1) := by
    have hk : exponents .t763 = ![9, 7, 1] := rfl
    have h : exponents .t767 = ![9, 9, 1] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t763_9_7_1_interval_bound (c .t763) (c .t765) (c .t767) (a := a 1) h0 h1 h2 ha

theorem t776_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_10_0_7.mem (c .t776))
    (h1 : ThomsonNine.ChainBinding.R1_10_0_7.mem (c .t777))
    (h2 : ThomsonNine.ChainBinding.R2_10_0_7.mem (c .t778))
    (h3 : ThomsonNine.ChainBinding.R3_10_0_7.mem (c .t779))
    (ha : ThomsonNine.ChainBinding.A_10_0_7.mem (a 2)) :
    (coefficientInterval .t776).mem (ThomsonNine.GatheredBinding.gathered (exponents .t776) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t776 i ≤ exponents t i)) = [.t776, .t777, .t778, .t779] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t776) (exponents .t776) (c .t776) a = c .t776 := by
    have h : exponents .t776 = ![10, 0, 7] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t777) (exponents .t776) (c .t777) a = ((8 * c .t777) * a 2) := by
    have hk : exponents .t776 = ![10, 0, 7] := rfl
    have h : exponents .t777 = ![10, 0, 8] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t778) (exponents .t776) (c .t778) a = (((36 * c .t778) * a 2) * a 2) := by
    have hk : exponents .t776 = ![10, 0, 7] := rfl
    have h : exponents .t778 = ![10, 0, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t779) (exponents .t776) (c .t779) a = ((((120 * c .t779) * a 2) * a 2) * a 2) := by
    have hk : exponents .t776 = ![10, 0, 7] := rfl
    have h : exponents .t779 = ![10, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 7 = 120 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t776_10_0_7_interval_bound (c .t776) (c .t777) (c .t778) (c .t779) (a := a 2) h0 h1 h2 h3 ha

theorem t777_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_10_0_8.mem (c .t777))
    (h1 : ThomsonNine.ChainBinding.R1_10_0_8.mem (c .t778))
    (h2 : ThomsonNine.ChainBinding.R2_10_0_8.mem (c .t779))
    (ha : ThomsonNine.ChainBinding.A_10_0_8.mem (a 2)) :
    (coefficientInterval .t777).mem (ThomsonNine.GatheredBinding.gathered (exponents .t777) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t777 i ≤ exponents t i)) = [.t777, .t778, .t779] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t777) (exponents .t777) (c .t777) a = c .t777 := by
    have h : exponents .t777 = ![10, 0, 8] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t778) (exponents .t777) (c .t778) a = ((9 * c .t778) * a 2) := by
    have hk : exponents .t777 = ![10, 0, 8] := rfl
    have h : exponents .t778 = ![10, 0, 9] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t779) (exponents .t777) (c .t779) a = (((45 * c .t779) * a 2) * a 2) := by
    have hk : exponents .t777 = ![10, 0, 8] := rfl
    have h : exponents .t779 = ![10, 0, 10] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 8 = 45 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t777_10_0_8_interval_bound (c .t777) (c .t778) (c .t779) (a := a 2) h0 h1 h2 ha

theorem t786_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_10_7_0.mem (c .t786))
    (h1 : ThomsonNine.ChainBinding.R1_10_7_0.mem (c .t787))
    (h2 : ThomsonNine.ChainBinding.R2_10_7_0.mem (c .t788))
    (h3 : ThomsonNine.ChainBinding.R3_10_7_0.mem (c .t789))
    (ha : ThomsonNine.ChainBinding.A_10_7_0.mem (a 1)) :
    (coefficientInterval .t786).mem (ThomsonNine.GatheredBinding.gathered (exponents .t786) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t786 i ≤ exponents t i)) = [.t786, .t787, .t788, .t789] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t786) (exponents .t786) (c .t786) a = c .t786 := by
    have h : exponents .t786 = ![10, 7, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t787) (exponents .t786) (c .t787) a = ((8 * c .t787) * a 1) := by
    have hk : exponents .t786 = ![10, 7, 0] := rfl
    have h : exponents .t787 = ![10, 8, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t788) (exponents .t786) (c .t788) a = (((36 * c .t788) * a 1) * a 1) := by
    have hk : exponents .t786 = ![10, 7, 0] := rfl
    have h : exponents .t788 = ![10, 9, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 9 7 = 36 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t789) (exponents .t786) (c .t789) a = ((((120 * c .t789) * a 1) * a 1) * a 1) := by
    have hk : exponents .t786 = ![10, 7, 0] := rfl
    have h : exponents .t789 = ![10, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 7 = 120 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t786_10_7_0_interval_bound (c .t786) (c .t787) (c .t788) (c .t789) (a := a 1) h0 h1 h2 h3 ha

theorem t787_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_10_8_0.mem (c .t787))
    (h1 : ThomsonNine.ChainBinding.R1_10_8_0.mem (c .t788))
    (h2 : ThomsonNine.ChainBinding.R2_10_8_0.mem (c .t789))
    (ha : ThomsonNine.ChainBinding.A_10_8_0.mem (a 1)) :
    (coefficientInterval .t787).mem (ThomsonNine.GatheredBinding.gathered (exponents .t787) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t787 i ≤ exponents t i)) = [.t787, .t788, .t789] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t787) (exponents .t787) (c .t787) a = c .t787 := by
    have h : exponents .t787 = ![10, 8, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t788) (exponents .t787) (c .t788) a = ((9 * c .t788) * a 1) := by
    have hk : exponents .t787 = ![10, 8, 0] := rfl
    have h : exponents .t788 = ![10, 9, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t789) (exponents .t787) (c .t789) a = (((45 * c .t789) * a 1) * a 1) := by
    have hk : exponents .t787 = ![10, 8, 0] := rfl
    have h : exponents .t789 = ![10, 10, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 10 8 = 45 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t787_10_8_0_interval_bound (c .t787) (c .t788) (c .t789) (a := a 1) h0 h1 h2 ha

theorem t803_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_24_0_0.mem (c .t803))
    (h1 : ThomsonNine.ChainBinding.R1_24_0_0.mem (c .t804))
    (h2 : ThomsonNine.ChainBinding.R2_24_0_0.mem (c .t805))
    (h3 : ThomsonNine.ChainBinding.R3_24_0_0.mem (c .t806))
    (ha : ThomsonNine.ChainBinding.A_24_0_0.mem (a 0)) :
    (coefficientInterval .t803).mem (ThomsonNine.GatheredBinding.gathered (exponents .t803) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t803 i ≤ exponents t i)) = [.t803, .t804, .t805, .t806] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t803) (exponents .t803) (c .t803) a = c .t803 := by
    have h : exponents .t803 = ![24, 0, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t804) (exponents .t803) (c .t804) a = ((25 * c .t804) * a 0) := by
    have hk : exponents .t803 = ![24, 0, 0] := rfl
    have h : exponents .t804 = ![25, 0, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t805) (exponents .t803) (c .t805) a = (((325 * c .t805) * a 0) * a 0) := by
    have hk : exponents .t803 = ![24, 0, 0] := rfl
    have h : exponents .t805 = ![26, 0, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 26 24 = 325 := by decide
    rw [hc]
    ring_nf
  have he3 : expandedCoefficient (exponents .t806) (exponents .t803) (c .t806) a = ((((2925 * c .t806) * a 0) * a 0) * a 0) := by
    have hk : exponents .t803 = ![24, 0, 0] := rfl
    have h : exponents .t806 = ![27, 0, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 27 24 = 2925 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2, he3]
  exact ThomsonNine.ChainBinding.target_t803_24_0_0_interval_bound (c .t803) (c .t804) (c .t805) (c .t806) (a := a 0) h0 h1 h2 h3 ha

theorem t804_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.ChainBinding.R0_25_0_0.mem (c .t804))
    (h1 : ThomsonNine.ChainBinding.R1_25_0_0.mem (c .t805))
    (h2 : ThomsonNine.ChainBinding.R2_25_0_0.mem (c .t806))
    (ha : ThomsonNine.ChainBinding.A_25_0_0.mem (a 0)) :
    (coefficientInterval .t804).mem (ThomsonNine.GatheredBinding.gathered (exponents .t804) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t804 i ≤ exponents t i)) = [.t804, .t805, .t806] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t804) (exponents .t804) (c .t804) a = c .t804 := by
    have h : exponents .t804 = ![25, 0, 0] := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t805) (exponents .t804) (c .t805) a = ((26 * c .t805) * a 0) := by
    have hk : exponents .t804 = ![25, 0, 0] := rfl
    have h : exponents .t805 = ![26, 0, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring
  have he2 : expandedCoefficient (exponents .t806) (exponents .t804) (c .t806) a = (((351 * c .t806) * a 0) * a 0) := by
    have hk : exponents .t804 = ![25, 0, 0] := rfl
    have h : exponents .t806 = ![27, 0, 0] := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose 27 25 = 351 := by decide
    rw [hc]
    ring_nf
  rw [he0, he1, he2]
  exact ThomsonNine.ChainBinding.target_t804_25_0_0_interval_bound (c .t804) (c .t805) (c .t806) (a := a 0) h0 h1 h2 ha

end ThomsonNine.GatheredChain

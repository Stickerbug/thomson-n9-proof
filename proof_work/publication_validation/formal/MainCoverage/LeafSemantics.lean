import MainCoverage.TreeModel
import PackedTensor.Linear

noncomputable section
namespace ThomsonNine.PackedMain
open scoped BigOperators
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix
attribute [local irreducible] packetValue

def axisCurve (e : AxisEntry) (t : ℝ) : ℝ :=
  curve 10 (fun i => ((axisValues e i : ℝ)-(offset : ℝ))/(scale : ℝ)) t

theorem scale_pos : (0 : ℝ)<scale := by norm_num [scale,Nat.shiftLeft_eq]
theorem bound_valid : 2*bound+1<2^128 := by decide +kernel
theorem sum_bound_valid : 4*bound<2^128 := by decide +kernel
theorem sum_offset_valid : 4*offset<2^128 := by decide +kernel

theorem positive_leaf (lookup : ℕ → AxisEntry) (s : State) (slot : Fin 4) (h0 h1 h2 : ℕ)
    (h : positiveOK lookup s slot h0 h1 h2=true)
    (x : Fin 3 → ℝ) (hx : ∀ a, 0≤x a ∧ x a≤1) :
    0≤packetValue 10 offset scale (s.kernels slot) x+
      axisCurve (lookup h0) (x 0)+axisCurve (lookup h1) (x 1)+axisCurve (lookup h2) (x 2) := by
  have hp := Bool.and_eq_true_iff.mp h
  have he : ∀ a : Fin 3, (![lookup h0,lookup h1,lookup h2] a).level=s.levels a ∧
      (![lookup h0,lookup h1,lookup h2] a).index=s.indices a ∧
      broadcastOK 1331 bound planes11 a (axisValues (![lookup h0,lookup h1,lookup h2] a))
        (broadcast (![lookup h0,lookup h1,lookup h2] a) a)=true := of_decide_eq_true hp.1
  dsimp only [axisCurve]
  exact four_packet_positive 10 1331 bound offset scale planes11 planes11_correct
    (s.kernels slot) (broadcast (lookup h0) 0) (broadcast (lookup h1) 1) (broadcast (lookup h2) 2)
    (axisValues (lookup h0)) (axisValues (lookup h1)) (axisValues (lookup h2))
    (he 0).2.2 (he 1).2.2 (he 2).2.2 sum_bound_valid sum_offset_valid hp.2 scale_pos (by omega) x hx

theorem gram_leaf (s : State) (h : gramOK s=true)
    (x : Fin 3 → ℝ) (hx : ∀ a, 0≤x a ∧ x a≤1) :
    0<packetValue 2 offset scale s.gram x := by
  have hp : ∀ i j k : Fin 3, offset<limb 128 s.gram (index 3 i j k) := of_decide_eq_true h
  have hc (p : CubeIndex 3) : (1 : ℝ)/(scale : ℝ)≤packetCoefficients 2 offset scale s.gram p := by
    have hi := hp p.1 p.2.1 p.2.2
    have hr : (offset : ℝ)+1≤(limb 128 s.gram (flat p) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hi)
    change (1 : ℝ)/(scale : ℝ)≤((limb 128 s.gram (flat p) : ℝ)-(offset : ℝ))/(scale : ℝ)
    apply (div_le_div_iff_of_pos_right scale_pos).mpr
    linarith
  exact (one_div_pos.mpr scale_pos).trans_le (packet_value_ge 2 offset scale s.gram _ hc x hx)
end ThomsonNine.PackedMain

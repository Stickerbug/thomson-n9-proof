import ThomsonNine.LocalNonneg
import ThomsonNine.LeafSemantics

/-! Elementary Gram boundary geometry and a conditional residual extension.
No residual evaluation, exact contact, or boundary derivative bound is asserted here.
-/

namespace ThomsonNine.LocalLDL

open ThomsonNine.Semantics

noncomputable def lowerGraph (v t : ℝ) : ℝ :=
  v * t - Real.sqrt ((1 - v ^ 2) * (1 - t ^ 2))

noncomputable def upperGraph (v t : ℝ) : ℝ :=
  v * t + Real.sqrt ((1 - v ^ 2) * (1 - t ^ 2))

theorem gram_eq_radicand_sub_sq (u v t : ℝ) :
    gram u v t = (1 - v ^ 2) * (1 - t ^ 2) - (u - v * t) ^ 2 := by
  unfold gram
  ring

theorem radicand_nonneg {v t : ℝ} (hv : -1 ≤ v ∧ v ≤ 1)
    (ht : -1 ≤ t ∧ t ≤ 1) : 0 ≤ (1 - v ^ 2) * (1 - t ^ 2) := by
  have hv2 : 0 ≤ 1 - v ^ 2 := by nlinarith [sq_le_sq' hv.1 hv.2]
  have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith [sq_le_sq' ht.1 ht.2]
  exact mul_nonneg hv2 ht2

theorem gram_lowerGraph_zero {v t : ℝ} (hv : -1 ≤ v ∧ v ≤ 1)
    (ht : -1 ≤ t ∧ t ≤ 1) : gram (lowerGraph v t) v t = 0 := by
  have hshift : lowerGraph v t - v * t =
      -Real.sqrt ((1 - v ^ 2) * (1 - t ^ 2)) := by unfold lowerGraph; ring
  rw [gram_eq_radicand_sub_sq, hshift, neg_sq, Real.sq_sqrt (radicand_nonneg hv ht)]
  exact sub_self _

/-- A Gram-feasible point lies between the two radical graphs. -/
theorem feasible_between_graphs {u v t : ℝ} (hv : -1 ≤ v ∧ v ≤ 1)
    (ht : -1 ≤ t ∧ t ≤ 1) (hg : 0 ≤ gram u v t) :
    lowerGraph v t ≤ u ∧ u ≤ upperGraph v t := by
  have hs := Real.sq_sqrt (radicand_nonneg hv ht)
  have hn := Real.sqrt_nonneg ((1 - v ^ 2) * (1 - t ^ 2))
  have hsq : (u - v * t) ^ 2 ≤
      Real.sqrt ((1 - v ^ 2) * (1 - t ^ 2)) ^ 2 := by
    rw [gram_eq_radicand_sub_sq] at hg
    nlinarith only [hg, hs]
  have hb := abs_le_of_sq_le_sq' hsq hn
  unfold lowerGraph upperGraph
  constructor <;> linarith [hb.1, hb.2]

/-- Monotone extension from the lower graph, on an expanded interval containing
both that graph value and the source point. All analytic bindings remain premises. -/
theorem residual_nonneg_of_graph {R : ℝ → ℝ → ℝ → ℝ} {Ru : ℝ → ℝ}
    {D : Set ℝ} {u v t : ℝ} (hv : -1 ≤ v ∧ v ≤ 1)
    (ht : -1 ≤ t ∧ t ≤ 1) (hg : 0 ≤ gram u v t)
    (hD : Convex ℝ D) (hc : ContinuousOn (fun s => R s v t) D)
    (hd : ∀ s ∈ interior D, HasDerivAt (fun q => R q v t) (Ru s) s)
    (hpos : ∀ s ∈ interior D, 0 ≤ Ru s)
    (hb : lowerGraph v t ∈ D) (hu : u ∈ D)
    (hgraph : 0 ≤ R (lowerGraph v t) v t) : 0 ≤ R u v t := by
  exact nonneg_above_boundary (f := fun s => R s v t) (f' := Ru)
    (b := lowerGraph v t) (u := u) hD hc hd hpos hb hu
    (feasible_between_graphs hv ht hg).1 hgraph

end ThomsonNine.LocalLDL

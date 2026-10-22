import ThomsonNine.Construction.LocalBoundary.C07.GraphData
import ThomsonNine.Construction.LocalShift.BoundaryExtension
import ThomsonNine.IntervalLocalOps

-- Isolated source: LocalBoundary.C07.Nonnegative
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C07
open ThomsonNine.FixedInterval ThomsonNine.FixedInterval.Schur ThomsonNine.ActualLocalAAA
open ThomsonNine.Interval.RatInterval
attribute [local irreducible] entries ActualR.residual
theorem center_source_bounds : ∀ a, (sourceBox a).lo≤(LocalShift.centerInterval localId a).lo ∧
    (LocalShift.centerInterval localId a).hi≤(sourceBox a).hi := by decide +kernel
theorem center_source_mem (a : Fin 3) : (sourceBox a).mem (LocalShift.center localId a) :=
  mem_subset (LocalShift.center_interval_mem localId a) (center_source_bounds a).1 (center_source_bounds a).2
theorem source_strict_bounds : ∀ a : Fin 2, -1<(sourceBox a.succ).lo ∧ (sourceBox a.succ).hi<1 := by decide +kernel
theorem source_unit {v t : ℝ} (hv : (sourceBox 1).mem v) (ht : (sourceBox 2).mem t) :
    0<1-v^2 ∧ 0<1-t^2 := by
  have hvlo : (-1 : ℝ)<(sourceBox 1).lo := by exact_mod_cast (source_strict_bounds 0).1
  have hvhi : ((sourceBox 1).hi : ℝ)<1 := by exact_mod_cast (source_strict_bounds 0).2
  have htlo : (-1 : ℝ)<(sourceBox 2).lo := by exact_mod_cast (source_strict_bounds 1).1
  have hthi : ((sourceBox 2).hi : ℝ)<1 := by exact_mod_cast (source_strict_bounds 1).2
  constructor <;> nlinarith [hv.1,hv.2,ht.1,ht.2]
theorem relative_bounds : ∀ a, (relativeBox a).lo≤((expandedBox a).sub (LocalShift.centerInterval localId a)).lo ∧
    ((expandedBox a).sub (LocalShift.centerInterval localId a)).hi≤(relativeBox a).hi := by decide +kernel
theorem relative_mem (p : Fin 3 → ℝ) (h0 : (expandedBox 0).mem (p 0))
    (h1 : (sourceBox 1).mem (p 1)) (h2 : (sourceBox 2).mem (p 2)) (a : Fin 3) :
    (relativeBox a).mem (p a-LocalShift.center localId a) := by
  have hp : (expandedBox a).mem (p a) := by
    fin_cases a
    · exact h0
    · exact h1
    · exact h2
  exact mem_subset (mem_sub hp (LocalShift.center_interval_mem localId a)) (relative_bounds a).1 (relative_bounds a).2
theorem graph_bounds : (LocalShift.scale : ℚ)*(expandedBox 0).lo≤graphInput.lo ∧
    (graphInput.hi : ℚ)≤(LocalShift.scale : ℚ)*(expandedBox 0).hi := by decide +kernel
theorem graph_mem {v t : ℝ} (hv : (sourceBox 1).mem v) (ht : (sourceBox 2).mem t) :
    (expandedBox 0).mem (LocalLDL.lowerGraph v t) := by
  have h : Mem LocalShift.scale graphInput (LocalLDL.lowerGraph v t) :=
    mem_subtract (mem_mul LocalShift.scale_pos (source_mem 1 hv) (source_mem 2 ht)) (radical_mem hv ht)
  exact mem_to_rat h LocalShift.scale_pos graph_bounds.1 graph_bounds.2
theorem graph_relative_mem {v t : ℝ} (hv : (sourceBox 1).mem v) (ht : (sourceBox 2).mem t) (a : Fin 3) :
    (relativeBox a).mem (LocalShift.relativeGraph localId v t a) :=
  relative_mem (GramGraph.point v t) (graph_mem hv ht) hv ht a
theorem actual_graph_nonnegative (v t : ℝ) (hv : (sourceBox 1).mem v) (ht : (sourceBox 2).mem t) :
    0≤ActualR.residual (GramGraph.point v t) := by
  apply LocalShift.graph_nonnegative localId (by unfold LocalShift.IsBoundary;decide +kernel)
    sourceBox center_source_mem (fun v t hv ht => source_unit hv ht) _ v t hv ht
  intro v t hv ht w
  exact graph_directional_nonnegative hv ht _ (graph_relative_mem hv ht) w
theorem source_expanded_bounds : (expandedBox 0).lo≤(sourceBox 0).lo ∧ (sourceBox 0).hi≤(expandedBox 0).hi := by decide +kernel
theorem actual_residual_nonnegative (p : Fin 3 → ℝ) (hp : ∀ a, (sourceBox a).mem (p a))
    (hg : 0≤Semantics.gram (p 0) (p 1) (p 2)) : 0≤ActualR.residual p := by
  exact LocalShift.boundary_extension localId sourceBox relativeBox (expandedBox 0)
    (fun v t hv ht => source_unit hv ht)
    (fun u hu => mem_subset hu source_expanded_bounds.1 source_expanded_bounds.2)
    (fun v t hv ht => graph_mem hv ht) relative_mem
    (fun x hx => le_of_lt (gradient_u_positive x hx)) actual_graph_nonnegative p hp hg
end ThomsonNine.ActualBoundary.C07

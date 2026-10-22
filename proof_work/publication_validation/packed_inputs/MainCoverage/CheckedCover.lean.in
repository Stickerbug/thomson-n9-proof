import MainCoverage.ChunkModel
import MainCoverage.ActualAxes
import MainCoverage.LocalMeaning
import MainCoverage.GlobalAssembly

noncomputable section
namespace ThomsonNine.PackedMain

theorem ordered_residual_from_frontier (chunks : ℕ → CertifiedChunk) (cut : CutTree)
    (hCut : cutCheck (fun id => (chunks id).path) [] cut=true)
    (p : Fin 3 → ℝ) (hp : RootCube p) (ho : Monotone p) (hG : 0≤gramFn p) :
    0≤ActualCoulombGlobal.residual p := by
  let G := fun x : Fin 3 → ℝ => Semantics.gram (x 0) (x 1) (x 2)
  have hcert (id : ℕ) (z : Fin 3 → ℝ) (hz : UnitCube z)
      (hord : Monotone (boxPoint (atPath rootState (chunks id).path) z))
      (hgram : 0≤G (boxPoint (atPath rootState (chunks id).path) z)) :
      0≤ActualCoulombGlobal.residual (boxPoint (atPath rootState (chunks id).path) z) := by
    have hf := path_frame penalizedKernel G actual_fallback rootState root_valid actual_root_frame
      (chunks id).path (chunks id).certificate.1
    exact check_sound axisLookup localCores penalizedKernel G ActualCoulombGlobal.residual
      (fun t => ActualCoulombGlobal.coulomb t-MainEnvelope.diagonal t) actual_fallback actual_axes_lower
      actual_dominates actual_local_lower (chunks id).tree (atPath rootState (chunks id).path)
      hf.1 hf.2 (chunks id).certificate.2 z hz hord hgram
  have he : boxPoint (atPath rootState []) (rootCoordinates p)=p :=
    root_point_eq rootState (fun _ => rfl) (fun _ => rfl) p
  have h := cutCover (fun id => (chunks id).path) rootState G ActualCoulombGlobal.residual hcert
    cut [] hCut (rootCoordinates p) (rootCoordinates_mem p hp)
    (by rw [he];exact ho) (by rw [he];exact hG)
  simpa only [he] using h

theorem claim_from_certified_frontier (chunks : ℕ → CertifiedChunk) (cut : CutTree)
    (hCut : cutCheck (fun id => (chunks id).path) [] cut=true) : ThomsonNineClaim :=
  frozen_claim_of_ordered_residual (ordered_residual_from_frontier chunks cut hCut)
end ThomsonNine.PackedMain

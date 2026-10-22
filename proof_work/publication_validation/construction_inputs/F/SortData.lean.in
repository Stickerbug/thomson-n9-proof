import ThomsonNine.Construction.SortBatches.Batch15

-- Isolated source: F.SortData
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualF.Data
theorem groups_partition : ((List.finRange 756).flatMap groups).Perm (List.range count) := by
  have h : Sort.Node124.targets=List.finRange 756 := by decide +kernel
  have hp := Sort.Node124.candidate_perm
  rw [h] at hp
  exact hp.symm
end ThomsonNine.ActualF.Data

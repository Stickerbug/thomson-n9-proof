import ThomsonNine.Construction.R.PartitionCache

-- Isolated source: R.Partition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualR.Collection
theorem cache_sorted : FiniteCollector.sortFuel 12 flatCache=List.range 3109 := by decide +kernel
theorem partition_sorted : FiniteCollector.sortFuel 12 ((List.finRange 807).flatMap groups)=List.range 3109 := by
  rw [flatCache_eq]
  exact cache_sorted
theorem partition : ((List.finRange 807).flatMap groups).Perm (List.range 3109) :=
  FiniteCollector.partition_of_fuel_sorted partition_sorted
end ThomsonNine.ActualR.Collection

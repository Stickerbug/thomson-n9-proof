import MainCoverage.Chunks.C0400Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0400_checked : pathOK rootState path0400=true := by decide +kernel
theorem cache0400_checked : stateEqual (atPath rootState path0400) cachedState0400=true := by decide +kernel
theorem cache0400_equal : atPath rootState path0400=cachedState0400 := stateEqual_sound _ _ cache0400_checked
end ThomsonNine.PackedMain

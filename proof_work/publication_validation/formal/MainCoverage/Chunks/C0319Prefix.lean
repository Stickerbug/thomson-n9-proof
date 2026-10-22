import MainCoverage.Chunks.C0319Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0319_checked : pathOK rootState path0319=true := by decide +kernel
theorem cache0319_checked : stateEqual (atPath rootState path0319) cachedState0319=true := by decide +kernel
theorem cache0319_equal : atPath rootState path0319=cachedState0319 := stateEqual_sound _ _ cache0319_checked
end ThomsonNine.PackedMain

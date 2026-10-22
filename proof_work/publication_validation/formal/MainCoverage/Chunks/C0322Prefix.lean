import MainCoverage.Chunks.C0322Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0322_checked : pathOK rootState path0322=true := by decide +kernel
theorem cache0322_checked : stateEqual (atPath rootState path0322) cachedState0322=true := by decide +kernel
theorem cache0322_equal : atPath rootState path0322=cachedState0322 := stateEqual_sound _ _ cache0322_checked
end ThomsonNine.PackedMain

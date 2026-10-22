import MainCoverage.Chunks.C0414Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0414_checked : pathOK rootState path0414=true := by decide +kernel
theorem cache0414_checked : stateEqual (atPath rootState path0414) cachedState0414=true := by decide +kernel
theorem cache0414_equal : atPath rootState path0414=cachedState0414 := stateEqual_sound _ _ cache0414_checked
end ThomsonNine.PackedMain

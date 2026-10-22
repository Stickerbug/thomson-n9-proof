import MainCoverage.Chunks.C0334Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0334_checked : pathOK rootState path0334=true := by decide +kernel
theorem cache0334_checked : stateEqual (atPath rootState path0334) cachedState0334=true := by decide +kernel
theorem cache0334_equal : atPath rootState path0334=cachedState0334 := stateEqual_sound _ _ cache0334_checked
end ThomsonNine.PackedMain

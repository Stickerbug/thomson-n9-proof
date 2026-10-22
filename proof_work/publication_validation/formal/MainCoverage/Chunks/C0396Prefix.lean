import MainCoverage.Chunks.C0396Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0396_checked : pathOK rootState path0396=true := by decide +kernel
theorem cache0396_checked : stateEqual (atPath rootState path0396) cachedState0396=true := by decide +kernel
theorem cache0396_equal : atPath rootState path0396=cachedState0396 := stateEqual_sound _ _ cache0396_checked
end ThomsonNine.PackedMain

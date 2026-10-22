import MainCoverage.Chunks.C0401Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0401_checked : pathOK rootState path0401=true := by decide +kernel
theorem cache0401_checked : stateEqual (atPath rootState path0401) cachedState0401=true := by decide +kernel
theorem cache0401_equal : atPath rootState path0401=cachedState0401 := stateEqual_sound _ _ cache0401_checked
end ThomsonNine.PackedMain

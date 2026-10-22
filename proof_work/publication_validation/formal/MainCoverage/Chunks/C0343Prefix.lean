import MainCoverage.Chunks.C0343Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0343_checked : pathOK rootState path0343=true := by decide +kernel
theorem cache0343_checked : stateEqual (atPath rootState path0343) cachedState0343=true := by decide +kernel
theorem cache0343_equal : atPath rootState path0343=cachedState0343 := stateEqual_sound _ _ cache0343_checked
end ThomsonNine.PackedMain

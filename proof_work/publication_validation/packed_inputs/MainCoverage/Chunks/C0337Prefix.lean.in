import MainCoverage.Chunks.C0337Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0337_checked : pathOK rootState path0337=true := by decide +kernel
theorem cache0337_checked : stateEqual (atPath rootState path0337) cachedState0337=true := by decide +kernel
theorem cache0337_equal : atPath rootState path0337=cachedState0337 := stateEqual_sound _ _ cache0337_checked
end ThomsonNine.PackedMain

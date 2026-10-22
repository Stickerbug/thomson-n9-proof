import MainCoverage.Chunks.C0330Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0330_checked : pathOK rootState path0330=true := by decide +kernel
theorem cache0330_checked : stateEqual (atPath rootState path0330) cachedState0330=true := by decide +kernel
theorem cache0330_equal : atPath rootState path0330=cachedState0330 := stateEqual_sound _ _ cache0330_checked
end ThomsonNine.PackedMain

import MainCoverage.Chunks.C0316Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0316_checked : pathOK rootState path0316=true := by decide +kernel
theorem cache0316_checked : stateEqual (atPath rootState path0316) cachedState0316=true := by decide +kernel
theorem cache0316_equal : atPath rootState path0316=cachedState0316 := stateEqual_sound _ _ cache0316_checked
end ThomsonNine.PackedMain

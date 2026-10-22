import MainCoverage.Chunks.C0416Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0416_checked : pathOK rootState path0416=true := by decide +kernel
theorem cache0416_checked : stateEqual (atPath rootState path0416) cachedState0416=true := by decide +kernel
theorem cache0416_equal : atPath rootState path0416=cachedState0416 := stateEqual_sound _ _ cache0416_checked
end ThomsonNine.PackedMain

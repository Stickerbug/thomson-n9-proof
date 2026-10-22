import MainCoverage.Chunks.C0321Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem prefix0321_checked : pathOK rootState path0321=true := by decide +kernel
theorem cache0321_checked : stateEqual (atPath rootState path0321) cachedState0321=true := by decide +kernel
theorem cache0321_equal : atPath rootState path0321=cachedState0321 := stateEqual_sound _ _ cache0321_checked
end ThomsonNine.PackedMain

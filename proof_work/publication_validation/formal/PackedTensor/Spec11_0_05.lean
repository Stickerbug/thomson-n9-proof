import PackedTensor.MaskData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PackedTensor
theorem spec11_0_05 : ∀ i j k : Fin 11,
    PackedRadix.limb 128 (planes11 0 5) (index 11 i j k)=
      if (coordinate 11 0 i j k).val=5 then 2^128-1 else 0 := by decide +kernel
end ThomsonNine.PackedTensor

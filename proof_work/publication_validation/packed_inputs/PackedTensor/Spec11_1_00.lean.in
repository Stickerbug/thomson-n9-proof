import PackedTensor.MaskData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PackedTensor
theorem spec11_1_00 : ∀ i j k : Fin 11,
    PackedRadix.limb 128 (planes11 1 0) (index 11 i j k)=
      if (coordinate 11 1 i j k).val=0 then 2^128-1 else 0 := by decide +kernel
end ThomsonNine.PackedTensor

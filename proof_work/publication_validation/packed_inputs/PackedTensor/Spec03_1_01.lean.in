import PackedTensor.MaskData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PackedTensor
theorem spec03_1_01 : ∀ i j k : Fin 3,
    PackedRadix.limb 128 (planes3 1 1) (index 3 i j k)=
      if (coordinate 3 1 i j k).val=1 then 2^128-1 else 0 := by decide +kernel
end ThomsonNine.PackedTensor

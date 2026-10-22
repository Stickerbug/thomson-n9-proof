import PackedTensor.MaskData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PackedTensor
theorem spec03_2_00 : ∀ i j k : Fin 3,
    PackedRadix.limb 128 (planes3 2 0) (index 3 i j k)=
      if (coordinate 3 2 i j k).val=0 then 2^128-1 else 0 := by decide +kernel
end ThomsonNine.PackedTensor

import PackedTensor.Spec03_0_00
import PackedTensor.Spec03_0_01
import PackedTensor.Spec03_0_02
import PackedTensor.Spec03_1_00
import PackedTensor.Spec03_1_01
import PackedTensor.Spec03_1_02
import PackedTensor.Spec03_2_00
import PackedTensor.Spec03_2_01
import PackedTensor.Spec03_2_02
import PackedTensor.Spec11_0_00
import PackedTensor.Spec11_0_01
import PackedTensor.Spec11_0_02
import PackedTensor.Spec11_0_03
import PackedTensor.Spec11_0_04
import PackedTensor.Spec11_0_05
import PackedTensor.Spec11_0_06
import PackedTensor.Spec11_0_07
import PackedTensor.Spec11_0_08
import PackedTensor.Spec11_0_09
import PackedTensor.Spec11_0_10
import PackedTensor.Spec11_1_00
import PackedTensor.Spec11_1_01
import PackedTensor.Spec11_1_02
import PackedTensor.Spec11_1_03
import PackedTensor.Spec11_1_04
import PackedTensor.Spec11_1_05
import PackedTensor.Spec11_1_06
import PackedTensor.Spec11_1_07
import PackedTensor.Spec11_1_08
import PackedTensor.Spec11_1_09
import PackedTensor.Spec11_1_10
import PackedTensor.Spec11_2_00
import PackedTensor.Spec11_2_01
import PackedTensor.Spec11_2_02
import PackedTensor.Spec11_2_03
import PackedTensor.Spec11_2_04
import PackedTensor.Spec11_2_05
import PackedTensor.Spec11_2_06
import PackedTensor.Spec11_2_07
import PackedTensor.Spec11_2_08
import PackedTensor.Spec11_2_09
import PackedTensor.Spec11_2_10
import Mathlib.Tactic.FinCases
namespace ThomsonNine.PackedTensor
theorem planes3_spec (a : Fin 3) (c i j k : Fin 3) :
    PackedRadix.limb 128 (planes3 a c) (index 3 i j k)=
      if (coordinate 3 a i j k).val=c.val then 2^128-1 else 0 := by
  fin_cases a <;> fin_cases c
  · exact spec03_0_00 i j k
  · exact spec03_0_01 i j k
  · exact spec03_0_02 i j k
  · exact spec03_1_00 i j k
  · exact spec03_1_01 i j k
  · exact spec03_1_02 i j k
  · exact spec03_2_00 i j k
  · exact spec03_2_01 i j k
  · exact spec03_2_02 i j k
theorem planes11_spec (a : Fin 3) (c i j k : Fin 11) :
    PackedRadix.limb 128 (planes11 a c) (index 11 i j k)=
      if (coordinate 11 a i j k).val=c.val then 2^128-1 else 0 := by
  fin_cases a <;> fin_cases c
  · exact spec11_0_00 i j k
  · exact spec11_0_01 i j k
  · exact spec11_0_02 i j k
  · exact spec11_0_03 i j k
  · exact spec11_0_04 i j k
  · exact spec11_0_05 i j k
  · exact spec11_0_06 i j k
  · exact spec11_0_07 i j k
  · exact spec11_0_08 i j k
  · exact spec11_0_09 i j k
  · exact spec11_0_10 i j k
  · exact spec11_1_00 i j k
  · exact spec11_1_01 i j k
  · exact spec11_1_02 i j k
  · exact spec11_1_03 i j k
  · exact spec11_1_04 i j k
  · exact spec11_1_05 i j k
  · exact spec11_1_06 i j k
  · exact spec11_1_07 i j k
  · exact spec11_1_08 i j k
  · exact spec11_1_09 i j k
  · exact spec11_1_10 i j k
  · exact spec11_2_00 i j k
  · exact spec11_2_01 i j k
  · exact spec11_2_02 i j k
  · exact spec11_2_03 i j k
  · exact spec11_2_04 i j k
  · exact spec11_2_05 i j k
  · exact spec11_2_06 i j k
  · exact spec11_2_07 i j k
  · exact spec11_2_08 i j k
  · exact spec11_2_09 i j k
  · exact spec11_2_10 i j k
end ThomsonNine.PackedTensor

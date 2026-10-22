import MainCoverage.RootTensor.K03Stage1
import MainCoverage.RootTensor.K03Stage2
import MainCoverage.RootTensor.K03Stage3
import MainCoverage.RootTensor.K03Lower
import MainCoverage.Frame
import PackedTensor.IntegerTransform
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PackedMain.RootTensor.K03
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix
def sourcePolynomial (x : Fin 3 → ℝ) : ℝ := tri (scaledInt coeff0 denominator0)
  (fun i => (x 0)^i.val) (fun j => (x 1)^j.val) (fun k => (x 2)^k.val)
theorem denominator_relation : denominator3=root10Den*(root10Den*(root10Den*denominator0)) ∧ 0<denominator3 := by decide +kernel
attribute [local irreducible] packetValue
theorem root_lower (z : Fin 3 → ℝ) (hz : UnitCube z) :
    packetValue 10 offset scale (rootState.kernels 3) z≤sourcePolynomial (boxPoint rootState z) := by
  have hden : (0:ℝ)<denominator3 := by exact_mod_cast denominator_relation.2
  have hc := packet_lower_integer 10 offset scale denominator3 (rootState.kernels 3) coeff3 scale_pos hden
    (fun p => lower_fields p.1 p.2.1 p.2.2) z hz
  have hSpec : affineMatrixSpec 10 root10 (-1) (39/25) := by simpa only [div_one] using root10_spec
  have he := integer_tensor_transform 10 root10 root10Int root10Den (-1) (39/25)
    root10_fields hSpec coeff0 coeff1 coeff2 coeff3 denominator0
    (fun p => stage1_fields p.1 p.2.1 p.2.2)
    (fun p => stage2_fields p.1 p.2.1 p.2.2)
    (fun p => stage3_fields p.1 p.2.1 p.2.2) z
  rw [← denominator_relation.1] at he
  have hp (a : Fin 3) : (((-1 : ℚ) : ℝ)+((39/25 : ℚ) : ℝ)*z a)=boxPoint rootState z a := by
    simp [boxPoint,rootState,point,left,width]
  have hf (a : Fin 3) : (fun i : Fin 11 => (((-1 : ℚ) : ℝ)+((39/25 : ℚ) : ℝ)*z a)^i.val)=
      fun i => (boxPoint rootState z a)^i.val := funext (fun i => congrArg (fun t : ℝ => t^i.val) (hp a))
  rw [hf 0,hf 1,hf 2] at he
  exact hc.trans_eq he
end ThomsonNine.PackedMain.RootTensor.K03

import MainCoverage.RootTensor.DFields
import MainCoverage.LeafSemantics
import MainCoverage.DyadicGeometry
import PackedTensor.IntegerTransform
import PackedRadix.Univariate

noncomputable section
namespace ThomsonNine.PackedMain.RootTensor.D
open scoped BigOperators
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix

def archiveDiagonal (t : ℝ) : ℝ := ∑ i : Fin 21, (MainEnvelope.Archive.diagonalCoeff i : ℝ)*t^i.val

attribute [local irreducible] uniValue

theorem negative_diagonal_root (t : ℝ) (ht : 0≤t ∧ t≤1) :
    uniValue 20 offset scale diagonalRootWord t≤-archiveDiagonal (point 0 0 t) := by
  have hd : (0:ℝ)<denominator1 := by exact_mod_cast denominator_fields.2
  have hc (i : Fin 21) : decode offset scale diagonalRootWord i.val≤(coeff1 i : ℝ)/(denominator1 : ℝ) :=
    integer_comparison _ offset scale denominator1 (coeff1 i) scale_pos hd (lower_fields i)
  have hl : uniValue 20 offset scale diagonalRootWord t≤curve 20 (fun i => (coeff1 i : ℝ)/(denominator1 : ℝ)) t := by
    unfold uniValue
    exact curve_mono 20 _ _ hc t ht
  have hSpec : affineMatrixSpec 20 root20 (-1) (39/25) := by simpa only [div_one] using root20_spec
  have he := integer_curve_transform 20 root20 root20Int root20Den (-1) (39/25)
    root20_fields hSpec coeff0 coeff1 denominator0 stage_fields t
  rw [denominator_fields.1,he] at hl
  have hs (i : Fin 21) : (coeff0 i : ℝ)/(denominator0 : ℝ)= -(MainEnvelope.Archive.diagonalCoeff i : ℝ) := by
    exact_mod_cast source_fields i
  simp_rw [hs] at hl
  simp only [neg_mul,Finset.sum_neg_distrib] at hl
  simpa only [archiveDiagonal,point,left,width,pow_zero,Nat.cast_zero,mul_zero,
    zero_div,add_zero,div_one,Rat.cast_neg,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using hl
end ThomsonNine.PackedMain.RootTensor.D

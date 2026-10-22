import F.CoefficientCacheData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualF.Cached
open ThomsonNine.ActualF.Data ThomsonNine.CertificateMatrices ThomsonNine.ActualHermite.CoefficientData ThomsonNine.FixedInterval
theorem fields (j : Fin 756) : Fields j := by
  have h : ∀ b : Fin 63, ∀ i : Fin 12, Fields ⟨b.val*12+i.val,by omega⟩ := by
    intro b
    fin_cases b
    · exact fields00
    · exact fields01
    · exact fields02
    · exact fields03
    · exact fields04
    · exact fields05
    · exact fields06
    · exact fields07
    · exact fields08
    · exact fields09
    · exact fields10
    · exact fields11
    · exact fields12
    · exact fields13
    · exact fields14
    · exact fields15
    · exact fields16
    · exact fields17
    · exact fields18
    · exact fields19
    · exact fields20
    · exact fields21
    · exact fields22
    · exact fields23
    · exact fields24
    · exact fields25
    · exact fields26
    · exact fields27
    · exact fields28
    · exact fields29
    · exact fields30
    · exact fields31
    · exact fields32
    · exact fields33
    · exact fields34
    · exact fields35
    · exact fields36
    · exact fields37
    · exact fields38
    · exact fields39
    · exact fields40
    · exact fields41
    · exact fields42
    · exact fields43
    · exact fields44
    · exact fields45
    · exact fields46
    · exact fields47
    · exact fields48
    · exact fields49
    · exact fields50
    · exact fields51
    · exact fields52
    · exact fields53
    · exact fields54
    · exact fields55
    · exact fields56
    · exact fields57
    · exact fields58
    · exact fields59
    · exact fields60
    · exact fields61
    · exact fields62

  have hh := h ⟨j.val/12,by omega⟩ ⟨j.val%12,by omega⟩
  have heq : (⟨j.val/12*12+j.val%12,by omega⟩ : Fin 756)=j := by
    apply Fin.ext
    change j.val/12*12+j.val%12=j.val
    omega
  simpa only [heq] using hh
theorem input_mem (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) (j : Fin 756) :
    Mem unitScale (input j) (coefficient X j) := by
  have hh := coefficient_mem X hX j
  change ((input j).lo : ℝ)≤(unitScale : ℝ)*coefficient X j ∧
    (unitScale : ℝ)*coefficient X j≤(input j).hi
  rw [← (fields j).1,← (fields j).2]
  exact hh
end ThomsonNine.ActualF.Cached

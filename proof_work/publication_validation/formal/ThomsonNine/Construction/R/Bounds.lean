import ThomsonNine.Construction.R.BoundsData

-- Isolated source: R.Bounds
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualR.Certified
open ThomsonNine.ActualR.Data ThomsonNine.ActualHermite.CoefficientData ThomsonNine.FixedInterval
theorem bounds (j : Fin 807) : Bound j := by
  by_cases hj : j.val<804
  · have h : ∀ b : Fin 67, ∀ i : Fin 12, Bound ⟨b.val*12+i.val,by omega⟩ := by
      intro b
      fin_cases b
      · exact bound00
      · exact bound01
      · exact bound02
      · exact bound03
      · exact bound04
      · exact bound05
      · exact bound06
      · exact bound07
      · exact bound08
      · exact bound09
      · exact bound10
      · exact bound11
      · exact bound12
      · exact bound13
      · exact bound14
      · exact bound15
      · exact bound16
      · exact bound17
      · exact bound18
      · exact bound19
      · exact bound20
      · exact bound21
      · exact bound22
      · exact bound23
      · exact bound24
      · exact bound25
      · exact bound26
      · exact bound27
      · exact bound28
      · exact bound29
      · exact bound30
      · exact bound31
      · exact bound32
      · exact bound33
      · exact bound34
      · exact bound35
      · exact bound36
      · exact bound37
      · exact bound38
      · exact bound39
      · exact bound40
      · exact bound41
      · exact bound42
      · exact bound43
      · exact bound44
      · exact bound45
      · exact bound46
      · exact bound47
      · exact bound48
      · exact bound49
      · exact bound50
      · exact bound51
      · exact bound52
      · exact bound53
      · exact bound54
      · exact bound55
      · exact bound56
      · exact bound57
      · exact bound58
      · exact bound59
      · exact bound60
      · exact bound61
      · exact bound62
      · exact bound63
      · exact bound64
      · exact bound65
      · exact bound66

    have hh := h ⟨j.val/12,by omega⟩ ⟨j.val%12,by omega⟩
    have heq : (⟨j.val/12*12+j.val%12,by omega⟩ : Fin 807)=j := by
      apply Fin.ext
      change j.val/12*12+j.val%12=j.val
      omega
    simpa only [heq] using hh
  · have hh := bound67 ⟨j.val-804,by omega⟩
    have heq : (⟨804+(j.val-804),by omega⟩ : Fin 807)=j := by
      apply Fin.ext
      change 804+(j.val-804)=j.val
      omega
    simpa only [heq] using hh
theorem indexed_mem (j : Fin 807) :
    (AAAGroupedData.sourceInterval (termIndex j)).mem (coefficient j) :=
  mem_to_rat (coefficient_mem j) unitScale_pos (bounds j).1 (bounds j).2
theorem family_mem (t : LocalSparseHessianAAA.TermIndex) :
    (AAAGroupedData.sourceInterval t).mem (family t) := by
  have h := indexed_mem (sourceIndex t)
  rw [termIndex_sourceIndex] at h
  exact h
end ThomsonNine.ActualR.Certified

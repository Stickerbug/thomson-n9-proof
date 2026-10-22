import R.CollectionMatchData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualR.Collection
open ThomsonNine.ActualR.Data
theorem all_matches (j : Fin 807) : Matches j := by
  by_cases hj : j.val<804
  · have h : ∀ b : Fin 67, ∀ i : Fin 12, Matches ⟨b.val*12+i.val,by omega⟩ := by
      intro b
      fin_cases b
      · exact matches00
      · exact matches01
      · exact matches02
      · exact matches03
      · exact matches04
      · exact matches05
      · exact matches06
      · exact matches07
      · exact matches08
      · exact matches09
      · exact matches10
      · exact matches11
      · exact matches12
      · exact matches13
      · exact matches14
      · exact matches15
      · exact matches16
      · exact matches17
      · exact matches18
      · exact matches19
      · exact matches20
      · exact matches21
      · exact matches22
      · exact matches23
      · exact matches24
      · exact matches25
      · exact matches26
      · exact matches27
      · exact matches28
      · exact matches29
      · exact matches30
      · exact matches31
      · exact matches32
      · exact matches33
      · exact matches34
      · exact matches35
      · exact matches36
      · exact matches37
      · exact matches38
      · exact matches39
      · exact matches40
      · exact matches41
      · exact matches42
      · exact matches43
      · exact matches44
      · exact matches45
      · exact matches46
      · exact matches47
      · exact matches48
      · exact matches49
      · exact matches50
      · exact matches51
      · exact matches52
      · exact matches53
      · exact matches54
      · exact matches55
      · exact matches56
      · exact matches57
      · exact matches58
      · exact matches59
      · exact matches60
      · exact matches61
      · exact matches62
      · exact matches63
      · exact matches64
      · exact matches65
      · exact matches66

    have hh := h ⟨j.val/12,by omega⟩ ⟨j.val%12,by omega⟩
    have he : (⟨j.val/12*12+j.val%12,by omega⟩ : Fin 807)=j := by
      apply Fin.ext
      change j.val/12*12+j.val%12=j.val
      omega
    simpa only [he] using hh
  · have hh := matches67 ⟨j.val-804,by omega⟩
    have he : (⟨804+(j.val-804),by omega⟩ : Fin 807)=j := by
      apply Fin.ext
      change 804+(j.val-804)=j.val
      omega
    simpa only [he] using hh
theorem group_exponent (j : Fin 807) (n : ℕ) (hn : n∈groups j) : sourceExponent n=Data.sourceExponent j := by
  have h := of_decide_eq_true ((List.all_eq_true.mp (all_matches j)) n hn)
  funext a
  fin_cases a
  · exact h.1
  · exact h.2.1
  · exact h.2.2
end ThomsonNine.ActualR.Collection

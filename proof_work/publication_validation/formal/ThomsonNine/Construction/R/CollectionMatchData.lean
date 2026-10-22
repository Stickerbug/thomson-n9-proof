import ThomsonNine.Construction.R.Collection

-- Isolated source: R.CollectionMatchData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualR.Collection
open ThomsonNine.ActualR.Data
def Matches (j : Fin 807) : Prop := (groups j).all (fun n =>
  decide (sourceExponent n 0=Data.sourceExponent j 0 ∧ sourceExponent n 1=Data.sourceExponent j 1 ∧ sourceExponent n 2=Data.sourceExponent j 2))=true
theorem matches00 : ∀ j : Fin 12, Matches ⟨0+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches01 : ∀ j : Fin 12, Matches ⟨12+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches02 : ∀ j : Fin 12, Matches ⟨24+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches03 : ∀ j : Fin 12, Matches ⟨36+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches04 : ∀ j : Fin 12, Matches ⟨48+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches05 : ∀ j : Fin 12, Matches ⟨60+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches06 : ∀ j : Fin 12, Matches ⟨72+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches07 : ∀ j : Fin 12, Matches ⟨84+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches08 : ∀ j : Fin 12, Matches ⟨96+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches09 : ∀ j : Fin 12, Matches ⟨108+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches10 : ∀ j : Fin 12, Matches ⟨120+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches11 : ∀ j : Fin 12, Matches ⟨132+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches12 : ∀ j : Fin 12, Matches ⟨144+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches13 : ∀ j : Fin 12, Matches ⟨156+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches14 : ∀ j : Fin 12, Matches ⟨168+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches15 : ∀ j : Fin 12, Matches ⟨180+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches16 : ∀ j : Fin 12, Matches ⟨192+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches17 : ∀ j : Fin 12, Matches ⟨204+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches18 : ∀ j : Fin 12, Matches ⟨216+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches19 : ∀ j : Fin 12, Matches ⟨228+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches20 : ∀ j : Fin 12, Matches ⟨240+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches21 : ∀ j : Fin 12, Matches ⟨252+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches22 : ∀ j : Fin 12, Matches ⟨264+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches23 : ∀ j : Fin 12, Matches ⟨276+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches24 : ∀ j : Fin 12, Matches ⟨288+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches25 : ∀ j : Fin 12, Matches ⟨300+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches26 : ∀ j : Fin 12, Matches ⟨312+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches27 : ∀ j : Fin 12, Matches ⟨324+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches28 : ∀ j : Fin 12, Matches ⟨336+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches29 : ∀ j : Fin 12, Matches ⟨348+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches30 : ∀ j : Fin 12, Matches ⟨360+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches31 : ∀ j : Fin 12, Matches ⟨372+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches32 : ∀ j : Fin 12, Matches ⟨384+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches33 : ∀ j : Fin 12, Matches ⟨396+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches34 : ∀ j : Fin 12, Matches ⟨408+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches35 : ∀ j : Fin 12, Matches ⟨420+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches36 : ∀ j : Fin 12, Matches ⟨432+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches37 : ∀ j : Fin 12, Matches ⟨444+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches38 : ∀ j : Fin 12, Matches ⟨456+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches39 : ∀ j : Fin 12, Matches ⟨468+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches40 : ∀ j : Fin 12, Matches ⟨480+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches41 : ∀ j : Fin 12, Matches ⟨492+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches42 : ∀ j : Fin 12, Matches ⟨504+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches43 : ∀ j : Fin 12, Matches ⟨516+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches44 : ∀ j : Fin 12, Matches ⟨528+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches45 : ∀ j : Fin 12, Matches ⟨540+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches46 : ∀ j : Fin 12, Matches ⟨552+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches47 : ∀ j : Fin 12, Matches ⟨564+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches48 : ∀ j : Fin 12, Matches ⟨576+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches49 : ∀ j : Fin 12, Matches ⟨588+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches50 : ∀ j : Fin 12, Matches ⟨600+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches51 : ∀ j : Fin 12, Matches ⟨612+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches52 : ∀ j : Fin 12, Matches ⟨624+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches53 : ∀ j : Fin 12, Matches ⟨636+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches54 : ∀ j : Fin 12, Matches ⟨648+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches55 : ∀ j : Fin 12, Matches ⟨660+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches56 : ∀ j : Fin 12, Matches ⟨672+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches57 : ∀ j : Fin 12, Matches ⟨684+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches58 : ∀ j : Fin 12, Matches ⟨696+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches59 : ∀ j : Fin 12, Matches ⟨708+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches60 : ∀ j : Fin 12, Matches ⟨720+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches61 : ∀ j : Fin 12, Matches ⟨732+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches62 : ∀ j : Fin 12, Matches ⟨744+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches63 : ∀ j : Fin 12, Matches ⟨756+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches64 : ∀ j : Fin 12, Matches ⟨768+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches65 : ∀ j : Fin 12, Matches ⟨780+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches66 : ∀ j : Fin 12, Matches ⟨792+j.val,by omega⟩ := by unfold Matches; decide +kernel
theorem matches67 : ∀ j : Fin 3, Matches ⟨804+j.val,by omega⟩ := by unfold Matches; decide +kernel
end ThomsonNine.ActualR.Collection

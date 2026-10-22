import ThomsonNine.Construction.R.Model

-- Isolated source: R.BoundsData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualR.Certified
open ThomsonNine.ActualR.Data ThomsonNine.ActualHermite.CoefficientData ThomsonNine.FixedInterval
def Bound (j : Fin 807) : Prop :=
  (unitScale : ℚ)*(AAAGroupedData.sourceInterval (termIndex j)).lo≤(input j).lo ∧
    ((input j).hi : ℚ)≤(unitScale : ℚ)*(AAAGroupedData.sourceInterval (termIndex j)).hi
theorem bound00 : ∀ j : Fin 12, Bound ⟨0+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound01 : ∀ j : Fin 12, Bound ⟨12+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound02 : ∀ j : Fin 12, Bound ⟨24+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound03 : ∀ j : Fin 12, Bound ⟨36+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound04 : ∀ j : Fin 12, Bound ⟨48+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound05 : ∀ j : Fin 12, Bound ⟨60+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound06 : ∀ j : Fin 12, Bound ⟨72+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound07 : ∀ j : Fin 12, Bound ⟨84+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound08 : ∀ j : Fin 12, Bound ⟨96+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound09 : ∀ j : Fin 12, Bound ⟨108+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound10 : ∀ j : Fin 12, Bound ⟨120+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound11 : ∀ j : Fin 12, Bound ⟨132+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound12 : ∀ j : Fin 12, Bound ⟨144+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound13 : ∀ j : Fin 12, Bound ⟨156+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound14 : ∀ j : Fin 12, Bound ⟨168+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound15 : ∀ j : Fin 12, Bound ⟨180+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound16 : ∀ j : Fin 12, Bound ⟨192+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound17 : ∀ j : Fin 12, Bound ⟨204+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound18 : ∀ j : Fin 12, Bound ⟨216+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound19 : ∀ j : Fin 12, Bound ⟨228+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound20 : ∀ j : Fin 12, Bound ⟨240+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound21 : ∀ j : Fin 12, Bound ⟨252+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound22 : ∀ j : Fin 12, Bound ⟨264+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound23 : ∀ j : Fin 12, Bound ⟨276+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound24 : ∀ j : Fin 12, Bound ⟨288+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound25 : ∀ j : Fin 12, Bound ⟨300+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound26 : ∀ j : Fin 12, Bound ⟨312+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound27 : ∀ j : Fin 12, Bound ⟨324+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound28 : ∀ j : Fin 12, Bound ⟨336+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound29 : ∀ j : Fin 12, Bound ⟨348+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound30 : ∀ j : Fin 12, Bound ⟨360+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound31 : ∀ j : Fin 12, Bound ⟨372+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound32 : ∀ j : Fin 12, Bound ⟨384+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound33 : ∀ j : Fin 12, Bound ⟨396+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound34 : ∀ j : Fin 12, Bound ⟨408+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound35 : ∀ j : Fin 12, Bound ⟨420+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound36 : ∀ j : Fin 12, Bound ⟨432+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound37 : ∀ j : Fin 12, Bound ⟨444+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound38 : ∀ j : Fin 12, Bound ⟨456+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound39 : ∀ j : Fin 12, Bound ⟨468+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound40 : ∀ j : Fin 12, Bound ⟨480+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound41 : ∀ j : Fin 12, Bound ⟨492+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound42 : ∀ j : Fin 12, Bound ⟨504+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound43 : ∀ j : Fin 12, Bound ⟨516+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound44 : ∀ j : Fin 12, Bound ⟨528+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound45 : ∀ j : Fin 12, Bound ⟨540+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound46 : ∀ j : Fin 12, Bound ⟨552+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound47 : ∀ j : Fin 12, Bound ⟨564+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound48 : ∀ j : Fin 12, Bound ⟨576+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound49 : ∀ j : Fin 12, Bound ⟨588+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound50 : ∀ j : Fin 12, Bound ⟨600+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound51 : ∀ j : Fin 12, Bound ⟨612+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound52 : ∀ j : Fin 12, Bound ⟨624+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound53 : ∀ j : Fin 12, Bound ⟨636+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound54 : ∀ j : Fin 12, Bound ⟨648+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound55 : ∀ j : Fin 12, Bound ⟨660+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound56 : ∀ j : Fin 12, Bound ⟨672+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound57 : ∀ j : Fin 12, Bound ⟨684+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound58 : ∀ j : Fin 12, Bound ⟨696+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound59 : ∀ j : Fin 12, Bound ⟨708+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound60 : ∀ j : Fin 12, Bound ⟨720+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound61 : ∀ j : Fin 12, Bound ⟨732+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound62 : ∀ j : Fin 12, Bound ⟨744+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound63 : ∀ j : Fin 12, Bound ⟨756+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound64 : ∀ j : Fin 12, Bound ⟨768+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound65 : ∀ j : Fin 12, Bound ⟨780+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound66 : ∀ j : Fin 12, Bound ⟨792+j.val,by omega⟩ := by unfold Bound; decide +kernel
theorem bound67 : ∀ j : Fin 3, Bound ⟨804+j.val,by omega⟩ := by unfold Bound; decide +kernel
end ThomsonNine.ActualR.Certified

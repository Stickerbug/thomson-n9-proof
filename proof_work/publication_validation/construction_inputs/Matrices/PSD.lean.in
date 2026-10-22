import ThomsonNine.Construction.Matrices.Model
import ThomsonNine.Construction.PSDBatches.Block00
import ThomsonNine.Construction.PSDBatches.Block01
import ThomsonNine.Construction.PSDBatches.Block02
import ThomsonNine.Construction.PSDBatches.Block03
import ThomsonNine.Construction.PSDBatches.Block04
import ThomsonNine.Construction.PSDBatches.Block05
import ThomsonNine.Construction.PSDBatches.Block06
import ThomsonNine.Construction.PSDBatches.Block07
import ThomsonNine.Construction.PSDBatches.Block08
import ThomsonNine.Construction.PSDBatches.Block09

-- Isolated source: Matrices.PSD
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CertificateMatrices
open ThomsonNine.FixedInterval ThomsonNine.FixedInterval.Schur ThomsonNine.ActualHermite.CoefficientData
theorem block_bounds00 : ∀ i j : Fin 9,
    Contains (ContactPSD.Block00Stage00.matrix i j) (reducedInput 0 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd00 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 0).PosSemidef :=
  ContactPSD.Block00Stage00.certificate (reduced X 0) (reduced_symmetric X 0)
    (fun i j => mem_contains (block_bounds00 i j) (reduced_mem X hX 0 i j))
theorem block_bounds01 : ∀ i j : Fin 9,
    Contains (ContactPSD.Block01Stage00.matrix i j) (reducedInput 1 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd01 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 1).PosSemidef :=
  ContactPSD.Block01Stage00.certificate (reduced X 1) (reduced_symmetric X 1)
    (fun i j => mem_contains (block_bounds01 i j) (reduced_mem X hX 1 i j))
theorem block_bounds02 : ∀ i j : Fin 7,
    Contains (ContactPSD.Block02Stage00.matrix i j) (reducedInput 2 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd02 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 2).PosSemidef :=
  ContactPSD.Block02Stage00.certificate (reduced X 2) (reduced_symmetric X 2)
    (fun i j => mem_contains (block_bounds02 i j) (reduced_mem X hX 2 i j))
theorem block_bounds03 : ∀ i j : Fin 7,
    Contains (ContactPSD.Block03Stage00.matrix i j) (reducedInput 3 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd03 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 3).PosSemidef :=
  ContactPSD.Block03Stage00.certificate (reduced X 3) (reduced_symmetric X 3)
    (fun i j => mem_contains (block_bounds03 i j) (reduced_mem X hX 3 i j))
theorem block_bounds04 : ∀ i j : Fin 5,
    Contains (ContactPSD.Block04Stage00.matrix i j) (reducedInput 4 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd04 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 4).PosSemidef :=
  ContactPSD.Block04Stage00.certificate (reduced X 4) (reduced_symmetric X 4)
    (fun i j => mem_contains (block_bounds04 i j) (reduced_mem X hX 4 i j))
theorem block_bounds05 : ∀ i j : Fin 5,
    Contains (ContactPSD.Block05Stage00.matrix i j) (reducedInput 5 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd05 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 5).PosSemidef :=
  ContactPSD.Block05Stage00.certificate (reduced X 5) (reduced_symmetric X 5)
    (fun i j => mem_contains (block_bounds05 i j) (reduced_mem X hX 5 i j))
theorem block_bounds06 : ∀ i j : Fin 3,
    Contains (ContactPSD.Block06Stage00.matrix i j) (reducedInput 6 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd06 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 6).PosSemidef :=
  ContactPSD.Block06Stage00.certificate (reduced X 6) (reduced_symmetric X 6)
    (fun i j => mem_contains (block_bounds06 i j) (reduced_mem X hX 6 i j))
theorem block_bounds07 : ∀ i j : Fin 3,
    Contains (ContactPSD.Block07Stage00.matrix i j) (reducedInput 7 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd07 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 7).PosSemidef :=
  ContactPSD.Block07Stage00.certificate (reduced X 7) (reduced_symmetric X 7)
    (fun i j => mem_contains (block_bounds07 i j) (reduced_mem X hX 7 i j))
theorem block_bounds08 : ∀ i j : Fin 1,
    Contains (ContactPSD.Block08Stage00.matrix i j) (reducedInput 8 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd08 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 8).PosSemidef :=
  ContactPSD.Block08Stage00.certificate (reduced X 8) (reduced_symmetric X 8)
    (fun i j => mem_contains (block_bounds08 i j) (reduced_mem X hX 8 i j))
theorem block_bounds09 : ∀ i j : Fin 1,
    Contains (ContactPSD.Block09Stage00.matrix i j) (reducedInput 9 i j) := by
  unfold Contains
  decide +kernel
theorem block_psd09 (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) :
    (reduced X 9).PosSemidef :=
  ContactPSD.Block09Stage00.certificate (reduced X 9) (reduced_symmetric X 9)
    (fun i j => mem_contains (block_bounds09 i j) (reduced_mem X hX 9 i j))
theorem reduced_psd (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) (k : Fin 11) :
    (reduced X k).PosSemidef := by
  fin_cases k
  · exact block_psd00 X hX
  · exact block_psd01 X hX
  · exact block_psd02 X hX
  · exact block_psd03 X hX
  · exact block_psd04 X hX
  · exact block_psd05 X hX
  · exact block_psd06 X hX
  · exact block_psd07 X hX
  · exact block_psd08 X hX
  · exact block_psd09 X hX
  · apply empty_psdSound unitScale (fun _ _ => zero) (reduced X 10) (reduced_symmetric X 10)
    intro i j
    exact Fin.elim0 i
theorem all_A_psd (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) (k : Fin 11) :
    (A X k).PosSemidef := A_psd X k (reduced_psd X hX k)
end ThomsonNine.CertificateMatrices

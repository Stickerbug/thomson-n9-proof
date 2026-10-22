import ThomsonNine.Construction.Contact.Model
import ThomsonNine.Construction.Kernel.FastBasis

-- Isolated source: Contact.FastModel
noncomputable section
namespace ThomsonNine.ActualContact.Fast
open ThomsonNine.ContactJet
open ThomsonNine.ActualHermite.CoefficientData
open ThomsonNine.ActualKernel

def nodeTag : Fin 7 → Fin 14 := ![0,9,7,2,4,10,3]
theorem rowCode_nonzero : ∀ row : Fin 45, ∀ j : Fin 3, QCache.pointCode (QCache.rowPoint row) j≠0 := by decide +kernel
theorem rowCode_tag : ∀ row : Fin 45, ∀ j : Fin 3, nodeTag (QCache.pointCode (QCache.rowPoint row) j)=(rows row).nodes j := by decide +kernel
theorem coordinate_tag (c : Fin 7) (hc : c≠0) : FeatureCache.coordinateValue c=ActualHermite.node (nodeTag c) := by
  fin_cases c <;> simp_all [FeatureCache.coordinateValue,nodeTag]
theorem rowPoint_eq (row : Fin 45) : QCache.point (QCache.rowPoint row)=point row := by
  funext j
  change FeatureCache.coordinateValue (QCache.pointCode (QCache.rowPoint row) j)=ActualHermite.node ((rows row).nodes j)
  rw [coordinate_tag _ (rowCode_nonzero row j),rowCode_tag]
def diagonalCode (c : Fin 7) : Fin 19 := ⟨if c=0 then 18 else 11+c.val,by split_ifs <;> omega⟩
def diagonalPoint (row : Fin 45) (j : Fin 3) : Fin 19 := diagonalCode (QCache.pointCode (QCache.rowPoint row) j)
theorem diagonalPoint_eq (row : Fin 45) (j : Fin 3) :
    QCache.point (diagonalPoint row j)=diagonal ((rows row).nodes j) := by
  have h (c : Fin 7) (hc : c≠0) : QCache.point (diagonalCode c)=diagonal (nodeTag c) := by
    funext a
    fin_cases c <;> fin_cases a <;> simp_all [QCache.point,QCache.pointCode,diagonalCode,FeatureCache.coordinateValue,nodeTag,diagonal]
  rw [diagonalPoint,h _ (rowCode_nonzero row j),rowCode_tag]
theorem onesPoint_eq : QCache.point 18=ones := by
  funext j
  fin_cases j <;> rfl

def cachedJet (p : Fin 19) (h : Fin 190) : Input :=
  FastBasis.basis p (indices h).block (indices h).left (indices h).right
theorem cachedJet_mem (p : Fin 19) (h : Fin 190) : Mem unitScale (cachedJet p h) (jet (QCache.point p) h) :=
  FastBasis.basis_mem p _ _ _
theorem row_jet_mem (row : Fin 45) (h : Fin 190) :
    Mem unitScale (cachedJet (QCache.rowPoint row) h) (jet (point row) h) := by
  simpa only [rowPoint_eq] using cachedJet_mem (QCache.rowPoint row) h
theorem diagonal_jet_mem (row : Fin 45) (j : Fin 3) (h : Fin 190) :
    Mem unitScale (cachedJet (diagonalPoint row j) h) (jet (diagonal ((rows row).nodes j)) h) := by
  simpa only [diagonalPoint_eq] using cachedJet_mem (diagonalPoint row j) h
theorem ones_jet_mem (h : Fin 190) :
    Mem unitScale (cachedJet 18 h) (jet ones h) := by simpa only [onesPoint_eq] using cachedJet_mem 18 h

def inputGradientRow (row : Fin 45) (h : Fin 190) (j : Fin 3) : B :=
  FixedInterval.add (FixedInterval.add
    (FixedInterval.scale 7 ((cachedJet (QCache.rowPoint row) h).gradient j))
    ((cachedJet (diagonalPoint row j) h).gradient 1))
    ((cachedJet (diagonalPoint row j) h).gradient 2)
theorem gradientRow_mem (row : Fin 45) (h : Fin 190) (j : Fin 3) :
    FixedInterval.Mem unitScale (inputGradientRow row h j) (gradientRow row h j) :=
  FixedInterval.mem_add (FixedInterval.mem_add
    (FixedInterval.mem_scale ((row_jet_mem row h).2 j) 7)
    ((diagonal_jet_mem row j h).2 1)) ((diagonal_jet_mem row j h).2 2)
def inputValueRow (row : Fin 45) (h : Fin 190) : B :=
  FixedInterval.add (FixedInterval.add (FixedInterval.scale 7 (cachedJet (QCache.rowPoint row) h).value)
    (FixedInterval.Schur.sumFin (fun j : Fin 3 => (cachedJet (diagonalPoint row j) h).value)))
    (FixedInterval.mul unitScale (FixedInterval.rational unitScale (1/8)) (cachedJet 18 h).value)
theorem valueRow_mem (row : Fin 45) (h : Fin 190) :
    FixedInterval.Mem unitScale (inputValueRow row h) (valueRow row h) := by
  have hc : FixedInterval.Mem unitScale (FixedInterval.rational unitScale (1/8)) (1/8 : ℝ) := by
    simpa using FixedInterval.rational_mem unitScale (1/8)
  exact FixedInterval.mem_add (FixedInterval.mem_add
    (FixedInterval.mem_scale (row_jet_mem row h).1 7)
    (FixedInterval.Schur.sumFin_mem _ _ (fun j => (diagonal_jet_mem row j h).1)))
    (FixedInterval.mem_mul unitScale_pos hc (ones_jet_mem h).1)
def inputM (row : Fin 45) (h : Fin 190) : B :=
  if (rows row).kind=0 then inputValueRow row h
  else if (rows row).kind=1 then inputGradientRow row h (rows row).axis
  else FixedInterval.Schur.subtract
    (FixedInterval.mul unitScale (inputGramGradient (inputPoint row) 0) (inputGradientRow row h (rows row).axis))
    (FixedInterval.mul unitScale (inputGramGradient (inputPoint row) (rows row).axis) (inputGradientRow row h 0))
theorem M_mem (row : Fin 45) (h : Fin 190) : FixedInterval.Mem unitScale (inputM row h) (M row h) := by
  unfold inputM M
  split_ifs
  · exact valueRow_mem row h
  · exact gradientRow_mem row h _
  · exact FixedInterval.Schur.mem_subtract
      (FixedInterval.mem_mul unitScale_pos (gramGradient_mem (point_mem row) _) (gradientRow_mem row h _))
      (FixedInterval.mem_mul unitScale_pos (gramGradient_mem (point_mem row) _) (gradientRow_mem row h _))
end ThomsonNine.ActualContact.Fast

import ThomsonNine.Construction.Contact.Metadata
import ThomsonNine.Construction.Algebra.IntervalSchur
import ThomsonNine.ActualHermiteArray
import Mathlib.Tactic.FinCases

-- Isolated source: Contact.Model
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet
open ThomsonNine.ActualHermite
open ThomsonNine.ActualHermite.CoefficientData
open ThomsonNine.ActualKernel.BasisJet
open scoped BigOperators

abbrev B := FixedInterval.Bounds
def point (row : Fin 45) : Point := fun j => node ((rows row).nodes j)
def inputPoint (row : Fin 45) : Fin 3 → B := fun j => inputNode ((rows row).nodes j)
theorem point_mem (row : Fin 45) (j : Fin 3) : FixedInterval.Mem unitScale (inputPoint row j) (point row j) := inputNode_mem _
def diagonal (a : Fin 14) : Point := ![1,node a,node a]
def inputDiagonal (a : Fin 14) : Fin 3 → B := ![FixedInterval.constant unitScale 1,inputNode a,inputNode a]
theorem diagonal_mem (a : Fin 14) (j : Fin 3) : FixedInterval.Mem unitScale (inputDiagonal a j) (diagonal a j) := by
  fin_cases j
  · simpa [inputDiagonal,diagonal] using FixedInterval.mem_constant unitScale 1
  · exact inputNode_mem a
  · exact inputNode_mem a
def ones : Point := fun _ => 1
def inputOnes : Fin 3 → B := fun _ => FixedInterval.constant unitScale 1
theorem ones_mem (j : Fin 3) : FixedInterval.Mem unitScale (inputOnes j) (ones j) := by
  simpa [inputOnes,ones] using FixedInterval.mem_constant unitScale 1

def jet (x : Point) (h : Fin 190) : Jet :=
  basisJet x (indices h).block (indices h).left (indices h).right
def inputJet (x : Fin 3 → B) (h : Fin 190) : Input :=
  inputBasisJet x (indices h).block (indices h).left (indices h).right
theorem jet_mem {x : Point} {I : Fin 3 → B} (hx : ∀ j, FixedInterval.Mem unitScale (I j) (x j)) (h : Fin 190) :
    Mem unitScale (inputJet I h) (jet x h) := basis_mem hx _ _ _

def gramGradient (x : Point) (j : Fin 3) : ℝ := 2*(x (j+1)*x (j+2)-x j)
def inputGramGradient (x : Fin 3 → B) (j : Fin 3) : B :=
  FixedInterval.mul unitScale (FixedInterval.constant unitScale 2)
    (FixedInterval.Schur.subtract (FixedInterval.mul unitScale (x (j+1)) (x (j+2))) (x j))
theorem gramGradient_mem {x : Point} {I : Fin 3 → B} (hx : ∀ j, FixedInterval.Mem unitScale (I j) (x j)) (j : Fin 3) :
    FixedInterval.Mem unitScale (inputGramGradient I j) (gramGradient x j) :=
  FixedInterval.mem_mul unitScale_pos (by simpa using FixedInterval.mem_constant unitScale 2)
    (FixedInterval.Schur.mem_subtract (FixedInterval.mem_mul unitScale_pos (hx _) (hx _)) (hx _))

def gradientRow (row : Fin 45) (h : Fin 190) (j : Fin 3) : ℝ :=
  7*(jet (point row) h).gradient j+
    (jet (diagonal ((rows row).nodes j)) h).gradient 1+
    (jet (diagonal ((rows row).nodes j)) h).gradient 2
def inputGradientRow (row : Fin 45) (h : Fin 190) (j : Fin 3) : B :=
  FixedInterval.add (FixedInterval.add
    (FixedInterval.scale 7 ((inputJet (inputPoint row) h).gradient j))
    ((inputJet (inputDiagonal ((rows row).nodes j)) h).gradient 1))
    ((inputJet (inputDiagonal ((rows row).nodes j)) h).gradient 2)
theorem gradientRow_mem (row : Fin 45) (h : Fin 190) (j : Fin 3) :
    FixedInterval.Mem unitScale (inputGradientRow row h j) (gradientRow row h j) := by
  exact FixedInterval.mem_add (FixedInterval.mem_add
    (FixedInterval.mem_scale ((jet_mem (point_mem row) h).2 j) 7)
    ((jet_mem (diagonal_mem _) h).2 1)) ((jet_mem (diagonal_mem _) h).2 2)

def valueRow (row : Fin 45) (h : Fin 190) : ℝ :=
  7*(jet (point row) h).value+
    (∑ j : Fin 3, (jet (diagonal ((rows row).nodes j)) h).value)+(1/8)*(jet ones h).value
def inputValueRow (row : Fin 45) (h : Fin 190) : B :=
  FixedInterval.add (FixedInterval.add (FixedInterval.scale 7 (inputJet (inputPoint row) h).value)
    (FixedInterval.Schur.sumFin (fun j : Fin 3 => (inputJet (inputDiagonal ((rows row).nodes j)) h).value)))
    (FixedInterval.mul unitScale (FixedInterval.rational unitScale (1/8)) (inputJet inputOnes h).value)
theorem valueRow_mem (row : Fin 45) (h : Fin 190) :
    FixedInterval.Mem unitScale (inputValueRow row h) (valueRow row h) := by
  have hc : FixedInterval.Mem unitScale (FixedInterval.rational unitScale (1/8)) (1/8 : ℝ) := by
    simpa using FixedInterval.rational_mem unitScale (1/8)
  exact FixedInterval.mem_add (FixedInterval.mem_add
    (FixedInterval.mem_scale (jet_mem (point_mem row) h).1 7)
    (FixedInterval.Schur.sumFin_mem _ _ (fun j => (jet_mem (diagonal_mem _) h).1)))
    (FixedInterval.mem_mul unitScale_pos hc (jet_mem ones_mem h).1)

def M (row : Fin 45) (h : Fin 190) : ℝ :=
  if (rows row).kind=0 then valueRow row h
  else if (rows row).kind=1 then gradientRow row h (rows row).axis
  else gramGradient (point row) 0*gradientRow row h (rows row).axis-
    gramGradient (point row) (rows row).axis*gradientRow row h 0
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

def energyNodes : Fin 6 → Fin 14 := ![9,7,2,4,10,3]
def energyWeights : Fin 6 → ℕ := ![6,3,6,3,12,6]
def E : ℝ := ∑ j : Fin 6, (energyWeights j : ℝ)*value (energyNodes j)
def inputE : B := FixedInterval.Schur.sumFin (fun j => FixedInterval.scale (energyWeights j) (inputValue (energyNodes j)))
theorem E_mem : FixedInterval.Mem unitScale inputE E :=
  FixedInterval.Schur.sumFin_mem _ _ (fun j => FixedInterval.mem_scale (inputValue_mem _) _)
def rhs (row : Fin 45) : ℝ :=
  if (rows row).kind=0 then (∑ j : Fin 3, value ((rows row).nodes j))-(1/12)*E
  else if (rows row).kind=1 then (value ((rows row).nodes (rows row).axis))^3
  else gramGradient (point row) 0*(value ((rows row).nodes (rows row).axis))^3-
    gramGradient (point row) (rows row).axis*(value ((rows row).nodes 0))^3
def inputRhs (row : Fin 45) : B :=
  if (rows row).kind=0 then FixedInterval.Schur.subtract
    (FixedInterval.Schur.sumFin (fun j : Fin 3 => inputValue ((rows row).nodes j)))
    (FixedInterval.mul unitScale (FixedInterval.rational unitScale (1/12)) inputE)
  else if (rows row).kind=1 then Coefficients.fixedCube ((rows row).nodes (rows row).axis)
  else FixedInterval.Schur.subtract
    (FixedInterval.mul unitScale (inputGramGradient (inputPoint row) 0) (Coefficients.fixedCube ((rows row).nodes (rows row).axis)))
    (FixedInterval.mul unitScale (inputGramGradient (inputPoint row) (rows row).axis) (Coefficients.fixedCube ((rows row).nodes 0)))
theorem rhs_mem (row : Fin 45) : FixedInterval.Mem unitScale (inputRhs row) (rhs row) := by
  unfold inputRhs rhs
  split_ifs
  · exact FixedInterval.Schur.mem_subtract
      (FixedInterval.Schur.sumFin_mem _ _ (fun j => inputValue_mem _))
      (FixedInterval.mem_mul unitScale_pos (by simpa using FixedInterval.rational_mem unitScale (1/12)) E_mem)
  · exact Coefficients.cube_mem _
  · exact FixedInterval.Schur.mem_subtract
      (FixedInterval.mem_mul unitScale_pos (gramGradient_mem (point_mem row) _) (Coefficients.cube_mem _))
      (FixedInterval.mem_mul unitScale_pos (gramGradient_mem (point_mem row) _) (Coefficients.cube_mem _))
end ThomsonNine.ActualContact

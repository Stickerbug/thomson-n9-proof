import F.TargetData

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualF
open ThomsonNine.ActualF.Data
open ThomsonNine.CertificateMatrices
open ThomsonNine.ActualHermite.CoefficientData
open ThomsonNine.FixedInterval
open scoped BigOperators

def leftIndex (s : Source) : Fin (ambientDim s.block) :=
  ⟨s.left%ambientDim s.block,Nat.mod_lt _ (ambient_positive s.block)⟩
def rightIndex (s : Source) : Fin (ambientDim s.block) :=
  ⟨s.right%ambientDim s.block,Nat.mod_lt _ (ambient_positive s.block)⟩
def sourceCoefficient (X : Fin 190 → ℝ) (s : Source) : ℝ :=
  ((Data.term s).2 : ℝ)*A X s.block (leftIndex s) (rightIndex s)
def sourceInput (s : Source) : Bounds :=
  scaleInteger (Data.term s).2 (Ainput s.block (leftIndex s) (rightIndex s))
theorem source_mem (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) (s : Source) :
    Mem unitScale (sourceInput s) (sourceCoefficient X s) :=
  mem_scaleInteger _ (A_mem X hX _ _ _)

def coefficient (X : Fin 190 → ℝ) (j : Fin 756) : ℝ :=
  (1/6)*((groups j).map (fun n => sourceCoefficient X (decode n))).sum
def coefficientInput (j : Fin 756) : Bounds :=
  mul unitScale (rational unitScale (1/6)) (FixedInterval.sum ((groups j).map (fun n => sourceInput (decode n))))
theorem coefficient_mem (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) (j : Fin 756) :
    Mem unitScale (coefficientInput j) (coefficient X j) := by
  have hc : Mem unitScale (rational unitScale (1/6)) (1/6 : ℝ) := by
    simpa using rational_mem unitScale (1/6)
  exact mem_mul unitScale_pos hc (FixedInterval.sum_mem
    (fun n => sourceInput (decode n)) (fun n => sourceCoefficient X (decode n)) (groups j)
    (fun n _ => source_mem X hX (decode n)))

def F (X : Fin 190 → ℝ) (u v t : ℝ) : ℝ :=
  ∑ j : Fin 756, coefficient X j*QPolynomial.monomial (support j) u v t
def rawEval (X : Fin 190 → ℝ) (u v t : ℝ) : ℝ :=
  (1/6)*((List.range count).map (fun n => sourceCoefficient X (decode n)*
    QPolynomial.monomial (exponent (decode n)) u v t)).sum

end ThomsonNine.ActualF

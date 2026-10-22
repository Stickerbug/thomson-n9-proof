import R.Data
import ThomsonNine.AAACenter

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualR
open ThomsonNine.ActualR.Data
open ThomsonNine.CertificateMatrices
open ThomsonNine.ActualHermite.CoefficientData
open ThomsonNine.FixedInterval
open scoped BigOperators

abbrev X := ActualContact.SystemCertificate.X
def diagonalCoefficient (n : Fin 28) : ℝ :=
  ((diagonalIndices n).map (ActualF.coefficient X)).sum
theorem diagonal_mem (n : Fin 28) : Mem unitScale (diagonalInput n) (diagonalCoefficient n) := by
  have hh := FixedInterval.sum_mem ActualF.Cached.input (ActualF.coefficient X) (diagonalIndices n)
    (fun j _ => ActualF.Cached.input_mem X actual_X_mem j)
  change ((diagonalInput n).lo : ℝ)≤(unitScale : ℝ)*diagonalCoefficient n ∧
    (unitScale : ℝ)*diagonalCoefficient n≤(diagonalInput n).hi
  rw [(diagonalInput_fields n).1,(diagonalInput_fields n).2]
  exact hh
def hPart (j : Fin 807) : ℝ := match pureDegree j with
  | none => 0
  | some n => (multiplicity j : ℝ)*ActualHermite.H.coeff n
def hInput (j : Fin 807) : Bounds := match pureDegree j with
  | none => zero
  | some n => scale (multiplicity j) (ActualHermite.Cached.input n)
theorem h_mem (j : Fin 807) : Mem unitScale (hInput j) (hPart j) := by
  unfold hInput hPart
  cases pureDegree j with
  | none => exact mem_zero unitScale
  | some n => exact mem_scale (ActualHermite.Cached.input_mem n) _
def fPart (j : Fin 807) : ℝ := match Findex j with
  | none => 0
  | some n => ActualF.coefficient X n
def fInput (j : Fin 807) : Bounds := match Findex j with
  | none => zero
  | some n => ActualF.Cached.input n
theorem f_mem (j : Fin 807) : Mem unitScale (fInput j) (fPart j) := by
  unfold fInput fPart
  cases Findex j with
  | none => exact mem_zero unitScale
  | some n => exact ActualF.Cached.input_mem X actual_X_mem n
def dPart (j : Fin 807) : ℝ := match pureDegree j with
  | none => 0
  | some n => (multiplicity j : ℝ)*diagonalCoefficient n
def dInput (j : Fin 807) : Bounds := match pureDegree j with
  | none => zero
  | some n => scale (multiplicity j) (diagonalInput n)
theorem d_mem (j : Fin 807) : Mem unitScale (dInput j) (dPart j) := by
  unfold dInput dPart
  cases pureDegree j with
  | none => exact mem_zero unitScale
  | some n => exact mem_scale (diagonal_mem n) _
def cPart (j : Fin 807) : ℝ := if j=0 then ActualF.Constants.c X else 0
def cInput (j : Fin 807) : Bounds := if j=0 then ActualF.Constants.cInput else zero
theorem c_mem (j : Fin 807) : Mem unitScale (cInput j) (cPart j) := by
  unfold cInput cPart
  split_ifs
  · exact ActualF.Constants.c_mem X actual_X_mem
  · exact mem_zero unitScale
def coefficient (j : Fin 807) : ℝ := hPart j-7*fPart j-dPart j-cPart j
def input (j : Fin 807) : Bounds := Schur.subtract
  (Schur.subtract (Schur.subtract (hInput j) (scale 7 (fInput j))) (dInput j)) (cInput j)
theorem coefficient_mem (j : Fin 807) : Mem unitScale (input j) (coefficient j) :=
  Schur.mem_subtract (Schur.mem_subtract (Schur.mem_subtract (h_mem j) (mem_scale (f_mem j) 7)) (d_mem j)) (c_mem j)
def family (t : LocalSparseHessianAAA.TermIndex) : ℝ := coefficient (sourceIndex t)
end ThomsonNine.ActualR

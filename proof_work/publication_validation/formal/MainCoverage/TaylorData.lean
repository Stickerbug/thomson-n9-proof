import Algebra.FiniteRationalPolynomial
import Algebra.ExactComposition
import Global.CoulombReduction
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.MainCoulombTaylor
open Polynomial ThomsonNine.RationalListPolynomial
open scoped BigOperators
def coefficients : List ℚ := [(1/1 : ℚ),(1/2 : ℚ),(3/8 : ℚ),(5/16 : ℚ),(35/128 : ℚ),(63/256 : ℚ),(231/1024 : ℚ),(429/2048 : ℚ),(6435/32768 : ℚ),(12155/65536 : ℚ),(46189/262144 : ℚ)]
def remainderCoefficients : List ℚ := [(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(88179/262144 : ℚ),(323323/2097152 : ℚ),(223839/2097152 : ℚ),(692835/8388608 : ℚ),(2263261/33554432 : ℚ),(61108047/1073741824 : ℚ),(13180167/268435456 : ℚ),(46235189/1073741824 : ℚ),(328513185/8589934592 : ℚ),(2357994639/68719476736 : ℚ),(2133423721/68719476736 : ℚ)]
def T : ℝ[X] := realPolynomial coefficients
theorem length_coefficients : coefficients.length=11 := by decide +kernel
theorem coefficients_nonnegative : ∀ c∈coefficients, 0≤c := by decide +kernel
theorem remainder_nonnegative : ∀ c∈remainderCoefficients, 0≤c := by decide +kernel
theorem remainder_fields : ExactPolynomial.sub [1]
    (ExactPolynomial.mul [1,-1] (ExactPolynomial.pow coefficients 2))=remainderCoefficients := by decide +kernel
end ThomsonNine.MainCoulombTaylor

import Moment.Function
import Moment.Factor00Row00
import Moment.Factor00Row01
import Moment.Factor00Row02
import Moment.Factor00Row03
import Moment.Factor00Row04
import Moment.Factor00Row05
import Moment.Factor00Row06
import Moment.Factor00Row07
import Moment.Factor00Row08
import Moment.Factor00Row09
import Moment.Factor00Row10
import Moment.Factor01Row00
import Moment.Factor01Row01
import Moment.Factor01Row02
import Moment.Factor01Row03
import Moment.Factor01Row04
import Moment.Factor01Row05
import Moment.Factor01Row06
import Moment.Factor01Row07
import Moment.Factor01Row08
import Moment.Factor01Row09
import Moment.Factor02Row00
import Moment.Factor02Row01
import Moment.Factor02Row02
import Moment.Factor02Row03
import Moment.Factor02Row04
import Moment.Factor02Row05
import Moment.Factor02Row06
import Moment.Factor02Row07
import Moment.Factor02Row08
import Moment.Factor03Row00
import Moment.Factor03Row01
import Moment.Factor03Row02
import Moment.Factor03Row03
import Moment.Factor03Row04
import Moment.Factor03Row05
import Moment.Factor03Row06
import Moment.Factor03Row07
import Moment.Factor04Row00
import Moment.Factor04Row01
import Moment.Factor04Row02
import Moment.Factor04Row03
import Moment.Factor04Row04
import Moment.Factor04Row05
import Moment.Factor04Row06
import Moment.Factor05Row00
import Moment.Factor05Row01
import Moment.Factor05Row02
import Moment.Factor05Row03
import Moment.Factor05Row04
import Moment.Factor05Row05
import Moment.Factor06Row00
import Moment.Factor06Row01
import Moment.Factor06Row02
import Moment.Factor06Row03
import Moment.Factor06Row04
import Moment.Factor07Row00
import Moment.Factor07Row01
import Moment.Factor07Row02
import Moment.Factor07Row03
import Moment.Factor08Row00
import Moment.Factor08Row01
import Moment.Factor08Row02
import Moment.Factor09Row00
import Moment.Factor09Row01
import Moment.Factor10Row00
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.CertificateMatrices ThomsonNine.ExactPolynomial ThomsonNine.RationalListPolynomial
theorem all_factor_zero (k : Fin 11) (a b : Fin (ambientDim k)) : sub (moment k (ambientIndex k a) (ambientIndex k b)) (factor k (ambientIndex k a) (ambientIndex k b))=[] := by
  fin_cases k
  · fin_cases a
    · exact factor_row_00_00 b
    · exact factor_row_00_01 b
    · exact factor_row_00_02 b
    · exact factor_row_00_03 b
    · exact factor_row_00_04 b
    · exact factor_row_00_05 b
    · exact factor_row_00_06 b
    · exact factor_row_00_07 b
    · exact factor_row_00_08 b
    · exact factor_row_00_09 b
    · exact factor_row_00_10 b
  · fin_cases a
    · exact factor_row_01_00 b
    · exact factor_row_01_01 b
    · exact factor_row_01_02 b
    · exact factor_row_01_03 b
    · exact factor_row_01_04 b
    · exact factor_row_01_05 b
    · exact factor_row_01_06 b
    · exact factor_row_01_07 b
    · exact factor_row_01_08 b
    · exact factor_row_01_09 b
  · fin_cases a
    · exact factor_row_02_00 b
    · exact factor_row_02_01 b
    · exact factor_row_02_02 b
    · exact factor_row_02_03 b
    · exact factor_row_02_04 b
    · exact factor_row_02_05 b
    · exact factor_row_02_06 b
    · exact factor_row_02_07 b
    · exact factor_row_02_08 b
  · fin_cases a
    · exact factor_row_03_00 b
    · exact factor_row_03_01 b
    · exact factor_row_03_02 b
    · exact factor_row_03_03 b
    · exact factor_row_03_04 b
    · exact factor_row_03_05 b
    · exact factor_row_03_06 b
    · exact factor_row_03_07 b
  · fin_cases a
    · exact factor_row_04_00 b
    · exact factor_row_04_01 b
    · exact factor_row_04_02 b
    · exact factor_row_04_03 b
    · exact factor_row_04_04 b
    · exact factor_row_04_05 b
    · exact factor_row_04_06 b
  · fin_cases a
    · exact factor_row_05_00 b
    · exact factor_row_05_01 b
    · exact factor_row_05_02 b
    · exact factor_row_05_03 b
    · exact factor_row_05_04 b
    · exact factor_row_05_05 b
  · fin_cases a
    · exact factor_row_06_00 b
    · exact factor_row_06_01 b
    · exact factor_row_06_02 b
    · exact factor_row_06_03 b
    · exact factor_row_06_04 b
  · fin_cases a
    · exact factor_row_07_00 b
    · exact factor_row_07_01 b
    · exact factor_row_07_02 b
    · exact factor_row_07_03 b
  · fin_cases a
    · exact factor_row_08_00 b
    · exact factor_row_08_01 b
    · exact factor_row_08_02 b
  · fin_cases a
    · exact factor_row_09_00 b
    · exact factor_row_09_01 b
  · fin_cases a
    · exact factor_row_10_00 b
theorem factor_identity : FactorIdentity := by
  intro k a b
  have h := congrArg realPolynomial (all_factor_zero k a b)
  rw [sub_sound] at h
  exact sub_eq_zero.mp h

theorem constructed_weightedF_zero (X : Fin 190 → ℝ) : weightedF X RefinedRadius.radius=0 :=
  weightedF_zero factor_identity X
theorem constructed_weightedF_stationary (X : Fin 190 → ℝ) : HasDerivAt (weightedF X) 0 RefinedRadius.radius :=
  weightedF_stationary factor_identity X
end ThomsonNine.CandidateMoment

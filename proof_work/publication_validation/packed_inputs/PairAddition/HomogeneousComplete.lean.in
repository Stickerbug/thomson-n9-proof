import PairAddition.HStep00
import PairAddition.HStep01
import PairAddition.HStep02
import PairAddition.HStep03
import PairAddition.HStep04
import PairAddition.HStep05
import PairAddition.HStep06
import PairAddition.HStep07
import PairAddition.HStep08
import PairAddition.HStep09
import PairAddition.HStep10
import PairAddition.HStep11
import PairAddition.HStep12
import PairAddition.HStep13
import PairAddition.HStep14
import PairAddition.HStep15
import PairAddition.HStep16
import PairAddition.HStep17
import PairAddition.HStep18
import PairAddition.HStep19
import PairAddition.HStep20
import PairAddition.HStep21
import PairAddition.HStep22
import PairAddition.HStep23
import PairAddition.HStep24
import PairAddition.HStep25
import PairAddition.HStep26
import PairAddition.HStep27
import PairAddition.HStep28
import PairAddition.HStep29
import PairAddition.HStep30
import PairAddition.HStep31
import PairAddition.HStep32
import PairAddition.HStep33
import PairAddition.HStep34
import PairAddition.HStep35
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
theorem homogeneous_step (m : Fin 36) (w d : ℝ) :
    homogeneous ⟨m.val+2,by omega⟩ w d=2*w*homogeneous ⟨m.val+1,by omega⟩ w d-d*homogeneous ⟨m.val,by omega⟩ w d := by
  fin_cases m
  · exact homogeneous_step00 w d
  · exact homogeneous_step01 w d
  · exact homogeneous_step02 w d
  · exact homogeneous_step03 w d
  · exact homogeneous_step04 w d
  · exact homogeneous_step05 w d
  · exact homogeneous_step06 w d
  · exact homogeneous_step07 w d
  · exact homogeneous_step08 w d
  · exact homogeneous_step09 w d
  · exact homogeneous_step10 w d
  · exact homogeneous_step11 w d
  · exact homogeneous_step12 w d
  · exact homogeneous_step13 w d
  · exact homogeneous_step14 w d
  · exact homogeneous_step15 w d
  · exact homogeneous_step16 w d
  · exact homogeneous_step17 w d
  · exact homogeneous_step18 w d
  · exact homogeneous_step19 w d
  · exact homogeneous_step20 w d
  · exact homogeneous_step21 w d
  · exact homogeneous_step22 w d
  · exact homogeneous_step23 w d
  · exact homogeneous_step24 w d
  · exact homogeneous_step25 w d
  · exact homogeneous_step26 w d
  · exact homogeneous_step27 w d
  · exact homogeneous_step28 w d
  · exact homogeneous_step29 w d
  · exact homogeneous_step30 w d
  · exact homogeneous_step31 w d
  · exact homogeneous_step32 w d
  · exact homogeneous_step33 w d
  · exact homogeneous_step34 w d
  · exact homogeneous_step35 w d
theorem homogeneous_eq_Q3 : ∀ n : ℕ, ∀ hn : n<38, ∀ u v t : ℝ,
    homogeneous ⟨n,hn⟩ (t-u*v) ((1-u^2)*(1-v^2))=ThreePoint.Q3 n u v t := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn u v t
    cases n with
    | zero => norm_num [homogeneous,qCoefficient,Fin.sum_univ_succ,ThreePoint.Q3]
    | succ n =>
      cases n with
      | zero => norm_num [homogeneous,qCoefficient,Fin.sum_univ_succ,ThreePoint.Q3]
      | succ k =>
        have h := homogeneous_step ⟨k,by omega⟩ (t-u*v) ((1-u^2)*(1-v^2))
        change homogeneous ⟨k+2,by omega⟩ (t-u*v) ((1-u^2)*(1-v^2))=_ at h
        rw [h,ih (k+1) (by omega) (by omega) u v t,ih k (by omega) (by omega) u v t]
        rfl
end ThomsonNine.PairAddition

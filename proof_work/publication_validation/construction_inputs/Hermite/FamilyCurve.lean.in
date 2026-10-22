import ThomsonNine.Construction.Hermite.CoulombDerivative
import ThomsonNine.Construction.Contact.Weights
import Mathlib.Analysis.Calculus.Deriv.Polynomial

-- Isolated source: Hermite.FamilyCurve
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ActualHermite ThomsonNine.RationalListPolynomial Polynomial Filter
open scoped BigOperators Topology

def pairIndex (j : Fin 6) : Fin 7 := ⟨j.val+1,by omega⟩
def pairCurve (j : Fin 6) (r : ℝ) : ℝ := CandidateMoment.realNodes r (pairIndex j)
def pairVelocity (j : Fin 6) : ℝ :=
  (realPolynomial (CandidateMoment.nodes (pairIndex j))).derivative.eval RefinedRadius.radius

theorem pairCurve_closed (j : Fin 6) (r : ℝ) : pairCurve j r=
    (![1-3*r^2/2,2*r^2-1,r^2/2-1,-1/2,r/2,-r] : Fin 6 → ℝ) j := by
  fin_cases j <;> norm_num [pairCurve,pairIndex,CandidateMoment.realNodes,CandidateMoment.nodes,realPolynomial,ListPolynomial.polynomial] <;> ring

theorem pairCurve_at (j : Fin 6) : pairCurve j RefinedRadius.radius=node (energyNodes j) := by
  fin_cases j <;> rw [pairCurve_closed] <;> norm_num [energyNodes,node]

def pairEnergy (r : ℝ) : ℝ := ∑ j : Fin 6, (energyWeights j : ℝ)*coulomb (pairCurve j r)

theorem pairEnergy_eq_family (r : ℝ) (hr : 0<r) (hr1 : r<1) : pairEnergy r=familyEnergy r := by
  have ha : coulomb (1-3*r^2/2)=(Real.sqrt 3*r)⁻¹ := by
    rw [coulomb,show 2-2*(1-3*r^2/2)=3*r^2 by ring,Real.sqrt_mul (by norm_num),Real.sqrt_sq (le_of_lt hr)]
  have hb : coulomb (2*r^2-1)=(2*Real.sqrt (1-r^2))⁻¹ := by
    have hs : Real.sqrt (4 : ℝ)=2 := by
      rw [show (4 : ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num)]
    rw [coulomb,show 2-2*(2*r^2-1)=4*(1-r^2) by ring,Real.sqrt_mul (by norm_num),hs]
  have hc : coulomb (r^2/2-1)=(Real.sqrt (4-r^2))⁻¹ := by
    rw [coulomb,show 2-2*(r^2/2-1)=4-r^2 by ring]
  have hd : coulomb (-1/2)=(Real.sqrt 3)⁻¹ := by norm_num [coulomb]
  have hf : coulomb (r/2)=(Real.sqrt (2-r))⁻¹ := by rw [coulomb,show 2-2*(r/2)=2-r by ring]
  have hg : coulomb (-r)=(Real.sqrt (2+2*r))⁻¹ := by simp [coulomb]
  simp only [pairEnergy,pairCurve_closed]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,energyWeights,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,Nat.cast_ofNat,add_zero]
  rw [ha,hb,hc,hd,hf,hg,Family.familyEnergy_alt hr hr1]
  ring

theorem pairCurve_derivative (j : Fin 6) : HasDerivAt (pairCurve j) (pairVelocity j) RefinedRadius.radius :=
  (realPolynomial (CandidateMoment.nodes (pairIndex j))).hasDerivAt _

theorem pair_energy_stationary :
    (∑ j : Fin 6, (energyWeights j : ℝ)*(value (energyNodes j))^3*pairVelocity j)=0 := by
  have hj (j : Fin 6) : HasDerivAt (fun r => (energyWeights j : ℝ)*coulomb (pairCurve j r))
      ((energyWeights j : ℝ)*(value (energyNodes j))^3*pairVelocity j) RefinedRadius.radius := by
    have hn := node_lt_one (energyNodes j)
    rw [← pairCurve_at j] at hn
    have h := ((coulomb_derivative _ hn).comp RefinedRadius.radius (pairCurve_derivative j)).const_mul (energyWeights j : ℝ)
    convert h using 1
    · rfl
    · rw [pairCurve_at]
      change (energyWeights j : ℝ)*(value (energyNodes j))^3*pairVelocity j=
        (energyWeights j : ℝ)*((value (energyNodes j))^3*pairVelocity j)
      ring
  have hsum := HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ => hj j)
  have he : pairEnergy =ᶠ[𝓝 RefinedRadius.radius] familyEnergy := by
    filter_upwards [Ioo_mem_nhds RefinedRadius.radius_pos RefinedRadius.radius_lt_one] with r hr
    exact pairEnergy_eq_family r hr.1 hr.2
  have hz := RefinedRadius.radius_stationary.congr_of_eventuallyEq he
  exact hsum.unique hz
end ThomsonNine.ActualContact

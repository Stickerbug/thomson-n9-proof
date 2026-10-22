import MainCoverage.RootData
import MainCoverage.TreeSound
import Global.CoulombReduction
import LocalAll.Nonnegative

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PackedMain

theorem cores_in_source : ∀ id : Fin 12, ∀ a : Fin 3,
    (ActualLocal.sourceBox id a).lo≤(localCores id.val a).1 ∧
      (localCores id.val a).2≤(ActualLocal.sourceBox id a).hi := by decide +kernel

theorem actual_local_lower : LocalLower localCores
    (fun x => Semantics.gram (x 0) (x 1) (x 2)) ActualCoulombGlobal.residual := by
  intro id x hid hx hcore hG
  let j : Fin 12 := ⟨id,hid⟩
  have hp (a : Fin 3) : (ActualLocal.sourceBox j a).mem (x a) := by
    have hl : ((ActualLocal.sourceBox j a).lo : ℝ)≤((localCores id a).1 : ℝ) := by
      exact_mod_cast (cores_in_source j a).1
    have hr : ((localCores id a).2 : ℝ)≤((ActualLocal.sourceBox j a).hi : ℝ) := by
      exact_mod_cast (cores_in_source j a).2
    exact ⟨hl.trans (hcore a).1,(hcore a).2.trans hr⟩
  have hpoly := ActualLocal.all_twelve_residual_nonnegative j x hp hG
  have hminor := ActualCoulombGlobal.polynomial_residual_le x (fun a =>
    ⟨(hx a).1,((hx a).2.trans_lt (by norm_num : (14:ℝ)/25<1))⟩)
  exact hpoly.trans hminor
end ThomsonNine.PackedMain

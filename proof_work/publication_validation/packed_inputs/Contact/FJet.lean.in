import F.BasisModel
import Kernel.BasisAlong
import Contact.Model

noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet ThomsonNine.ActualKernel.BasisJet
open scoped BigOperators

theorem point_eta (y : Point) : ![y 0,y 1,y 2]=y := by
  funext i
  fin_cases i <;> rfl

def FJet (X : Fin 190 → ℝ) (x : Point) : Jet :=
  ContactJet.sum (List.finRange 190) (fun h => ContactJet.mul (constant (X h)) (jet x h))

theorem FJet_along (X : Fin 190 → ℝ) (x : Point) :
    AlongCorrect (fun y => ActualF.F X (y 0) (y 1) (y 2)) x (FJet X x) := by
  have h := along_sum (List.finRange 190)
    (fun h y => X h*basisFunction (indices h).block (indices h).left (indices h).right y)
    (fun h => ContactJet.mul (constant (X h)) (jet x h)) x
    (fun h _ => (along_constant (X h) x).mul (basis_along x _ _ _))
  have he : (fun y => ((List.finRange 190).map (fun h => X h*basisFunction (indices h).block (indices h).left (indices h).right y)).sum)=
      (fun y => ActualF.F X (y 0) (y 1) (y 2)) := by
    funext y
    rw [MonomialSymmetry.finRange_sum,ActualF.F_eq_contact_basis,point_eta]
  rw [he] at h
  exact h

theorem sum_jet_value {α : Type*} (l : List α) (f : α → Jet) :
    (ContactJet.sum l f).value=(l.map (fun i => (f i).value)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (f a).value+(ContactJet.sum l f).value=(f a).value+(l.map (fun i => (f i).value)).sum
    rw [ih]
theorem sum_jet_gradient {α : Type*} (l : List α) (f : α → Jet) (j : Fin 3) :
    (ContactJet.sum l f).gradient j=(l.map (fun i => (f i).gradient j)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (f a).gradient j+(ContactJet.sum l f).gradient j=(f a).gradient j+(l.map (fun i => (f i).gradient j)).sum
    rw [ih]
theorem FJet_value (X : Fin 190 → ℝ) (x : Point) :
    (FJet X x).value=∑ h : Fin 190, X h*(jet x h).value := by
  rw [FJet,sum_jet_value,MonomialSymmetry.finRange_sum]
  rfl
theorem FJet_gradient (X : Fin 190 → ℝ) (x : Point) (j : Fin 3) :
    (FJet X x).gradient j=∑ h : Fin 190, X h*(jet x h).gradient j := by
  rw [FJet,sum_jet_gradient,MonomialSymmetry.finRange_sum]
  simp only [ContactJet.mul,constant,zero_mul,zero_add]
end ThomsonNine.ActualContact

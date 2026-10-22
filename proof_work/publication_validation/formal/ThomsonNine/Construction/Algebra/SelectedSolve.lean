import ThomsonNine.Interval
import ThomsonNine.Construction.Algebra.SchurSolve

-- Isolated source: Algebra.SelectedSolve
noncomputable section
namespace ThomsonNine.SelectedSolve
open scoped BigOperators

def augment {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (seed : ι → ℝ) (columns : κ → ι) (delta : κ → ℝ) (h : ι) : ℝ :=
  seed h+∑ j, if columns j=h then delta j else 0

theorem augment_selected {ι κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (seed : ι → ℝ) (columns : κ → ι) (hinj : Function.Injective columns) (delta : κ → ℝ) (j : κ) :
    augment seed columns delta (columns j)=seed (columns j)+delta j := by
  simp [augment,hinj.eq_iff]

theorem augment_unselected {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (seed : ι → ℝ) (columns : κ → ι) (delta : κ → ℝ) (h : ι) (hn : ∀ j, columns j≠h) :
    augment seed columns delta h=seed h := by simp [augment,hn]

theorem sum_augment {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (row seed : ι → ℝ) (columns : κ → ι) (delta : κ → ℝ) :
    (∑ h, row h*augment seed columns delta h) =
      (∑ h, row h*seed h)+∑ j, row (columns j)*delta j := by
  simp only [augment,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_ite,mul_zero]
  simp

theorem selected_equations {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] (M : ρ → ι → ℝ) (seed : ι → ℝ) (columns : κ → ι)
    (delta : κ → ℝ) (rhs : ρ → ℝ)
    (h : ∀ row, (∑ j, M row (columns j)*delta j)=rhs row-∑ i, M row i*seed i) :
    ∀ row, (∑ i, M row i*augment seed columns delta i)=rhs row := by
  intro row
  rw [sum_augment,h]
  ring
end ThomsonNine.SelectedSolve

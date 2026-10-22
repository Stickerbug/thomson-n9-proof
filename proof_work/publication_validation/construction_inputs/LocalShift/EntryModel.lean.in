import ThomsonNine.Construction.LocalShift.Inputs
import ThomsonNine.Construction.AAA.Model

-- Isolated source: LocalShift.EntryModel
noncomputable section
namespace ThomsonNine.LocalShift
open ThomsonNine.Interval.SparsePolynomial ThomsonNine.LocalSparseHessianAAA
open ThomsonNine.ActualLocalAAA
attribute [local irreducible] entries

theorem eval_entries (c : TermIndex → ℝ) (x : Fin 3 → ℝ) :
    eval Entry.exp (fun E => c E.index) x entries=
      eval exponents c x GatheredBinding.allTerms := by
  rw [AAACollected.eval_eq_map_sum,AAACollected.eval_eq_map_sum]
  have he : (entries.map (fun E => c E.index*monomial E.exp x))=
      (entries.map Entry.index).map (fun t => c t*monomial (exponents t) x) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro E hE
    rw [entry_exp_eq E hE]
    rfl
  rw [he,entries_indices]

theorem entries_function_eq (localId : Fin 12) :
    (fun x => eval Entry.exp (fun E => family3 localId E.index) x entries)=
      translate (center localId) ActualR.residual := by
  funext x
  rw [eval_entries]
  exact family3_eval localId x
end ThomsonNine.LocalShift

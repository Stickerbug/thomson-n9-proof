import AAA.Data

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.ActualLocalAAA
open ThomsonNine.FixedInterval ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.Interval.SparsePolynomial.Grouped
open ThomsonNine.LocalSparseHessianAAA ThomsonNine.GatheredBinding
attribute [local irreducible] entries

def translated (t : TermIndex) : ℝ := gathered (exponents t) ActualR.family RefinedRadius.aaaCenter

theorem translated_mem (t : TermIndex) : (coefficientInterval t).mem (translated t) :=
  AAAFixedComplete.all_gathered ActualR.family RefinedRadius.aaaCenter
    ActualR.Certified.family_mem RefinedRadius.aaaCenter_mem t

theorem entry_exp_eq (E : Entry) (hE : E∈entries) : E.exp=exponents E.index := by
  have h := valid_of_mem E hE
  funext i
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem entry_input_mem (E : Entry) (hE : E∈entries) : Mem precision E.input (translated E.index) :=
  mem_of_rat (translated_mem E.index) precision_pos (valid_of_mem E hE).2.2.2.1 (valid_of_mem E hE).2.2.2.2

theorem powers_mem {x : ℝ} (hx : relativeDomain.mem x) (n : ℕ) : Mem precision (powers n) (x^n) := by
  have hd : Mem precision domain x := mem_of_rat hx precision_pos domain_bounds.1 domain_bounds.2
  by_cases hn : n<28
  · have he : powerCache ⟨n,hn⟩=power precision domain n :=
      congrArg₂ Bounds.mk (power_fields ⟨n,hn⟩).1 (power_fields ⟨n,hn⟩).2
    rw [powers,dif_pos hn,he]
    exact power_mem precision_pos hd n
  · rw [powers,dif_neg hn]
    exact power_mem precision_pos hd n

theorem eval_entries (x : Fin 3 → ℝ) :
    eval Entry.exp (fun E => translated E.index) x entries=
      eval exponents translated x GatheredBinding.allTerms := by
  rw [AAACollected.eval_eq_map_sum,AAACollected.eval_eq_map_sum]
  have he : (entries.map (fun E => translated E.index*monomial E.exp x))=
      (entries.map Entry.index).map (fun t => translated t*monomial (exponents t) x) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro E hE
    rw [entry_exp_eq E hE]
    rfl
  rw [he,entries_indices]

theorem entries_function_eq :
    (fun x => eval Entry.exp (fun E => translated E.index) x entries)=translate RefinedRadius.aaaCenter ActualR.residual := by
  funext x
  rw [eval_entries]
  exact (AAACollected.eval_shift_gathered ActualR.family RefinedRadius.aaaCenter x).symm.trans
    (congrFun ActualR.source_function_eq (fun j => RefinedRadius.aaaCenter j+x j))

def hessianComputed (i j : Fin 3) : Bounds :=
  FixedSparseHessian.hessianInput precision Entry.exp Entry.input (fun _ => powers) i j entries

theorem hessianComputed_mem (i j : Fin 3) (x : Fin 3 → ℝ)
    (hx : ∀ a, (relativeBox a).mem (x a)) :
    Mem precision (hessianComputed i j)
      (axisDeriv (axisDeriv ActualR.residual i) j (fun a => RefinedRadius.aaaCenter a+x a)) := by
  have h := FixedSparseHessian.hessianInput_mem precision_pos Entry.exp Entry.input
    (fun E => translated E.index) (fun _ => powers) x i j entries entry_input_mem
    (fun a n => powers_mem (hx a) n)
  rw [← axisDeriv_axisDeriv_eval,entries_function_eq,axisDeriv_axisDeriv_translate] at h
  exact h
end ThomsonNine.ActualLocalAAA

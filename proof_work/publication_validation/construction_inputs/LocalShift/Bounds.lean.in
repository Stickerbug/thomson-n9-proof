import ThomsonNine.Construction.LocalShift.Model

-- Isolated source: LocalShift.Bounds
noncomputable section
namespace ThomsonNine.LocalShift
open ThomsonNine.FixedInterval ThomsonNine.ListPolynomial
open ThomsonNine.LocalSparseHessianAAA
attribute [local irreducible] rows rowOf

def CacheFields (s : ℤ) (A : Bounds) (axis : Fin 3) (old new : TermIndex → Bounds) (row : Fin 155) : Prop :=
  (((rows axis row).map new).map Bounds.lo=(HornerShift.shiftedInput s A ((rows axis row).map old)).map Bounds.lo) ∧
  (((rows axis row).map new).map Bounds.hi=(HornerShift.shiftedInput s A ((rows axis row).map old)).map Bounds.hi)
instance (s : ℤ) (A : Bounds) (axis : Fin 3) (old new : TermIndex → Bounds) (row : Fin 155) :
    Decidable (CacheFields s A axis old new row) := by unfold CacheFields;infer_instance

theorem cached_step_mem {s : ℤ} (hs : 0<s) {A : Bounds} {a : ℝ} (ha : Mem s A a)
    (axis : Fin 3) (old new : TermIndex → Bounds) (c : TermIndex → ℝ)
    (hC : ∀ t, Mem s (old t) (c t)) (hFields : ∀ row, CacheFields s A axis old new row) (t : TermIndex) :
    Mem s (new t) (step axis a c t) := by
  have hin : List.Forall₂ (Mem s) ((rows axis (rowOf axis t)).map old) ((rows axis (rowOf axis t)).map c) :=
    rel_map (Mem s) (rows axis (rowOf axis t)) old c (fun k _ => hC k)
  have h := HornerShift.shifted_mem hs ha hin
  have he := HornerShift.bounds_list_ext ((rows axis (rowOf axis t)).map new)
    (HornerShift.shiftedInput s A ((rows axis (rowOf axis t)).map old))
    (hFields (rowOf axis t)).1 (hFields (rowOf axis t)).2
  rw [← he] at h
  have hc := mem_coeff h (exponents t axis)
  simp only [List.getElem?_map,(row_binding axis t).2,Option.map_some,Option.getD_some] at hc
  exact hc
end ThomsonNine.LocalShift

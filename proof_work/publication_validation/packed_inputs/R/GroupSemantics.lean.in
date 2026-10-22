import R.Collection
import Algebra.MonomialSymmetry

noncomputable section
namespace ThomsonNine.ActualR.Collection
open ThomsonNine.ActualR.Data
open ThomsonNine.MonomialSymmetry

theorem map_sum_neg {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map (fun a => -f a)).sum= -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring
theorem hGroup_eval (H : Fin 28 → ℝ) (F : Fin 756 → ℝ) (c : ℝ)
    (as : List (Fin 3)) (n : Option (Fin 28)) :
    ((as.flatMap (fun a => n.toList.map (hId a))).map (sourceCoefficient H F c)).sum =
      (as.length : ℝ)*(n.map H).getD 0 := by
  cases n with
  | none =>
    have he : as.flatMap (fun a : Fin 3 => ([] : List ℕ))=[] := by induction as <;> simp [*]
    simpa only [Option.toList_none,List.map_nil,Option.map_none,Option.getD_none,mul_zero,List.sum_nil] using congrArg (fun l : List ℕ => (l.map (sourceCoefficient H F c)).sum) he
  | some n =>
    simp only [Option.toList_some,Option.map_some,Option.getD_some,List.map_cons,List.map_nil]
    induction as with
    | nil => simp
    | cons a as ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,source_h,List.length_cons,Nat.cast_add,Nat.cast_one]
      rw [ih]
      ring
theorem dGroup_eval (H : Fin 28 → ℝ) (F : Fin 756 → ℝ) (c : ℝ)
    (as : List (Fin 3)) (n : Option (Fin 28)) :
    ((as.flatMap (fun a => n.toList.flatMap (fun n => (diagonalIndices n).map (dId a)))).map
      (sourceCoefficient H F c)).sum =
      -(as.length : ℝ)*(n.map (fun n => ((diagonalIndices n).map F).sum)).getD 0 := by
  cases n with
  | none =>
    have he : as.flatMap (fun a : Fin 3 => ([] : List ℕ))=[] := by induction as <;> simp [*]
    simpa only [Option.toList_none,List.flatMap_nil,List.map_nil,Option.map_none,Option.getD_none,mul_zero,List.sum_nil] using congrArg (fun l : List ℕ => (l.map (sourceCoefficient H F c)).sum) he
  | some n =>
    simp only [Option.toList_some,Option.map_some,Option.getD_some,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    induction as with
    | nil => simp
    | cons a as ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_map,Function.comp_def,source_d,map_sum_neg,List.length_cons,Nat.cast_add,Nat.cast_one]
      rw [ih]
      ring
theorem axes_length (j : Fin 807) : (axes j).length=Data.multiplicity j := by
  by_cases hj : j=0 <;> simp [axes,Data.multiplicity,hj]

def actualSourceCoefficient : ℕ → ℝ :=
  sourceCoefficient (fun n => ActualHermite.H.coeff n) (ActualF.coefficient X) (ActualF.Constants.c X)

theorem hGroup_actual (j : Fin 807) :
    ((hGroup j).map actualSourceCoefficient).sum=hPart j := by
  rw [hGroup]
  change (((axes j).flatMap (fun a => (pureDegree j).toList.map (hId a))).map actualSourceCoefficient).sum = _
  unfold actualSourceCoefficient
  rw [hGroup_eval,axes_length]
  cases hp : pureDegree j <;> simp [hPart,hp]
theorem dGroup_actual (j : Fin 807) :
    ((dGroup j).map actualSourceCoefficient).sum= -dPart j := by
  rw [dGroup]
  change (((axes j).flatMap (fun a => (pureDegree j).toList.flatMap (fun n => (diagonalIndices n).map (dId a)))).map actualSourceCoefficient).sum = _
  unfold actualSourceCoefficient
  rw [dGroup_eval,axes_length]
  cases hp : pureDegree j <;> simp [dPart,diagonalCoefficient,hp]
theorem fGroup_actual (j : Fin 807) :
    ((fGroup j).map actualSourceCoefficient).sum= -7*fPart j := by
  cases hf : Findex j <;> simp [fGroup,hf,fPart,actualSourceCoefficient,source_f]
theorem cGroup_actual (j : Fin 807) :
    ((cGroup j).map actualSourceCoefficient).sum= -cPart j := by
  by_cases hj : j=0 <;> simp [cGroup,cPart,hj,actualSourceCoefficient,source_c]
theorem group_actual (j : Fin 807) :
    ((groups j).map actualSourceCoefficient).sum=coefficient j := by
  simp only [groups,List.map_append,List.sum_append,hGroup_actual,fGroup_actual,dGroup_actual,cGroup_actual,coefficient]
  ring
end ThomsonNine.ActualR.Collection

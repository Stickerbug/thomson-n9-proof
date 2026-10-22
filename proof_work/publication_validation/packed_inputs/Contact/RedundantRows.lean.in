import Contact.GradientSymmetry
import Contact.RowBinding
import Contact.RowClasses
import Contact.PointVector
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ActualHermite
open scoped BigOperators
attribute [local irreducible] FJet contactGradient
theorem class23_00 (X : Fin 190 → ℝ) : classGradient X 0 1=classGradient X 0 2 := by
  have hp : point (valueRows 0)=![node 9,node 9,node 9] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat23 X (node 9) (node 9)
theorem class23_02 (X : Fin 190 → ℝ) : classGradient X 2 1=classGradient X 2 2 := by
  have hp : point (valueRows 2)=![node 9,node 2,node 2] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat23 X (node 9) (node 2)
theorem class23_03 (X : Fin 190 → ℝ) : classGradient X 3 1=classGradient X 3 2 := by
  have hp : point (valueRows 3)=![node 9,node 10,node 10] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat23 X (node 9) (node 10)
theorem class23_05 (X : Fin 190 → ℝ) : classGradient X 5 1=classGradient X 5 2 := by
  have hp : point (valueRows 5)=![node 7,node 10,node 10] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat23 X (node 7) (node 10)
theorem class23_06 (X : Fin 190 → ℝ) : classGradient X 6 1=classGradient X 6 2 := by
  have hp : point (valueRows 6)=![node 7,node 3,node 3] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat23 X (node 7) (node 3)
theorem class23_07 (X : Fin 190 → ℝ) : classGradient X 7 1=classGradient X 7 2 := by
  have hp : point (valueRows 7)=![node 2,node 10,node 10] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat23 X (node 2) (node 10)
theorem class23_09 (X : Fin 190 → ℝ) : classGradient X 9 1=classGradient X 9 2 := by
  have hp : point (valueRows 9)=![node 4,node 4,node 4] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat23 X (node 4) (node 4)
theorem class23_10 (X : Fin 190 → ℝ) : classGradient X 10 1=classGradient X 10 2 := by
  have hp : point (valueRows 10)=![node 4,node 10,node 10] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat23 X (node 4) (node 10)
theorem class12_00 (X : Fin 190 → ℝ) : classGradient X 0 0=classGradient X 0 1 := by
  have hp : point (valueRows 0)=![node 9,node 9,node 9] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat12 X (node 9) (node 9)
theorem class12_09 (X : Fin 190 → ℝ) : classGradient X 9 0=classGradient X 9 1 := by
  have hp : point (valueRows 9)=![node 4,node 4,node 4] := by rw [point_as_vector];rfl
  simpa only [classGradient,hp] using contactGradient_repeat12 X (node 4) (node 4)
attribute [local irreducible] classGradient
theorem matrix_redundant_01 (X : Fin 190 → ℝ) :
    (∑ h : Fin 190, M 1 h*X h)=(∑ h : Fin 190, M 2 h*X h) := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class12_00 X]
theorem rhs_redundant_01 : rhs 1=rhs 2 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_redundant_03 (X : Fin 190 → ℝ) :
    (∑ h : Fin 190, M 3 h*X h)=(∑ h : Fin 190, M 2 h*X h) := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class23_00 X]
theorem rhs_redundant_03 : rhs 3=rhs 2 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_redundant_11 (X : Fin 190 → ℝ) :
    (∑ h : Fin 190, M 11 h*X h)=(∑ h : Fin 190, M 10 h*X h) := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class23_02 X]
theorem rhs_redundant_11 : rhs 11=rhs 10 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_redundant_15 (X : Fin 190 → ℝ) :
    (∑ h : Fin 190, M 15 h*X h)=(∑ h : Fin 190, M 14 h*X h) := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class23_03 X]
theorem rhs_redundant_15 : rhs 15=rhs 14 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_redundant_23 (X : Fin 190 → ℝ) :
    (∑ h : Fin 190, M 23 h*X h)=(∑ h : Fin 190, M 22 h*X h) := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class23_05 X]
theorem rhs_redundant_23 : rhs 23=rhs 22 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_redundant_26 (X : Fin 190 → ℝ) :
    (∑ h : Fin 190, M 26 h*X h)=(∑ h : Fin 190, M 25 h*X h) := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class23_06 X]
  ring
theorem rhs_redundant_26 : rhs 26=rhs 25 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_redundant_29 (X : Fin 190 → ℝ) :
    (∑ h : Fin 190, M 29 h*X h)=(∑ h : Fin 190, M 28 h*X h) := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class23_07 X]
  ring
theorem rhs_redundant_29 : rhs 29=rhs 28 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_redundant_40 (X : Fin 190 → ℝ) :
    (∑ h : Fin 190, M 40 h*X h)=(∑ h : Fin 190, M 39 h*X h) := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class23_10 X]
theorem rhs_redundant_40 : rhs 40=rhs 39 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_zero_35 (X : Fin 190 → ℝ) : (∑ h : Fin 190, M 35 h*X h)=0 := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class12_09 X,class23_09 X] <;> ring
theorem rhs_zero_35 : rhs 35=0 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
theorem matrix_zero_36 (X : Fin 190 → ℝ) : (∑ h : Fin 190, M 36 h*X h)=0 := by
  simp only [row_sum,gradient_eq_class]
  norm_num [rowClass,rows,point,gramGradient,Fin.add_def]
  rw [class12_09 X,class23_09 X] <;> ring
theorem rhs_zero_36 : rhs 36=0 := by
  norm_num [rhs,rows,point,gramGradient,Fin.add_def] <;> ring_nf <;> simp
end ThomsonNine.ActualContact

import ThomsonNine.Construction.Contact.ValueBinding

-- Isolated source: Contact.CurveDerivative
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet
open scoped BigOperators
attribute [local irreducible] FJet

def contactGradient (X : Fin 190 → ℝ) (x : Point) (j : Fin 3) : ℝ :=
  7*(FJet X x).gradient j+(FJet X ![1,x j,x j]).gradient 1+(FJet X ![1,x j,x j]).gradient 2

theorem contactGradient_row (X : Fin 190 → ℝ) (row : Fin 45) (j : Fin 3) :
    contactGradient X (point row) j=∑ h : Fin 190, X h*gradientRow row h j := by
  have hp : (![1,(point row) j,(point row) j] : Point)=diagonal ((rows row).nodes j) := rfl
  have he := congrArg (FJet X) hp
  have hg := congrArg (fun J : Jet => 7*(FJet X (point row)).gradient j+J.gradient 1+J.gradient 2) he
  dsimp only [contactGradient]
  with_reducible exact hg.trans (gradientRow_sum X row j).symm

theorem polynomialContact_derivative (X : Fin 190 → ℝ) (x : Point)
    (curve : ℝ → Point) (velocity : Point) (s : ℝ) (hc : curve s=x)
    (hd : ∀ j, HasDerivAt (fun t => curve t j) (velocity j) s) :
    HasDerivAt (fun t => polynomialContact X (curve t))
      (∑ j : Fin 3, contactGradient X x j*velocity j) s := by
  have hmain := (FJet_along X x).2 curve velocity s hc hd
  have hdiag (j : Fin 3) : HasDerivAt (fun t => ActualF.F X 1 (curve t j) (curve t j))
      (((FJet X ![1,x j,x j]).gradient 1+(FJet X ![1,x j,x j]).gradient 2)*velocity j) s := by
    have hinput (i : Fin 3) : HasDerivAt (fun t => (![1,curve t j,curve t j] : Point) i)
        ((![0,velocity j,velocity j] : Point) i) s := by
      fin_cases i
      · exact hasDerivAt_const s 1
      · exact hd j
      · exact hd j
    have h := (FJet_along X ![1,x j,x j]).2 (fun t => ![1,curve t j,curve t j])
      ![0,velocity j,velocity j] s (by rw [hc]) hinput
    convert h using 1 <;>
      simp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.head_cons,Matrix.tail_cons,mul_zero,zero_add] <;> ring
  have hsum := HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ => hdiag j)
  have hp := ((hmain.const_mul 7).add hsum).add (hasDerivAt_const s ((1/8)*ActualF.F X 1 1 1))
  have he : (∑ j : Fin 3, contactGradient X x j*velocity j)=
      7*(∑ j : Fin 3, (FJet X x).gradient j*velocity j)+
      (∑ j : Fin 3, ((FJet X ![1,x j,x j]).gradient 1+(FJet X ![1,x j,x j]).gradient 2)*velocity j)+0 := by
    simp only [contactGradient,Finset.mul_sum,← Finset.sum_add_distrib,add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  convert hp using 1 <;> rfl
end ThomsonNine.ActualContact

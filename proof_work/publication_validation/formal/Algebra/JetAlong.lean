import Algebra.JetPolynomial

noncomputable section
namespace ThomsonNine.ContactJet
open scoped BigOperators

def AlongCorrect (f : Point → ℝ) (x : Point) (j : Jet) : Prop :=
  j.value=f x ∧ ∀ (curve : ℝ → Point) (velocity : Point) (s : ℝ), curve s=x →
    (∀ i, HasDerivAt (fun t => curve t i) (velocity i) s) →
    HasDerivAt (fun t => f (curve t)) (∑ i : Fin 3, j.gradient i*velocity i) s

theorem along_constant (a : ℝ) (x : Point) : AlongCorrect (fun _ => a) x (constant a) := by
  refine ⟨rfl,?_⟩
  intro curve velocity s hc hd
  simpa [constant] using hasDerivAt_const s a

theorem along_coordinate (x : Point) (i : Fin 3) : AlongCorrect (fun y => y i) x (coordinate x i) := by
  refine ⟨rfl,?_⟩
  intro curve velocity s hc hd
  simpa [coordinate] using hd i

theorem AlongCorrect.add {f g : Point → ℝ} {x : Point} {a b : Jet}
    (ha : AlongCorrect f x a) (hb : AlongCorrect g x b) :
    AlongCorrect (fun y => f y+g y) x (ContactJet.add a b) := by
  refine ⟨by change a.value+b.value=f x+g x;rw [ha.1,hb.1],?_⟩
  intro curve velocity s hc hd
  convert (ha.2 curve velocity s hc hd).add (hb.2 curve velocity s hc hd) using 1 <;>
    simp only [ContactJet.add,add_mul,Finset.sum_add_distrib]

theorem AlongCorrect.neg {f : Point → ℝ} {x : Point} {a : Jet}
    (ha : AlongCorrect f x a) : AlongCorrect (fun y => -f y) x (ContactJet.neg a) := by
  refine ⟨by change -a.value= -f x;rw [ha.1],?_⟩
  intro curve velocity s hc hd
  convert (ha.2 curve velocity s hc hd).neg using 1 <;>
    simp only [ContactJet.neg,neg_mul,Finset.sum_neg_distrib]

theorem AlongCorrect.mul {f g : Point → ℝ} {x : Point} {a b : Jet}
    (ha : AlongCorrect f x a) (hb : AlongCorrect g x b) :
    AlongCorrect (fun y => f y*g y) x (ContactJet.mul a b) := by
  refine ⟨by change a.value*b.value=f x*g x;rw [ha.1,hb.1],?_⟩
  intro curve velocity s hc hd
  have h := (ha.2 curve velocity s hc hd).mul (hb.2 curve velocity s hc hd)
  have he : (∑ i : Fin 3, (ContactJet.mul a b).gradient i*velocity i)=
      (∑ i : Fin 3, a.gradient i*velocity i)*g (curve s)+f (curve s)*(∑ i : Fin 3, b.gradient i*velocity i) := by
    rw [hc,← ha.1,← hb.1]
    simp only [ContactJet.mul,Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  convert h using 1

theorem along_sum {α : Type*} (l : List α) (f : α → Point → ℝ) (j : α → Jet) (x : Point)
    (h : ∀ i∈l, AlongCorrect (f i) x (j i)) :
    AlongCorrect (fun y => (l.map (fun i => f i y)).sum) x (sum l j) := by
  induction l with
  | nil => exact along_constant 0 x
  | cons i l ih => exact (h i (by simp)).add (ih (fun k hk => h k (by simp [hk])))

theorem along_horner {f : Point → ℝ} {x : Point} {a : Jet} (ha : AlongCorrect f x a) (l : List ℝ) :
    AlongCorrect (fun y => (ListPolynomial.polynomial l).eval (f y)) x (horner a l) := by
  induction l with
  | nil => simpa [horner,ListPolynomial.polynomial] using along_constant 0 x
  | cons b l ih =>
    simpa only [horner,ListPolynomial.polynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
      using (along_constant b x).add (ha.mul ih)

theorem AlongCorrect.subtract {f g : Point → ℝ} {x : Point} {a b : Jet}
    (ha : AlongCorrect f x a) (hb : AlongCorrect g x b) :
    AlongCorrect (fun y => f y-g y) x (subtract a b) := by
  simpa only [ContactJet.subtract,sub_eq_add_neg] using ha.add hb.neg
theorem along_q {fu fv ft : Point → ℝ} {x : Point} {u v t : Jet}
    (hu : AlongCorrect fu x u) (hv : AlongCorrect fv x v) (ht : AlongCorrect ft x t) (k : ℕ) :
    AlongCorrect (fun y => ThreePoint.Q3 k (fu y) (fv y) (ft y)) x (q u v t k) := by
  have both : ∀ k, AlongCorrect (fun y => ThreePoint.Q3 k (fu y) (fv y) (ft y)) x (q u v t k) ∧
      AlongCorrect (fun y => ThreePoint.Q3 (k+1) (fu y) (fv y) (ft y)) x (q u v t (k+1)) := by
    intro k
    induction k with
    | zero => exact ⟨along_constant 1 x,ht.subtract (hu.mul hv)⟩
    | succ k ih =>
      refine ⟨ih.2,?_⟩
      have h := (((along_constant 2 x).mul (ht.subtract (hu.mul hv))).mul ih.2).subtract
        ((((along_constant 1 x).subtract (hu.mul hu)).mul
          ((along_constant 1 x).subtract (hv.mul hv))).mul ih.1)
      simpa only [q,ThreePoint.Q3,pow_two] using h
  exact (both k).1

end ThomsonNine.ContactJet

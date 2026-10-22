import ThomsonNine.FixedIntervalSigned
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section
namespace ThomsonNine.ListPolynomial
open Polynomial
open ThomsonNine.FixedInterval

def zipAdd {α : Type*} (plus : α → α → α) : List α → List α → List α
  | [],m => m
  | l,[] => l
  | a::l,b::m => plus a b :: zipAdd plus l m

def multiply {α : Type*} (z : α) (plus times : α → α → α) : List α → List α → List α
  | [],_ => []
  | a::l,m => zipAdd plus (m.map (times a)) (z::multiply z plus times l m)

def polynomial : List ℝ → ℝ[X]
  | [] => 0
  | a::l => C a+X*polynomial l

lemma polynomial_zipAdd (l m : List ℝ) :
    polynomial (zipAdd (·+·) l m) = polynomial l+polynomial m := by
  induction l generalizing m with
  | nil => simp [zipAdd,polynomial]
  | cons a l ih =>
    cases m with
    | nil => simp [zipAdd,polynomial]
    | cons b m => simp [zipAdd,polynomial,ih]; ring

lemma polynomial_map_mul (a : ℝ) (l : List ℝ) :
    polynomial (l.map (fun b => a*b)) = C a*polynomial l := by
  induction l with
  | nil => simp [polynomial]
  | cons b l ih => simp [polynomial,ih]; ring

 theorem polynomial_multiply (l m : List ℝ) :
    polynomial (multiply 0 (·+·) (·*·) l m) = polynomial l*polynomial m := by
  induction l with
  | nil => simp [multiply,polynomial]
  | cons a l ih => simp [multiply,polynomial_zipAdd,polynomial_map_mul,polynomial,ih]; ring

 theorem polynomial_coeff (l : List ℝ) (n : ℕ) :
    (polynomial l).coeff n = (l[n]?).getD 0 := by
  induction l generalizing n with
  | nil => simp [polynomial]
  | cons a l ih =>
    cases n with
    | zero => simp [polynomial]
    | succ n => simp [polynomial,coeff_X_mul,ih]

lemma rel_zipAdd {α β : Type*} (R : α → β → Prop)
    (plus : α → α → α) (plus' : β → β → β)
    (h : ∀ {a b c d}, R a b → R c d → R (plus a c) (plus' b d))
    {l : List α} {l' : List β} {m : List α} {m' : List β}
    (hl : List.Forall₂ R l l') (hm : List.Forall₂ R m m') :
    List.Forall₂ R (zipAdd plus l m) (zipAdd plus' l' m') := by
  induction hl generalizing m m' with
  | nil => simpa [zipAdd] using hm
  | cons hab htail ih =>
    cases hm with
    | nil => simpa [zipAdd] using List.Forall₂.cons hab htail
    | cons hcd hrest => exact List.Forall₂.cons (h hab hcd) (ih hrest)

lemma mem_map_mul {s : ℤ} (hs : 0 < s) {I : Bounds} {a : ℝ}
    (ha : Mem s I a) {l : List Bounds} {l' : List ℝ} (hl : List.Forall₂ (Mem s) l l') :
    List.Forall₂ (Mem s) (l.map (mul s I)) (l'.map (fun b => a*b)) := by
  induction hl with
  | nil => exact List.Forall₂.nil
  | cons hb htail ih => exact List.Forall₂.cons (mem_mul hs ha hb) ih

 theorem mem_multiply {s : ℤ} (hs : 0 < s)
    {l m : List Bounds} {l' m' : List ℝ}
    (hl : List.Forall₂ (Mem s) l l') (hm : List.Forall₂ (Mem s) m m') :
    List.Forall₂ (Mem s) (multiply zero add (mul s) l m) (multiply 0 (·+·) (·*·) l' m') := by
  induction hl with
  | nil => exact List.Forall₂.nil
  | cons ha htail ih =>
    apply rel_zipAdd (Mem s) add (·+·) (fun h₁ h₂ => mem_add h₁ h₂)
    · exact mem_map_mul hs ha hm
    · exact List.Forall₂.cons (mem_zero s) ih

 theorem mem_coeff {s : ℤ} {l : List Bounds} {l' : List ℝ}
    (hl : List.Forall₂ (Mem s) l l') (n : ℕ) :
    Mem s ((l[n]?).getD zero) ((polynomial l').coeff n) := by
  rw [polynomial_coeff]
  induction hl generalizing n with
  | nil => simpa using mem_zero s
  | cons ha htail ih =>
    cases n with
    | zero => exact ha
    | succ n => exact ih n

def sumCoefficients {α : Type*} (plus : α → α → α) : List (List α) → List α
  | [] => []
  | l::ls => zipAdd plus l (sumCoefficients plus ls)

def productCoefficients {α : Type*} (z one : α) (plus times : α → α → α) : List (List α) → List α
  | [] => [one]
  | l::ls => multiply z plus times l (productCoefficients z one plus times ls)

theorem polynomial_sumCoefficients (ls : List (List ℝ)) :
    polynomial (sumCoefficients (·+·) ls) = (ls.map polynomial).sum := by
  induction ls with
  | nil => simp [sumCoefficients,polynomial]
  | cons l ls ih => simp [sumCoefficients,polynomial_zipAdd,ih]

theorem polynomial_productCoefficients (ls : List (List ℝ)) :
    polynomial (productCoefficients 0 1 (·+·) (·*·) ls) = (ls.map polynomial).prod := by
  induction ls with
  | nil => simp [productCoefficients,polynomial]
  | cons l ls ih => simp [productCoefficients,polynomial_multiply,ih]

lemma rel_map {α β γ : Type*} (R : β → γ → Prop) (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ i ∈ l, R (f i) (g i)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons i l ih =>
    exact List.Forall₂.cons (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem mem_sumCoefficients {s : ℤ} {ls : List (List Bounds)} {ls' : List (List ℝ)}
    (h : List.Forall₂ (List.Forall₂ (Mem s)) ls ls') :
    List.Forall₂ (Mem s) (sumCoefficients add ls) (sumCoefficients (·+·) ls') := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hl htail ih => exact rel_zipAdd (Mem s) add (·+·) (fun h₁ h₂ => mem_add h₁ h₂) hl ih

theorem mem_productCoefficients {s : ℤ} (hs : 0 < s) {one : Bounds}
    (hOne : Mem s one 1) {ls : List (List Bounds)} {ls' : List (List ℝ)}
    (h : List.Forall₂ (List.Forall₂ (Mem s)) ls ls') :
    List.Forall₂ (Mem s) (productCoefficients zero one add (mul s) ls)
      (productCoefficients 0 1 (·+·) (·*·) ls') := by
  induction h with
  | nil => exact List.Forall₂.cons hOne List.Forall₂.nil
  | cons hl htail ih => exact mem_multiply hs hl ih

 theorem polynomial_map_neg (l : List ℝ) : polynomial (l.map (fun x => -x)) = -polynomial l := by
  induction l with
  | nil => simp [polynomial]
  | cons a l ih => simp [polynomial,ih]; ring

 theorem mem_map_neg {s : ℤ} {l : List Bounds} {l' : List ℝ}
    (hl : List.Forall₂ (Mem s) l l') :
    List.Forall₂ (Mem s) (l.map FixedInterval.neg) (l'.map (fun x => -x)) := by
  induction hl with
  | nil => exact List.Forall₂.nil
  | cons ha htail ih => exact List.Forall₂.cons (FixedInterval.mem_neg ha) ih
end ThomsonNine.ListPolynomial

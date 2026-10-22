import ThomsonNine.IntervalListPolynomial

-- Isolated source: Algebra.HornerShift
noncomputable section
namespace ThomsonNine.HornerShift
open ThomsonNine.ListPolynomial ThomsonNine.FixedInterval Polynomial

def affine (a : ℝ) (l : List ℝ) : List ℝ := zipAdd (·+·) (l.map (a*·)) (0::l)
def shifted (a : ℝ) : List ℝ → List ℝ
  | [] => []
  | c::l => zipAdd (·+·) [c] (affine a (shifted a l))

theorem affine_polynomial (a : ℝ) (l : List ℝ) :
    polynomial (affine a l)=(C a+X)*polynomial l := by
  rw [affine,polynomial_zipAdd,polynomial_map_mul,polynomial]
  simp only [map_zero,zero_add]
  ring

theorem shifted_eval (a x : ℝ) (l : List ℝ) :
    (polynomial (shifted a l)).eval x=(polynomial l).eval (a+x) := by
  induction l with
  | nil => simp [shifted,polynomial]
  | cons c l ih =>
    rw [shifted,polynomial_zipAdd,affine_polynomial]
    simp only [polynomial,eval_add,eval_C,eval_mul,eval_X,eval_zero,mul_zero,add_zero,ih]

theorem zipAdd_length {α : Type*} (plus : α → α → α) (l m : List α) :
    (zipAdd plus l m).length=max l.length m.length := by
  induction l generalizing m with
  | nil => simp [zipAdd]
  | cons a l ih =>
    cases m with
    | nil => simp [zipAdd]
    | cons b m => simp [zipAdd,ih]

theorem affine_length (a : ℝ) (l : List ℝ) : (affine a l).length=l.length+1 := by
  simp only [affine,zipAdd_length,List.length_map,List.length_cons]
  omega

theorem shifted_length (a : ℝ) (l : List ℝ) : (shifted a l).length=l.length := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [shifted,zipAdd_length,List.length_singleton,affine_length,ih,List.length_cons,List.length_nil]
    omega

def affineInput (s : ℤ) (A : Bounds) (l : List Bounds) : List Bounds :=
  zipAdd add (l.map (mul s A)) (zero::l)
def shiftedInput (s : ℤ) (A : Bounds) : List Bounds → List Bounds
  | [] => []
  | c::l => zipAdd add [c] (affineInput s A (shiftedInput s A l))

theorem affine_mem {s : ℤ} (hs : 0<s) {A : Bounds} {a : ℝ}
    (ha : Mem s A a) {l : List Bounds} {r : List ℝ} (hl : List.Forall₂ (Mem s) l r) :
    List.Forall₂ (Mem s) (affineInput s A l) (affine a r) :=
  rel_zipAdd (Mem s) add (·+·) (fun h1 h2 => mem_add h1 h2)
    (mem_map_mul hs ha hl) (List.Forall₂.cons (mem_zero s) hl)

theorem shifted_mem {s : ℤ} (hs : 0<s) {A : Bounds} {a : ℝ}
    (ha : Mem s A a) {l : List Bounds} {r : List ℝ} (hl : List.Forall₂ (Mem s) l r) :
    List.Forall₂ (Mem s) (shiftedInput s A l) (shifted a r) := by
  induction hl with
  | nil => exact List.Forall₂.nil
  | cons hc ht ih =>
    exact rel_zipAdd (Mem s) add (·+·) (fun h1 h2 => mem_add h1 h2)
      (List.Forall₂.cons hc List.Forall₂.nil) (affine_mem hs ha ih)

theorem bounds_list_ext (l m : List Bounds) (hl : l.map Bounds.lo=m.map Bounds.lo)
    (hh : l.map Bounds.hi=m.map Bounds.hi) : l=m := by
  induction l generalizing m with
  | nil => cases m <;> simpa using hl
  | cons a l ih =>
    cases m with
    | nil => simp at hl
    | cons b m =>
      simp only [List.map_cons,List.cons.injEq] at hl hh
      exact congrArg₂ List.cons (congrArg₂ Bounds.mk hl.1 hh.1) (ih m hl.2 hh.2)
end ThomsonNine.HornerShift

import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
DRAFT until direct Lean compilation succeeds.
Explicit Householder coordinates, independent of the numerical checker.
No local certificate, PSD claim, or Thomson minimum theorem is assumed here.
-/
noncomputable section

namespace ThomsonNine.Transverse

abbrev Vec3 := Fin 3 → ℝ

def dot3 (x y : Vec3) : ℝ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def north : Vec3 := ![0, 0, 1]

def beta (a x : Vec3) : ℝ := dot3 a x - x 2

def householder (a x : Vec3) : Vec3 :=
  fun i => x i - beta a x / (1 - a 2) * (a i - north i)

lemma unit_at_north (a : Vec3) (ha : dot3 a a = 1) (h2 : a 2 = 1) :
    a 0 = 0 ∧ a 1 = 0 := by
  dsimp [dot3] at ha
  rw [h2] at ha
  constructor <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]

lemma denominator_ne_zero (a : Vec3) (h2 : a 2 ≠ 1) : 1 - a 2 ≠ 0 := by
  intro h
  apply h2
  linarith

lemma householder_third (a x : Vec3) (hd : 1 - a 2 ≠ 0) :
    householder a x 2 = dot3 a x := by
  simp [householder, beta, north, dot3]
  field_simp [hd]
  <;> ring

lemma householder_dot (a x y : Vec3) (hd : 1 - a 2 ≠ 0) :
    dot3 (householder a x) (householder a y) = dot3 x y +
      (dot3 a a - 1) * beta a x * beta a y / (1 - a 2) ^ 2 := by
  simp [householder, beta, north, dot3]
  field_simp [hd]
  <;> ring

lemma householder_dot_unit (a x y : Vec3) (ha : dot3 a a = 1)
    (hd : 1 - a 2 ≠ 0) :
    dot3 (householder a x) (householder a y) = dot3 x y := by
  rw [householder_dot a x y hd, ha]
  simp

/-- One map works simultaneously for every pair of vectors. -/
theorem exists_transverse_isometry (a : Vec3) (ha : dot3 a a = 1) :
    ∃ T : Vec3 → Vec3,
      (∀ x y, dot3 (T x) (T y) = dot3 x y) ∧
      (∀ x, (T x) 2 = dot3 a x) := by
  by_cases h2 : a 2 = 1
  · obtain ⟨h0, h1⟩ := unit_at_north a ha h2
    refine ⟨id, ?_, ?_⟩
    · intro x y
      rfl
    · intro x
      simp [dot3, h0, h1, h2]
  · have hd := denominator_ne_zero a h2
    exact ⟨householder a, fun x y => householder_dot_unit a x y ha hd,
      fun x => householder_third a x hd⟩

lemma transverse_square_sum (a : Vec3) (T : Vec3 → Vec3)
    (hT : ∀ x y, dot3 (T x) (T y) = dot3 x y)
    (hthird : ∀ x, (T x) 2 = dot3 a x) (x : Vec3) :
    (T x) 0 * (T x) 0 + (T x) 1 * (T x) 1 =
      dot3 x x - (dot3 a x) ^ 2 := by
  have h := hT x x
  change (T x) 0 * (T x) 0 + (T x) 1 * (T x) 1 +
    (T x) 2 * (T x) 2 = dot3 x x at h
  rw [hthird x] at h
  nlinarith

lemma transverse_product_sum (a : Vec3) (T : Vec3 → Vec3)
    (hT : ∀ x y, dot3 (T x) (T y) = dot3 x y)
    (hthird : ∀ x, (T x) 2 = dot3 a x) (x y : Vec3) :
    (T x) 0 * (T y) 0 + (T x) 1 * (T y) 1 =
      dot3 x y - dot3 a x * dot3 a y := by
  have h := hT x y
  change (T x) 0 * (T y) 0 + (T x) 1 * (T y) 1 +
    (T x) 2 * (T y) 2 = dot3 x y at h
  rw [hthird x, hthird y] at h
  linarith

noncomputable def transverseComplex (T : Vec3 → Vec3) (x : Vec3) : ℂ :=
  ⟨(T x) 0, (T x) 1⟩

lemma transverseComplex_normSq (a : Vec3) (T : Vec3 → Vec3)
    (hT : ∀ x y, dot3 (T x) (T y) = dot3 x y)
    (hthird : ∀ x, (T x) 2 = dot3 a x) (x : Vec3) :
    Complex.normSq (transverseComplex T x) = dot3 x x - (dot3 a x) ^ 2 := by
  simpa only [transverseComplex, Complex.normSq_mk] using
    transverse_square_sum a T hT hthird x

lemma transverseComplex_re_mul_conj (a : Vec3) (T : Vec3 → Vec3)
    (hT : ∀ x y, dot3 (T x) (T y) = dot3 x y)
    (hthird : ∀ x, (T x) 2 = dot3 a x) (x y : Vec3) :
    (transverseComplex T x * star (transverseComplex T y)).re =
      dot3 x y - dot3 a x * dot3 a y := by
  have h := transverse_product_sum a T hT hthird x y
  simpa [transverseComplex, Complex.mul_re] using h

/-- Complex transverse coordinates for arbitrary vectors about a unit axis. -/
theorem exists_complex_coordinates (a : Vec3) (ha : dot3 a a = 1) :
    ∃ z : Vec3 → ℂ,
      (∀ x, Complex.normSq (z x) = dot3 x x - (dot3 a x) ^ 2) ∧
      (∀ x y, (z x * star (z y)).re = dot3 x y - dot3 a x * dot3 a y) := by
  obtain ⟨T, hT, hthird⟩ := exists_transverse_isometry a ha
  exact ⟨transverseComplex T, transverseComplex_normSq a T hT hthird,
    transverseComplex_re_mul_conj a T hT hthird⟩

end ThomsonNine.Transverse

import ThomsonNine.ThreePointBound
import ThomsonNine.Statement

/-!
# n=10 three-point certificate interface

This is an instance-sized wrapper around the already generic `three_point_bound_sos`
theorem.  It intentionally carries the pointwise Gram-domain inequality as a
field: no n=10 PSD blocks or global coverage data are asserted here.
-/

namespace ThomsonTen

open ThomsonNine
open ThomsonNine.ThreePoint
open scoped RealInnerProductSpace

theorem n10_choose_two : (Nat.choose 10 2 : ℝ) = 45 := by norm_num [Nat.choose]

theorem n10_Rk_expansion {m k : ℕ} (u v t : ℝ) :
    Rk 10 m k u v t =
      (8 : ℝ) • S3 m k u v t +
        (S3 m k u u 1 + S3 m k v v 1 + S3 m k t t 1) +
          (1 / 9 : ℝ) • S3 m k 1 1 1 := by
  unfold Rk
  norm_num [Nat.cast_ofNat]

theorem n10_pointwise_rhs (H : ℝ → ℝ) (e u v t : ℝ) :
    (H u + H v + H t) / 3 - e / (Nat.choose 10 2 : ℝ) =
      (H u + H v + H t) / 3 - e / 45 := by
  rw [n10_choose_two]

structure ThreePointCertificate10 where
  K : ℕ
  m : ℕ → ℕ
  F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ
  sos : ∀ k, k < K → ∃ (r : ℕ) (v : Fin r → Fin (m k) → ℝ),
    F k = ∑ s, Matrix.vecMulVec (v s) (v s)
  H : ℝ → ℝ
  e : ℝ
  pointwise : ∀ u v t : ℝ, GramOK u v t →
    ∑ k ∈ Finset.range K,
        matDot (F k) (Rk 10 (m k) k u v t) ≤
      (H u + H v + H t) / 3 - e / (Nat.choose 10 2 : ℝ)

theorem ThreePointCertificate10.lower_bound
    (C : ThreePointCertificate10) (x : Fin 10 → R3)
    (hx : ∀ i, ‖x i‖ = 1) :
    C.e ≤ ∑ i, ∑ j ∈ Finset.Ioi i, C.H (⟪x i, x j⟫) := by
  exact three_point_bound_sos (n := 10) (by norm_num) C.K C.m C.F C.sos C.H C.e
    C.pointwise x hx

end ThomsonTen

import ThomsonNine.LocalLDLSemantics

/-! Exact LDL recurrence and preconditioning identities.
Theorems require enclosure of the REAL pivots. Exported endpoint positivity
alone does not establish those membership premises for the actual Hessian.
-/

namespace ThomsonNine.LocalLDL

/-- The second pivot in the checker's scalar LDL recurrence. -/
noncomputable def pivot2 (a b d : ℝ) : ℝ := d - (b / a) ^ 2 * a

/-- The third pivot in the checker's scalar LDL recurrence. -/
noncomputable def pivot3 (a b c d e f : ℝ) : ℝ :=
  f - (c / a) ^ 2 * a -
    ((e - (c / a) * (b / a) * a) / pivot2 a b d) ^ 2 * pivot2 a b d

/-- The six entry identities are consequences of the actual division recurrence;
no independent factorization premise is needed. -/
theorem quadratic_eq_recurrence (a b c d e f x y z : ℝ)
    (ha : a ≠ 0) (hp : pivot2 a b d ≠ 0) :
    symmetricQuadratic a b c d e f x y z =
      quadratic a (pivot2 a b d) (pivot3 a b c d e f)
        (b / a) (c / a) ((e - (c / a) * (b / a) * a) / pivot2 a b d) x y z := by
  apply quadratic_eq_of_entries
  · rfl
  · exact (div_mul_cancel₀ b ha).symm
  · exact (div_mul_cancel₀ c ha).symm
  · unfold pivot2
    ring
  · rw [div_mul_cancel₀ _ hp]
    ring
  · unfold pivot3
    ring

/-- Enclosed real LDL pivots certify the original six-entry quadratic form. -/
theorem LDL3Cert.entries_nonneg (cert : LDL3Cert) (a b c d e f : ℝ)
    (h1 : cert.d1.mem a) (h2 : cert.d2.mem (pivot2 a b d))
    (h3 : cert.d3.mem (pivot3 a b c d e f)) (x y z : ℝ) :
    0 ≤ symmetricQuadratic a b c d e f x y z := by
  rw [quadratic_eq_recurrence a b c d e f x y z
    (ne_of_gt (positive_of_mem cert.hd1 h1))
    (ne_of_gt (positive_of_mem cert.hd2 h2))]
  exact cert.sound h1 h2 h3 _ _ _ _ _ _

/-- Entries of W H Wᵀ, for W unit lower triangular with entries a,b,c. -/
theorem symmetricQuadratic_congruence (A B C D E F a b c x y z : ℝ) :
    symmetricQuadratic A (a * A + B) (b * A + c * B + C)
      (a ^ 2 * A + 2 * a * B + D)
      (a * b * A + (a * c + b) * B + a * C + c * D + E)
      (b ^ 2 * A + 2 * b * c * B + 2 * b * C + c ^ 2 * D + 2 * c * E + F)
      x y z =
      symmetricQuadratic A B C D E F (x + a * y + b * z) (y + c * z) z := by
  unfold symmetricQuadratic
  ring

/-- Full 3D preconditioned entry bridge; all remaining arithmetic premises are
memberships of the actual real pivots in the exported intervals. -/
theorem LDL3Cert.preconditioned_entries_nonneg (cert : LDL3Cert)
    (A B C D E F : ℝ)
    (h1 : cert.d1.mem A)
    (h2 : cert.d2.mem (pivot2 A ((cert.w21 : ℝ) * A + B)
      ((cert.w21 : ℝ) ^ 2 * A + 2 * cert.w21 * B + D)))
    (h3 : cert.d3.mem (pivot3 A ((cert.w21 : ℝ) * A + B)
      ((cert.w31 : ℝ) * A + cert.w32 * B + C)
      ((cert.w21 : ℝ) ^ 2 * A + 2 * cert.w21 * B + D)
      ((cert.w21 : ℝ) * cert.w31 * A + (cert.w21 * cert.w32 + cert.w31) * B +
        cert.w21 * C + cert.w32 * D + E)
      ((cert.w31 : ℝ) ^ 2 * A + 2 * cert.w31 * cert.w32 * B +
        2 * cert.w31 * C + (cert.w32 : ℝ) ^ 2 * D + 2 * cert.w32 * E + F)))
    (x y z : ℝ) : 0 ≤ symmetricQuadratic A B C D E F x y z := by
  apply congruence_nonneg (symmetricQuadratic A B C D E F)
    (symmetricQuadratic A ((cert.w21 : ℝ) * A + B)
      ((cert.w31 : ℝ) * A + cert.w32 * B + C)
      ((cert.w21 : ℝ) ^ 2 * A + 2 * cert.w21 * B + D)
      ((cert.w21 : ℝ) * cert.w31 * A + (cert.w21 * cert.w32 + cert.w31) * B +
        cert.w21 * C + cert.w32 * D + E)
      ((cert.w31 : ℝ) ^ 2 * A + 2 * cert.w31 * cert.w32 * B +
        2 * cert.w31 * C + (cert.w32 : ℝ) ^ 2 * D + 2 * cert.w32 * E + F))
    cert.w21 cert.w31 cert.w32
  · exact fun u v w => symmetricQuadratic_congruence A B C D E F _ _ _ u v w
  · exact fun u v w => cert.entries_nonneg _ _ _ _ _ _ h1 h2 h3 u v w

/-- Boundary recurrence, including its exact quadratic factorization. -/
theorem LDL2Cert.entries_nonneg (cert : LDL2Cert) (a b c : ℝ)
    (h1 : cert.d1.mem a) (h2 : cert.d2.mem (pivot2 a b c)) (x y : ℝ) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  have ha : a ≠ 0 := ne_of_gt (positive_of_mem cert.hd1 h1)
  rw [quadratic2_eq_of_entries a b c a (pivot2 a b c) (b / a) x y rfl
    (div_mul_cancel₀ b ha).symm (by unfold pivot2; ring)]
  exact cert.sound h1 h2 _ _ _

/-- Boundary version of the exact inverse-congruence bridge. -/
theorem LDL2Cert.preconditioned_entries_nonneg (cert : LDL2Cert) (A B C : ℝ)
    (h1 : cert.d1.mem A)
    (h2 : cert.d2.mem (pivot2 A ((cert.w21 : ℝ) * A + B)
      ((cert.w21 : ℝ) ^ 2 * A + 2 * cert.w21 * B + C))) (x y : ℝ) :
    0 ≤ A * x ^ 2 + 2 * B * x * y + C * y ^ 2 := by
  apply congruence2_nonneg (fun u v => A * u ^ 2 + 2 * B * u * v + C * v ^ 2)
    (fun u v => A * u ^ 2 + 2 * ((cert.w21 : ℝ) * A + B) * u * v +
      ((cert.w21 : ℝ) ^ 2 * A + 2 * cert.w21 * B + C) * v ^ 2) cert.w21
  · intros
    ring
  · exact fun u v => cert.entries_nonneg _ _ _ h1 h2 u v

end ThomsonNine.LocalLDL

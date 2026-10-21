import ThomsonNine.GramBound

/-!
# The ordered chamber of three unit vectors

The certificate for the nine-point candidate is posed on the ordered chamber
`D = {u ≤ v ≤ t, -1 ≤ u, t ≤ 1, 0 ≤ gram u v t}`.  The physical input is an
*unordered* triple of pairwise inner products of three unit vectors.  This file
shows that sorting that triple loses nothing: some ordering of the three inner
products always lands in the chamber, with the Gram constraint preserved.

The upper bound `t ≤ 14/25` used by the certificate is an extra pair-reduction
input and is deliberately **not** claimed here.
-/

open scoped BigOperators InnerProductSpace

namespace ThomsonNine

open ThomsonNine.Semantics (gram)

theorem gram_swap12 (u v t : ℝ) : gram u v t = gram v u t := by
  unfold gram
  ring

theorem gram_swap23 (u v t : ℝ) : gram u v t = gram u t v := by
  unfold gram
  ring

theorem gram_swap13 (u v t : ℝ) : gram u v t = gram t v u := by
  unfold gram
  ring

/-- Sorting three numbers in `[-1,1]` whose Gram constraint holds preserves the
constraint and gives an ordered triple in the chamber. -/
theorem exists_ordered_domain_triple (p q r : ℝ)
    (hp : p ∈ Set.Icc (-1 : ℝ) 1) (hq : q ∈ Set.Icc (-1 : ℝ) 1)
    (hr : r ∈ Set.Icc (-1 : ℝ) 1) (hg : 0 ≤ gram p q r) :
    ∃ u v t : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 ∧ t ∈ Set.Icc (-1 : ℝ) 1 ∧
      u ≤ v ∧ v ≤ t ∧ 0 ≤ gram u v t := by
  rcases le_total p q with hpq | hqp
  · rcases le_total q r with hqr | hrq
    · exact ⟨p, q, r, hp, hr, hpq, hqr, hg⟩
    · rcases le_total p r with hpr | hrp
      · exact ⟨p, r, q, hp, hq, hpr, hrq, by rw [gram_swap23]; exact hg⟩
      · exact ⟨r, p, q, hr, hq, hrp, hpq,
          by rw [gram_swap12, gram_swap23]; exact hg⟩
  · rcases le_total p r with hpr | hrp
    · exact ⟨q, p, r, hq, hr, hqp, hpr, by rw [gram_swap12]; exact hg⟩
    · rcases le_total q r with hqr | hrq
      · exact ⟨q, r, p, hq, hp, hqr, hrp,
          by rw [gram_swap13, gram_swap23]; exact hg⟩
      · exact ⟨r, q, p, hr, hp, hrq, hqp, by rw [gram_swap13]; exact hg⟩

/-- Every triple of points of a unit configuration has a sorted inner-product
triple in the ordered chamber. -/
theorem exists_ordered_gram_constraint_of_mem (x : Fin 9 → R3)
    (hx : x ∈ SphereConfig 9) (i j k : Fin 9) :
    ∃ u v t : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 ∧ t ∈ Set.Icc (-1 : ℝ) 1 ∧
      u ≤ v ∧ v ≤ t ∧ 0 ≤ gram u v t :=
  exists_ordered_domain_triple (⟪x i, x j⟫_ℝ) (⟪x i, x k⟫_ℝ) (⟪x j, x k⟫_ℝ)
    (inner_mem_Icc_of_mem x hx i j) (inner_mem_Icc_of_mem x hx i k)
    (inner_mem_Icc_of_mem x hx j k) (gram_constraint_of_mem x hx i j k)

end ThomsonNine

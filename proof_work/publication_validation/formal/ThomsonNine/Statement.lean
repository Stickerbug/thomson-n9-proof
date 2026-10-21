import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators

/-! Frozen specification only. This file asserts no theorem and contains no sorry or axiom. -/
namespace ThomsonNine
abbrev R3 := EuclideanSpace ℝ (Fin 3)
def SphereConfig (n : ℕ) : Set (Fin n → R3) :=
  {x | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}
noncomputable def energy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹
noncomputable def cyl (ρ θ h : ℝ) : R3 :=
  !₂[ρ * Real.cos θ, ρ * Real.sin θ, h]
noncomputable def candidate (r : ℝ) : Fin 9 → R3 := fun i =>
  if (i : ℕ) < 3 then cyl r (2 * Real.pi * (i : ℕ) / 3) (Real.sqrt (1-r^2))
  else if (i : ℕ) < 6 then
    cyl r (2 * Real.pi * ((i : ℕ)-3) / 3) (-Real.sqrt (1-r^2))
  else cyl 1 ((2*((i : ℕ)-6)+1) * Real.pi / 3) 0
noncomputable def familyEnergy (r : ℝ) : ℝ :=
  Real.sqrt 3 + 2*Real.sqrt 3/r + 3/(2*Real.sqrt (1-r^2)) +
  6/Real.sqrt (4-r^2) + 12/Real.sqrt (2-r) + 6/Real.sqrt (2+2*r)
def ThomsonNineClaim : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧ HasDerivAt familyEnergy 0 r ∧
    (∀ s : ℝ, 0 < s → s < 1 → HasDerivAt familyEnergy 0 s → s = r) ∧
    candidate r ∈ SphereConfig 9 ∧ energy (candidate r) = familyEnergy r ∧
    ∀ x ∈ SphereConfig 9, familyEnergy r ≤ energy x
end ThomsonNine

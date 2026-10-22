import MainCoverage.DiagonalFields
import MainCoverage.DyadicGeometry
import MainCoverage.LeafSemantics
import PackedTensor.BernsteinListSpec20

noncomputable section
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix

def DiagonalLower (D : ℝ → ℝ) (e : DiagonalEntry) : Prop :=
  ∀ t, 0≤t ∧ t≤1 → uniValue 20 offset scale e.word t≤-D (point e.level e.index t)

attribute [local irreducible] uniValue

theorem all_diagonal_lower (D : ℝ → ℝ)
    (hRoot : ∀ t, 0≤t ∧ t≤1 → uniValue 20 offset scale diagonalRootWord t≤-D (point 0 0 t))
    (id : ℕ) (hid : id<4816) : DiagonalLower D (diagonalLookup id) := by
  induction id using Nat.strong_induction_on with
  | h id ih =>
    have hcheck := all_diagonal_fields id hid
    by_cases hz : id=0
    · subst id
      have hp : (diagonalLookup 0).level=0 ∧ (diagonalLookup 0).index=0 ∧ (diagonalLookup 0).word=diagonalRootWord := by
        simpa only [diagonalOK,ite_true,decide_eq_true_eq] using hcheck
      intro t ht
      rw [hp.1,hp.2.1,hp.2.2]
      exact hRoot t ht
    · let e := diagonalLookup id
      let p := diagonalLookup e.parent
      let side : Bool := decide (e.index%2=1)
      have hp : (e.parent < id ∧ e.level=p.level+1 ∧ e.index=2*p.index+e.index%2 ∧ e.index%2≤1) ∧
          uniHalfOK 21 bound side p.word=true ∧ uniHalf 21 bound side p.word=e.word := by
        simpa only [diagonalOK,if_neg hz,Bool.and_eq_true_iff,decide_eq_true_eq,and_assoc] using hcheck
      have hparent := ih e.parent hp.1.1 (by omega)
      intro t ht
      have ht' : 0≤((if side then 1+t else t)/2) ∧ ((if side then 1+t else t)/2)≤1 := by
        cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true]
        all_goals constructor <;> linarith [ht.1,ht.2]
      have hnum : (if side then (1:ℕ) else 0)=e.index%2 := by
        by_cases hh : e.index%2=1
        · simp [side,hh]
        · have hm := Nat.mod_lt e.index (by omega : 0<2)
          simp [side,hh]
          omega
      have hpoint : point e.level e.index t=point p.level p.index ((if side then 1+t else t)/2) := by
        rw [hp.1.2.1,hp.1.2.2.1,← hnum]
        exact point_split p.level p.index side t
      have hhalf := uniHalf_lower 20 bound offset scale row_spec_21 basis_list_spec_20 side p.word
        bound_valid hp.2.1 scale_pos t ht
      have hpval := hparent _ ht'
      change uniValue 20 offset scale e.word t≤-D (point e.level e.index t)
      rw [← hp.2.2,hpoint]
      exact hhalf.trans hpval
end ThomsonNine.PackedMain

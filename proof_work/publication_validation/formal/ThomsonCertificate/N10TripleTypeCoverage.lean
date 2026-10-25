import ThomsonCertificate.N10GramSymmetry

/-!
Type-level interface for the twelve symbolic D4d triple classes.  The
`coverage` field is intentionally explicit: this module packages local Gram
facts but does not assert that every arbitrary ten-point configuration is
covered by the D4d list.
-/
namespace ThomsonTen

open ThomsonNine.ThreePoint

structure N10LocalTripleType where
  support : ℝ → Prop
  gram_certificate : ∀ {h : ℝ}, support h → GramOK (-h) (-h) (h^2)

structure N10TripleTypeCoverage where
  types : Fin 12 → N10LocalTripleType
  multiplicity : Fin 12 → ℕ
  multiplicity_sum : ∑ i, multiplicity i = 120
  coverage : ∀ (i : Fin 12) (h : ℝ), (types i).support h →
    GramOK (-h) (-h) (h^2)

theorem N10TripleTypeCoverage.local_gram
    (C : N10TripleTypeCoverage) (i : Fin 12) {h : ℝ}
    (hs : (C.types i).support h) : GramOK (-h) (-h) (h^2) :=
  C.coverage i h hs

theorem N10TripleTypeCoverage.counts_to_120
    (C : N10TripleTypeCoverage) : ∑ i, C.multiplicity i = 120 :=
  C.multiplicity_sum

end ThomsonTen

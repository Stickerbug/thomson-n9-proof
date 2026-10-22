import MainCoverage.TreeModel
import PackedRadix.Univariate

namespace ThomsonNine.PackedMain
open ThomsonNine.PackedRadix
structure DiagonalEntry where
  level : ℕ
  index : ℕ
  parent : ℕ
  word : ℕ

def diagonalOK (lookup : ℕ → DiagonalEntry) (rootWord id : ℕ) : Bool :=
  let e := lookup id
  if id=0 then decide (e.level=0 ∧ e.index=0 ∧ e.word=rootWord)
  else
    let p := lookup e.parent
    let side : Bool := decide (e.index%2=1)
    decide (e.parent < id ∧ e.level=p.level+1 ∧ e.index=2*p.index+e.index%2 ∧ e.index%2≤1) &&
      uniHalfOK 21 bound side p.word && decide (uniHalf 21 bound side p.word=e.word)
end ThomsonNine.PackedMain

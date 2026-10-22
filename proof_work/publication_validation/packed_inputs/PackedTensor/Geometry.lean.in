import PackedTensor.MaskData
import Mathlib.Tactic.FinCases

namespace ThomsonNine.PackedTensor
abbrev CubeIndex (d : ℕ) := Fin d × Fin d × Fin d
def flat {d : ℕ} (p : CubeIndex d) : ℕ := index d p.1 p.2.1 p.2.2
def coord {d : ℕ} (axis : Fin 3) (p : CubeIndex d) : Fin d := coordinate d axis p.1 p.2.1 p.2.2
def stride (d : ℕ) (axis : Fin 3) : ℕ := if axis=0 then d*d else if axis=1 then d else 1
def replace {d : ℕ} (axis : Fin 3) (p : CubeIndex d) (c : Fin d) : CubeIndex d :=
  if axis=0 then (c,p.2.1,p.2.2) else if axis=1 then (p.1,c,p.2.2) else (p.1,p.2.1,c)
def zeroIndex {d : ℕ} [NeZero d] (axis : Fin 3) (p : CubeIndex d) : ℕ := flat (replace axis p 0)

theorem flat_lt {d : ℕ} (p : CubeIndex d) : flat p<d*d*d := by
  have hmid : p.1.val*d+p.2.1.val<d*d := by
    calc
      p.1.val*d+p.2.1.val<p.1.val*d+d := Nat.add_lt_add_left p.2.1.isLt _
      _ = (p.1.val+1)*d := by ring
      _ ≤ d*d := Nat.mul_le_mul_right d (by omega)
  change (p.1.val*d+p.2.1.val)*d+p.2.2.val<d*d*d
  calc
    (p.1.val*d+p.2.1.val)*d+p.2.2.val<(p.1.val*d+p.2.1.val)*d+d :=
      Nat.add_lt_add_left p.2.2.isLt _
    _ = (p.1.val*d+p.2.1.val+1)*d := by ring
    _ ≤ d*d*d := Nat.mul_le_mul_right d (by omega)

theorem coord_replace {d : ℕ} (axis : Fin 3) (p : CubeIndex d) (c : Fin d) :
    coord axis (replace axis p c)=c := by
  fin_cases axis <;> simp [coord,coordinate,replace]
theorem replace_same {d : ℕ} (axis : Fin 3) (p : CubeIndex d) : replace axis p (coord axis p)=p := by
  fin_cases axis <;> simp [coord,coordinate,replace]
theorem flat_replace {d : ℕ} [NeZero d] (axis : Fin 3) (p : CubeIndex d) (c : Fin d) :
    flat (replace axis p c)=zeroIndex axis p+stride d axis*c.val := by
  fin_cases axis <;> simp [flat,index,zeroIndex,replace,stride] <;> ring
theorem flat_decompose {d : ℕ} [NeZero d] (axis : Fin 3) (p : CubeIndex d) :
    flat p=zeroIndex axis p+stride d axis*(coord axis p).val := by
  have h := flat_replace axis p (coord axis p)
  rw [replace_same] at h
  exact h
theorem zeroIndex_replace {d : ℕ} [NeZero d] (axis : Fin 3) (p : CubeIndex d) (c : Fin d) :
    zeroIndex axis (replace axis p c)=zeroIndex axis p := by
  fin_cases axis <;> simp [zeroIndex,replace]
end ThomsonNine.PackedTensor

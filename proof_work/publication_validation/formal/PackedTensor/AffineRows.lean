import PackedTensor.Half
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

noncomputable section
namespace ThomsonNine.PackedTensor
open ThomsonNine.PackedRadix
def decode (offset scale x i : ℕ) : ℝ := ((limb 128 x i : ℝ)-(offset : ℝ))/(scale : ℝ)
def realRow (parent : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,pos => parent pos
  | j+1,pos => (realRow parent j pos+realRow parent j (pos+1))/2

theorem scaled_average_bound (a b c offset scale : ℕ) (A B : ℝ) (hs : (0 : ℝ)<scale)
    (hc : c=(a+b)/2) (ha : ((a : ℝ)-(offset : ℝ))/(scale : ℝ)≤A)
    (hb : ((b : ℝ)-(offset : ℝ))/(scale : ℝ)≤B) :
    ((c : ℝ)-(offset : ℝ))/(scale : ℝ)≤(A+B)/2 := by
  have hn : 2*c≤a+b := by omega
  have hr : (2 : ℝ)*(c : ℝ)≤(a : ℝ)+(b : ℝ) := by exact_mod_cast hn
  have ha' := (div_le_iff₀ hs).mp ha
  have hb' := (div_le_iff₀ hs).mp hb
  apply (div_le_iff₀ hs).mpr
  nlinarith

theorem rows_bound (d n g step x offset scale : ℕ) (rows : List ℕ)
    (hg : 2*g+1<2^128) (h : rowsOK d n g step x rows=true)
    (hs : (0 : ℝ)<scale) (base : ℕ) (parent : ℕ → ℝ)
    (hindex : ∀ j<d, base+step*j<n)
    (hbase : ∀ j<d, decode offset scale x (base+step*j)≤parent j) :
    ∀ level pos : ℕ, level+pos<d →
      decode offset scale (rowAt rows level) (base+step*pos)≤realRow parent level pos := by
  intro level
  induction level with
  | zero =>
    intro pos hp
    rw [rows_initial h]
    exact hbase pos (by omega)
  | succ level ih =>
    intro pos hp
    have hstep := rows_step hg h level (base+step*pos) (by omega) (hindex pos (by omega))
    have he : base+step*pos+step=base+step*(pos+1) := by ring
    rw [he] at hstep
    exact scaled_average_bound _ _ _ offset scale _ _ hs hstep
      (ih pos (by omega)) (ih (pos+1) (by omega))
end ThomsonNine.PackedTensor

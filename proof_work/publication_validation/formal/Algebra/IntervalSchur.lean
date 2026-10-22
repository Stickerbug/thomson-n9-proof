import Algebra.SchurSolve
import Algebra.FixedHorner

noncomputable section
namespace ThomsonNine.FixedInterval.Schur
open scoped BigOperators

def subtract (I J : Bounds) : Bounds := add I (neg J)
lemma mem_subtract {s : ℤ} {I J : Bounds} {x y : ℝ} (hx : Mem s I x) (hy : Mem s J y) :
    Mem s (subtract I J) (x-y) := by simpa only [subtract,sub_eq_add_neg] using mem_add hx (mem_neg hy)
def sumFin {n : ℕ} (f : Fin n → Bounds) : Bounds := FixedInterval.sum ((List.finRange n).map f)
lemma sumFin_mem {n : ℕ} {s : ℤ} (f : Fin n → Bounds) (g : Fin n → ℝ)
    (h : ∀ i, Mem s (f i) (g i)) : Mem s (sumFin f) (∑ i, g i) := by
  have hh := FixedInterval.sum_mem f g (List.finRange n) (fun i _ => h i)
  have hs := List.sum_toFinset g (show (List.finRange n).Nodup by exact List.nodup_finRange n)
  have heq : (List.finRange n).toFinset = (Finset.univ : Finset (Fin n)) := by ext i; simp
  rw [← hs,heq] at hh
  exact hh

def reducedMatrix {n : ℕ} (s : ℤ) (A : Fin (n+1) → Fin (n+1) → Bounds) (iv : Bounds) :
    Fin n → Fin n → Bounds := fun i j => subtract (A i.succ j.succ) (mul s (mul s (A i.succ 0) iv) (A 0 j.succ))
def reducedRhs {n : ℕ} (s : ℤ) (A : Fin (n+1) → Fin (n+1) → Bounds)
    (b : Fin (n+1) → Bounds) (iv : Bounds) : Fin n → Bounds :=
  fun i => subtract (b i.succ) (mul s (mul s (A i.succ 0) iv) (b 0))
def recover {n : ℕ} (s : ℤ) (A : Fin (n+1) → Fin (n+1) → Bounds)
    (b : Fin (n+1) → Bounds) (iv : Bounds) (tail : Fin n → Bounds) : Fin (n+1) → Bounds :=
  Fin.cons (mul s iv (subtract (b 0) (sumFin (fun j => mul s (A 0 j.succ) (tail j))))) tail

theorem reducedMatrix_mem {n : ℕ} {s : ℤ} (hs : 0<s)
    (IA : Fin (n+1) → Fin (n+1) → Bounds) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, Mem s (IA i j) (A i j)) (iv : Bounds) (hiv : Mem s iv ((A 0 0)⁻¹))
    (i j : Fin n) : Mem s (reducedMatrix s IA iv i j) (SchurSolve.reducedMatrix A i j) :=
  mem_subtract (hA _ _) (mem_mul hs (mem_mul hs (hA _ _) hiv) (hA _ _))
theorem reducedRhs_mem {n : ℕ} {s : ℤ} (hs : 0<s)
    (IA : Fin (n+1) → Fin (n+1) → Bounds) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (Ib : Fin (n+1) → Bounds) (b : Fin (n+1) → ℝ)
    (hA : ∀ i j, Mem s (IA i j) (A i j)) (hb : ∀ i, Mem s (Ib i) (b i))
    (iv : Bounds) (hiv : Mem s iv ((A 0 0)⁻¹))
    (i : Fin n) : Mem s (reducedRhs s IA Ib iv i) (SchurSolve.reducedRhs A b i) :=
  mem_subtract (hb _) (mem_mul hs (mem_mul hs (hA _ _) hiv) (hb _))
theorem recover_mem {n : ℕ} {s : ℤ} (hs : 0<s)
    (IA : Fin (n+1) → Fin (n+1) → Bounds) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (Ib : Fin (n+1) → Bounds) (b : Fin (n+1) → ℝ)
    (hA : ∀ i j, Mem s (IA i j) (A i j)) (hb : ∀ i, Mem s (Ib i) (b i))
    (iv : Bounds) (hiv : Mem s iv ((A 0 0)⁻¹))
    (Itail : Fin n → Bounds) (tail : Fin n → ℝ) (htail : ∀ i, Mem s (Itail i) (tail i)) :
    ∀ i, Mem s (recover s IA Ib iv Itail i) (SchurSolve.recover A b tail i) := by
  intro i
  cases i using Fin.cases with
  | zero =>
    exact mem_mul hs hiv (mem_subtract (hb _) (sumFin_mem _ _ (fun j => mem_mul hs (hA _ _) (htail _))))
  | succ i => exact htail i
end ThomsonNine.FixedInterval.Schur

import ThomsonNine.IntervalListPolynomial

noncomputable section
namespace ThomsonNine.IntervalMonicSolve
open ThomsonNine.FixedInterval
open ThomsonNine.ListPolynomial
open scoped BigOperators

def realTail (d : ℕ) (q : ℕ → ℝ) : ℕ → List ℝ
  | 0 => []
  | k+1 => q (d-1-k)::realTail d q k

def solveTail (d : ℕ) (s : ℤ) (g w : ℕ → Bounds) : ℕ → List Bounds
  | 0 => []
  | k+1 =>
    let tail := solveTail d s g w k
    let corr := FixedInterval.sum ((List.range d).map
      (fun j => mul s (w j) ((tail[d-1-j]?).getD zero)))
    add (g (d-1-k+d)) (neg corr)::tail

lemma realTail_lookup (d : ℕ) (q : ℕ → ℝ) (k : ℕ) (hk : k≤d) (j : ℕ) :
    ((realTail d q k)[j]?).getD 0 = if j<k then q (d-k+j) else 0 := by
  induction k generalizing j with
  | zero => simp [realTail]
  | succ k ih =>
    cases j with
    | zero =>
      simp only [realTail,List.getElem?_cons_zero,Option.getD_some,Nat.zero_lt_succ,if_pos,Nat.add_zero]
      congr 1
      omega
    | succ j =>
      simp only [realTail,List.getElem?_cons_succ]
      rw [ih (by omega)]
      by_cases h : j<k
      · simp only [Nat.succ_lt_succ_iff,h,if_pos]
        congr 1
        omega
      · simp [h]

lemma tail_correction_lookup (d : ℕ) (q : ℕ → ℝ)
    (hzero : ∀ n, d≤n → q n=0) (k j : ℕ) (hk : k<d) (hj : j<d) :
    ((realTail d q k)[d-1-j]?).getD 0 = q (d-1-k+d-j) := by
  rw [realTail_lookup d q k (by omega)]
  split
  · congr 1
    omega
  · symm
    apply hzero
    omega

lemma lookup_mem {s : ℤ} {l : List Bounds} {r : List ℝ}
    (h : List.Forall₂ (Mem s) l r) (j : ℕ) :
    Mem s ((l[j]?).getD zero) ((r[j]?).getD 0) := by
  simpa only [polynomial_coeff] using mem_coeff h j

/-- Descending coefficient recovery from a monic product relation. All rounding
occurs in the supplied integer interval operations. -/
theorem solveTail_mem (d : ℕ) {s : ℤ} (hs : 0<s) (g w : ℕ → Bounds)
    (G W q : ℕ → ℝ)
    (hG : ∀ n, Mem s (g n) (G n)) (hW : ∀ n, Mem s (w n) (W n))
    (hzero : ∀ n, d≤n → q n=0)
    (hrec : ∀ n, n<d → q n = G (n+d)-∑ j ∈ Finset.range d, W j*q (n+d-j))
    (k : ℕ) (hk : k≤d) :
    List.Forall₂ (Mem s) (solveTail d s g w k) (realTail d q k) := by
  induction k with
  | zero => exact List.Forall₂.nil
  | succ k ih =>
    have htail := ih (by omega)
    have hcorr : Mem s
        (FixedInterval.sum ((List.range d).map (fun j =>
          mul s (w j) (((solveTail d s g w k)[d-1-j]?).getD zero))))
        (((List.range d).map (fun j => W j*q (d-1-k+d-j))).sum) := by
      apply FixedInterval.sum_mem
      intro j hj
      have hlookup := lookup_mem htail (d-1-j)
      rw [tail_correction_lookup d q hzero k j (by omega) (List.mem_range.mp hj)] at hlookup
      exact mem_mul hs (hW j) hlookup
    have hsum : (((List.range d).map (fun j => W j*q (d-1-k+d-j))).sum) =
        ∑ j ∈ Finset.range d, W j*q (d-1-k+d-j) := by
      symm
      simpa only [List.toFinset_range] using
        List.sum_toFinset (fun j => W j*q (d-1-k+d-j)) (List.nodup_range (n := d))
    rw [hsum] at hcorr
    have hhead := mem_add (hG (d-1-k+d)) (mem_neg hcorr)
    have hhead' : Mem s
        (add (g (d-1-k+d)) (neg (FixedInterval.sum ((List.range d).map (fun j =>
          mul s (w j) (((solveTail d s g w k)[d-1-j]?).getD zero)))))) (q (d-1-k)) := by
      rw [hrec (d-1-k) (by omega)]
      simpa only [sub_eq_add_neg] using hhead
    exact List.Forall₂.cons hhead' htail

 theorem polynomial_realTail (d : ℕ) (P : Polynomial ℝ)
    (hz : ∀ n, d≤n → P.coeff n=0) :
    polynomial (realTail d P.coeff d) = P := by
  apply Polynomial.ext
  intro n
  rw [polynomial_coeff,realTail_lookup d P.coeff d (le_refl d)]
  by_cases h : n<d
  · simp [h]
  · simp [h,hz n (by omega)]
end ThomsonNine.IntervalMonicSolve

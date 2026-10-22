import ThomsonNine.CollectedTranslation

set_option maxRecDepth 10000
noncomputable section
namespace ThomsonNine.Interval.SparsePolynomial.Collected

def natMask : List ℕ → ℕ
  | [] => 0
  | n :: l => (2^n) ||| natMask l

 theorem natMask_mem (l : List ℕ) (n : ℕ) :
    (natMask l).testBit n = true ↔ n ∈ l := by
  induction l with
  | nil => simp [natMask]
  | cons i l ih =>
    simp only [natMask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, List.mem_cons, ih]
    exact or_congr eq_comm Iff.rfl

def encode (e : Exp3) : ℕ := e 0 * 784 + e 1 * 28 + e 2

def bounded (e : Exp3) : Prop := e 0 < 28 ∧ e 1 < 28 ∧ e 2 < 28

 theorem encode_inj {e k : Exp3} (he : bounded e) (hk : bounded k)
    (h : encode e = encode k) : e = k := by
  simp only [bounded] at he hk
  unfold encode at h
  have h0 : e 0 = k 0 := by omega
  have h1 : e 1 = k 1 := by omega
  have h2 : e 2 = k 2 := by omega
  funext j
  fin_cases j <;> assumption

 theorem mem_of_code (q : List Exp3) (hq : ∀ e ∈ q, bounded e)
    {k : Exp3} (hk : bounded k) (h : encode k ∈ q.map encode) : k ∈ q := by
  obtain ⟨e, he, hc⟩ := List.mem_map.mp h
  have heq : e = k := encode_inj (hq e he) hk hc
  simpa [heq] using he

lemma downward_nat (P : ℕ → Prop) (hP : ∀ n, P (n+1) → P n) :
    ∀ u, P u → ∀ k, k ≤ u → P k := by
  intro u
  induction u with
  | zero =>
    intro hu k hk
    have heq : k = 0 := by omega
    simpa [heq] using hu
  | succ u ih =>
    intro hu k hk
    by_cases heq : k = u+1
    · simpa [heq] using hu
    · exact ih (hP u hu) k (by omega)

 theorem lower_closed_of_steps (q : List Exp3)
    (h0 : ∀ u v t, exponentTriple (u+1) v t ∈ q → exponentTriple u v t ∈ q)
    (h1 : ∀ u v t, exponentTriple u (v+1) t ∈ q → exponentTriple u v t ∈ q)
    (h2 : ∀ u v t, exponentTriple u v (t+1) ∈ q → exponentTriple u v t ∈ q) :
    ∀ e ∈ q, ∀ k : Exp3, (∀ j, k j ≤ e j) → k ∈ q := by
  intro e he k hk
  have heq : exponentTriple (e 0) (e 1) (e 2) = e := by
    funext j; fin_cases j <;> rfl
  have hstart : exponentTriple (e 0) (e 1) (e 2) ∈ q := by simpa [heq] using he
  have hfirst := downward_nat (fun u => exponentTriple u (e 1) (e 2) ∈ q)
    (fun u => h0 u (e 1) (e 2)) (e 0) hstart (k 0) (hk 0)
  have hsecond := downward_nat (fun v => exponentTriple (k 0) v (e 2) ∈ q)
    (fun v => h1 (k 0) v (e 2)) (e 1) hfirst (k 1) (hk 1)
  have hthird := downward_nat (fun t => exponentTriple (k 0) (k 1) t ∈ q)
    (fun t => h2 (k 0) (k 1) t) (e 2) hsecond (k 2) (hk 2)
  have hkq : exponentTriple (k 0) (k 1) (k 2) = k := by
    funext j; fin_cases j <;> rfl
  simpa [hkq] using hthird

/-- Only immediate predecessors need finite numerical checking. A bit mask
provides constant-sized membership witnesses, with a proved list interpretation. -/
 theorem lower_closed_of_mask (q : List Exp3) (M : ℕ)
    (hmask : natMask (q.map encode) = M) (hbound : ∀ e ∈ q, bounded e)
    (h0 : ∀ e ∈ q, 0 < e 0 →
      M.testBit (encode (exponentTriple (e 0-1) (e 1) (e 2))) = true)
    (h1 : ∀ e ∈ q, 0 < e 1 →
      M.testBit (encode (exponentTriple (e 0) (e 1-1) (e 2))) = true)
    (h2 : ∀ e ∈ q, 0 < e 2 →
      M.testBit (encode (exponentTriple (e 0) (e 1) (e 2-1))) = true) :
    ∀ e ∈ q, ∀ k : Exp3, (∀ j, k j ≤ e j) → k ∈ q := by
  have hmem {k : Exp3} (hk : bounded k) (hbit : M.testBit (encode k) = true) : k ∈ q := by
    apply mem_of_code q hbound hk
    apply (natMask_mem (q.map encode) (encode k)).mp
    simpa [hmask] using hbit
  apply lower_closed_of_steps
  · intro u v t he
    have hb := hbound _ he
    apply hmem
    · simp [bounded, exponentTriple] at hb ⊢
      omega
    · simpa [exponentTriple] using h0 _ he (by simp [exponentTriple])
  · intro u v t he
    have hb := hbound _ he
    apply hmem
    · simp [bounded, exponentTriple] at hb ⊢
      omega
    · simpa [exponentTriple] using h1 _ he (by simp [exponentTriple])
  · intro u v t he
    have hb := hbound _ he
    apply hmem
    · simp [bounded, exponentTriple] at hb ⊢
      omega
    · simpa [exponentTriple] using h2 _ he (by simp [exponentTriple])
end ThomsonNine.Interval.SparsePolynomial.Collected

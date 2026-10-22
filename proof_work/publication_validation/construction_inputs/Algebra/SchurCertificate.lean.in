import ThomsonNine.Construction.Algebra.IntervalSchur
import ThomsonNine.IntervalInverse

-- Isolated source: Algebra.SchurCertificate
noncomputable section
namespace ThomsonNine.FixedInterval.Schur
open ThomsonNine.Interval (RatInterval)

def Contains (outer inner : Bounds) : Prop := outer.lo≤ inner.lo ∧ inner.hi≤outer.hi
theorem mem_contains {s : ℤ} {outer inner : Bounds} {x : ℝ}
    (h : Contains outer inner) (hx : Mem s inner x) : Mem s outer x := by
  have hl : (outer.lo : ℝ)≤ inner.lo := by exact_mod_cast h.1
  have hh : (inner.hi : ℝ)≤outer.hi := by exact_mod_cast h.2
  exact ⟨hl.trans hx.1,hx.2.trans hh⟩
def InverseRule (s : ℤ) (I J : Bounds) : Prop := ∀ x : ℝ, Mem s I x → x≠0 ∧ Mem s J x⁻¹

theorem inverseRule_of_rat {s : ℤ} (hs : 0<s) (I J : Bounds) (K L : RatInterval)
    (hSourceLo : (s : ℚ)*K.lo≤I.lo) (hSourceHi : (I.hi : ℚ)≤(s : ℚ)*K.hi)
    (hSign : 0<K.lo ∨ K.hi<0) (hInvLo : L.lo≤1/K.hi) (hInvHi : 1/K.lo≤L.hi)
    (hTargetLo : (J.lo : ℚ)≤(s : ℚ)*L.lo) (hTargetHi : (s : ℚ)*L.hi≤J.hi) :
    InverseRule s I J := by
  intro x hx
  have hk := mem_to_rat hx hs hSourceLo hSourceHi
  have hne : x≠0 := by
    rcases hSign with hp | hn
    · have hp' : (0 : ℝ)<K.lo := by exact_mod_cast hp
      have := hp'.trans_le hk.1
      exact ne_of_gt this
    · have hn' : (K.hi : ℝ)<0 := by exact_mod_cast hn
      exact ne_of_lt (hk.2.trans_lt hn')
  exact ⟨hne,mem_of_rat (Interval.RatInterval.mem_inv_of_bounds hk hSign hInvLo hInvHi) hs hTargetLo hTargetHi⟩

def Sound {n : ℕ} (s : ℤ) (IA : Fin n → Fin n → Bounds) (Ib Ix : Fin n → Bounds) : Prop :=
  ∀ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
    (∀ i j, Mem s (IA i j) (A i j)) → (∀ i, Mem s (Ib i) (b i)) →
    ∃ x : Fin n → ℝ, A.mulVec x=b ∧ ∀ i, Mem s (Ix i) (x i)

theorem empty_sound (s : ℤ) (IA : Fin 0 → Fin 0 → Bounds) (Ib Ix : Fin 0 → Bounds) :
    Sound s IA Ib Ix := by
  intro A b hA hb
  refine ⟨Fin.elim0,?_,?_⟩
  · funext i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

theorem step_sound {n : ℕ} {s : ℤ} (hs : 0<s)
    (IA : Fin (n+1) → Fin (n+1) → Bounds) (Ib Ix : Fin (n+1) → Bounds) (iv : Bounds)
    (JA : Fin n → Fin n → Bounds) (Jb Jx : Fin n → Bounds)
    (hInv : InverseRule s (IA 0 0) iv)
    (hNextA : ∀ i j, Contains (JA i j) (reducedMatrix s IA iv i j))
    (hNextB : ∀ i, Contains (Jb i) (reducedRhs s IA Ib iv i))
    (hNext : Sound s JA Jb Jx)
    (hOutput : ∀ i, Contains (Ix i) (recover s IA Ib iv Jx i)) : Sound s IA Ib Ix := by
  intro A b hA hb
  have hi := hInv (A 0 0) (hA 0 0)
  have hJA : ∀ i j, Mem s (JA i j) (SchurSolve.reducedMatrix A i j) :=
    fun i j => mem_contains (hNextA i j) (reducedMatrix_mem hs IA A hA iv hi.2 i j)
  have hJb : ∀ i, Mem s (Jb i) (SchurSolve.reducedRhs A b i) :=
    fun i => mem_contains (hNextB i) (reducedRhs_mem hs IA A Ib b hA hb iv hi.2 i)
  obtain ⟨tail,ht,htmem⟩ := hNext (SchurSolve.reducedMatrix A) (SchurSolve.reducedRhs A b) hJA hJb
  refine ⟨SchurSolve.recover A b tail,SchurSolve.recover_solves A b hi.1 tail ht,?_⟩
  intro i
  exact mem_contains (hOutput i) (recover_mem hs IA A Ib b hA hb iv hi.2 Jx tail htmem i)
end ThomsonNine.FixedInterval.Schur

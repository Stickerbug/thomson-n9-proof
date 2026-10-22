import LocalShift.GraphNonnegative

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.LocalShift
open ThomsonNine.Interval.SparsePolynomial ThomsonNine.ActualLocalAAA
attribute [local irreducible] entries ActualR.residual
open scoped BigOperators

theorem boundary_extension (localId : Fin 12)
    (sourceBox relativeBox : Fin 3 → Interval.RatInterval) (expanded : Interval.RatInterval)
    (hunit : ∀ v t, (sourceBox 1).mem v → (sourceBox 2).mem t → 0<1-v^2 ∧ 0<1-t^2)
    (hsource : ∀ u, (sourceBox 0).mem u → expanded.mem u)
    (hgraph_box : ∀ v t, (sourceBox 1).mem v → (sourceBox 2).mem t → expanded.mem (LocalLDL.lowerGraph v t))
    (hrelative : ∀ p : Fin 3 → ℝ, expanded.mem (p 0) → (sourceBox 1).mem (p 1) → (sourceBox 2).mem (p 2) →
      ∀ a, (relativeBox a).mem (p a-center localId a))
    (hpos : ∀ x : Fin 3 → ℝ, (∀ a, (relativeBox a).mem (x a)) → 0≤translatedGradient localId x 0)
    (hgraph : ∀ v t, (sourceBox 1).mem v → (sourceBox 2).mem t → 0≤ActualR.residual (GramGraph.point v t))
    (p : Fin 3 → ℝ) (hp : ∀ a, (sourceBox a).mem (p a))
    (hg : 0≤Semantics.gram (p 0) (p 1) (p 2)) : 0≤ActualR.residual p := by
  let v := p 1
  let t := p 2
  let b := LocalLDL.lowerGraph v t
  let curve : ℝ → (Fin 3 → ℝ) := fun u a => (![u,v,t] a)-center localId a
  let f : ℝ → ℝ := fun u => eval Entry.exp (fun E => family3 localId E.index) (curve u) entries
  let f' : ℝ → ℝ := fun u => translatedGradient localId (curve u) 0
  have hcurve (u : ℝ) (a : Fin 3) : HasDerivAt (fun q => curve q a) (![1,0,0] a) u := by
    fin_cases a
    · convert (hasDerivAt_id' u).sub_const (center localId 0) using 1
      · funext q;rfl
      · rfl
    · exact hasDerivAt_const u (v-center localId 1)
    · exact hasDerivAt_const u (t-center localId 2)
  have hd (u : ℝ) : HasDerivAt f (f' u) u := by
    have h := eval_curve_derivative Entry.exp (fun E => family3 localId E.index) entries curve ![1,0,0] u (hcurve u)
    simpa only [f,f',directionalDerivative,translatedGradient,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      mul_one,mul_zero,add_zero] using h
  have he : f=(fun u => ActualR.residual ![u,v,t]) := by
    funext u
    have h := congrFun (entries_function_eq localId) (curve u)
    dsimp only [translate,curve] at h
    convert h using 1
    congr 1
    funext a
    ring
  have hbound : ∀ u∈Set.Icc (expanded.lo : ℝ) (expanded.hi : ℝ), 0≤f' u := by
    intro u hu
    apply hpos (curve u)
    exact hrelative ![u,v,t] hu (hp 1) (hp 2)
  have hu := hunit v t (hp 1) (hp 2)
  have hvunit : -1≤v ∧ v≤1 := by constructor <;> nlinarith [hu.1]
  have htunit : -1≤t ∧ t≤1 := by constructor <;> nlinarith [hu.2]
  have hbu : b≤p 0 := (LocalLDL.feasible_between_graphs hvunit htunit hg).1
  have hbpos : 0≤f b := by
    rw [he]
    exact hgraph v t (hp 1) (hp 2)
  have h := LocalLDL.nonneg_above_boundary
    (D:=Set.Icc (expanded.lo : ℝ) (expanded.hi : ℝ)) (f:=f) (f':=f')
    (b:=b) (u:=p 0) (convex_Icc _ _)
    (fun u hu => (hd u).continuousAt.continuousWithinAt)
    (fun u hu => hd u) (fun u hu => hbound u (interior_subset hu))
    (hgraph_box v t (hp 1) (hp 2)) (hsource (p 0) (hp 0)) hbu hbpos
  rw [he] at h
  have hpvec : ![p 0,p 1,p 2]=p := by funext a;fin_cases a <;> rfl
  change 0≤ActualR.residual ![p 0,p 1,p 2] at h
  rw [hpvec] at h
  exact h
end ThomsonNine.LocalShift

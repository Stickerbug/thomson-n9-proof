import LocalShift.BoundaryGeometry
import LocalShift.EntryModel
import Algebra.SparseAcceleration
import ThomsonNine.LocalNonneg

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.LocalShift
open ThomsonNine.Interval.SparsePolynomial ThomsonNine.ActualLocalAAA
open scoped BigOperators
attribute [local irreducible] entries ActualR.residual
def translatedGradient (localId : Fin 12) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => formalDerivative Entry.exp (fun E => family3 localId E.index) i x entries
def translatedHessian (localId : Fin 12) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => formalHessianEntry Entry.exp (fun E => family3 localId E.index) i j x entries
def relativeGraph (localId : Fin 12) (v t : ℝ) : Fin 3 → ℝ :=
  fun a => GramGraph.point v t a-center localId a

theorem graph_nonnegative (localId : Fin 12) (hb : IsBoundary localId)
    (box : Fin 3 → Interval.RatInterval)
    (hcenter : ∀ a, (box a).mem (center localId a))
    (hunit : ∀ v t, (box 1).mem v → (box 2).mem t → 0<1-v^2 ∧ 0<1-t^2)
    (hH : ∀ v t, (box 1).mem v → (box 2).mem t → ∀ w : Fin 2 → ℝ,
      0≤∑ i : Fin 2, ∑ j : Fin 2,
        GramGraph.hessian (translatedHessian localId (relativeGraph localId v t))
          (translatedGradient localId (relativeGraph localId v t) 0) v t i j*w j*w i)
    (v t : ℝ) (hv : (box 1).mem v) (ht : (box 2).mem t) :
    0≤ActualR.residual (GramGraph.point v t) := by
  let y := v-center localId 1
  let z := t-center localId 2
  let V : ℝ → ℝ := fun s => center localId 1+s*y
  let T : ℝ → ℝ := fun s => center localId 2+s*z
  let curve : ℝ → (Fin 3 → ℝ) := fun s => relativeGraph localId (V s) (T s)
  let velocity : ℝ → (Fin 3 → ℝ) := fun s => GramGraph.velocity (V s) (T s) y z
  let acc : ℝ → (Fin 3 → ℝ) := fun s => GramGraph.acceleration (V s) (T s) y z
  let f : ℝ → ℝ := fun s => eval Entry.exp (fun E => family3 localId E.index) (curve s) entries
  let f' : ℝ → ℝ := fun s => directionalDerivative Entry.exp (fun E => family3 localId E.index) (curve s) (velocity s) entries
  let f'' : ℝ → ℝ := fun s => directionalHessian Entry.exp (fun E => family3 localId E.index) (curve s) (velocity s) entries+
    directionalDerivative Entry.exp (fun E => family3 localId E.index) (curve s) (acc s) entries
  have hV (s : ℝ) : HasDerivAt V y s := by
    convert (hasDerivAt_const s (center localId 1)).add ((hasDerivAt_id' s).mul_const y) using 1 <;> simp
  have hT (s : ℝ) : HasDerivAt T z s := by
    convert (hasDerivAt_const s (center localId 2)).add ((hasDerivAt_id' s).mul_const z) using 1 <;> simp
  have hseg {a x : ℝ} (axis : Fin 3) (ha : (box axis).mem a) (hx : (box axis).mem x)
      (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) : (box axis).mem (a+s*(x-a)) := by
    have h := (convex_Icc ((box axis).lo : ℝ) ((box axis).hi : ℝ)).lineMap_mem ha hx hs
    change ((box axis).lo : ℝ)≤a+s*(x-a) ∧ a+s*(x-a)≤((box axis).hi : ℝ)
    simpa only [AffineMap.lineMap_apply,smul_eq_mul,vsub_eq_sub,vadd_eq_add,Set.mem_Icc,add_comm] using h
  have hvs (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) : (box 1).mem (V s) :=
    hseg 1 (hcenter 1) hv s hs
  have hts (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) : (box 2).mem (T s) :=
    hseg 2 (hcenter 2) ht s hs
  have hdcurve (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) (a : Fin 3) :
      HasDerivAt (fun q => curve q a) (velocity s a) s := by
    have hu := hunit _ _ (hvs s hs) (hts s hs)
    convert (GramGraph.point_derivative V T y z s (hV s) (hT s) hu.1 hu.2 a).sub_const (center localId a) using 1
    funext q
    rfl
  have hdvel (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) (a : Fin 3) :
      HasDerivAt (fun q => velocity q a) (acc s a) s := by
    have hu := hunit _ _ (hvs s hs) (hts s hs)
    exact GramGraph.velocity_derivative V T y z s (hV s) (hT s) hu.1 hu.2 a
  have hd (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) : HasDerivAt f (f' s) s :=
    eval_curve_derivative Entry.exp (fun E => family3 localId E.index) entries curve (velocity s) s (hdcurve s hs)
  have hdd (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) : HasDerivAt f' (f'' s) s :=
    variable_directionalDerivative_curve Entry.exp (fun E => family3 localId E.index) entries curve velocity (acc s) s (hdcurve s hs) (hdvel s hs)
  have he : f=(fun s => ActualR.residual (GramGraph.point (V s) (T s))) := by
    funext s
    have h := congrFun (entries_function_eq localId) (curve s)
    dsimp only [translate,curve,relativeGraph] at h
    convert h using 1
    congr 1
    funext a
    ring
  have hc : GramGraph.point (V 0) (T 0)=center localId := by
    simpa only [V,T,zero_mul,add_zero] using center_graph localId hb
  have hfzero : f 0=0 := by
    rw [he]
    change ActualR.residual (GramGraph.point (V 0) (T 0))=0
    rw [hc]
    exact center_value_zero localId
  have hderzero : HasDerivAt f 0 0 := by
    rw [he]
    have hu := hunit _ _ (hcenter 1) (hcenter 2)
    apply center_curve_derivative_zero_of_tangent localId hb _ (velocity 0) hc
    · intro a
      exact GramGraph.point_derivative V T y z 0 (hV 0) (hT 0) (by simpa only [V,zero_mul,add_zero] using hu.1)
        (by simpa only [T,zero_mul,add_zero] using hu.2) a
    · rw [← hc]
      exact GramGraph.gram_tangent _ _ y z (by simpa only [V,zero_mul,add_zero] using hu.1)
        (by simpa only [T,zero_mul,add_zero] using hu.2)
  have hnonneg (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) : 0≤f'' s := by
    have h := hH (V s) (T s) (hvs s hs) (hts s hs) ![y,z]
    have hid := GramGraph.quadratic_identity (translatedHessian localId (curve s))
      (translatedGradient localId (curve s) 0) (V s) (T s) y z
    have heq : f'' s=∑ i : Fin 2, ∑ j : Fin 2,
        GramGraph.hessian (translatedHessian localId (curve s))
          (translatedGradient localId (curve s) 0) (V s) (T s) i j*(![y,z] j)*(![y,z] i) := by
      rw [← hid]
      simp only [f'',directionalDerivative,directionalHessian,translatedHessian,translatedGradient,velocity,Fin.sum_univ_three,acc,GramGraph.acceleration,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
        mul_zero,add_zero]
    rw [heq]
    exact h
  have h := LocalLDL.segment_nonneg_of_second_derivative
    (f:=f) (f':=f') (f'':=f'')
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (interior_subset hs)) (fun s hs => hdd s (interior_subset hs))
    (fun s hs => hnonneg s (interior_subset hs)) hfzero hderzero
    1 (by constructor <;> norm_num)
  rw [he] at h
  simpa only [V,T,y,z,one_mul,add_sub_cancel] using h
end ThomsonNine.LocalShift

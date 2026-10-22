import ThomsonNine.Construction.Algebra.GramGraph
import ThomsonNine.Construction.Algebra.SparseAcceleration
import ThomsonNine.Construction.Contact.Model

-- Isolated source: Algebra.GramCurve
noncomputable section
namespace ThomsonNine.GramGraph
open ThomsonNine.ContactJet
open scoped BigOperators
def point (v t : ℝ) : Point := ![LocalLDL.lowerGraph v t,v,t]
def velocity (v t y z : ℝ) : Point := ![slope v t*y+slope t v*z,y,z]
def acceleration (v t y z : ℝ) : Point :=
  ![curvatureVV v t*y^2+2*curvatureVT v t*y*z+curvatureVV t v*z^2,0,0]
def jacobian (v t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![slope v t,slope t v;1,0;0,1]
def curvature (v t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![curvatureVV v t,curvatureVT v t;curvatureVT v t,curvatureVV t v]
def hessian (H : Matrix (Fin 3) (Fin 3) ℝ) (Ru v t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (jacobian v t).transpose * H * jacobian v t + Ru • curvature v t

theorem point_derivative (V T : ℝ → ℝ) (y z s : ℝ)
    (hV : HasDerivAt V y s) (hT : HasDerivAt T z s)
    (hv : 0<1-(V s)^2) (ht : 0<1-(T s)^2) (a : Fin 3) :
    HasDerivAt (fun q => point (V q) (T q) a) (velocity (V s) (T s) y z a) s := by
  fin_cases a
  · exact lowerGraph_derivative V T y z s hV hT hv ht
  · exact hV
  · exact hT

theorem velocity_derivative (V T : ℝ → ℝ) (y z s : ℝ)
    (hV : HasDerivAt V y s) (hT : HasDerivAt T z s)
    (hv : 0<1-(V s)^2) (ht : 0<1-(T s)^2) (a : Fin 3) :
    HasDerivAt (fun q => velocity (V q) (T q) y z a) (acceleration (V s) (T s) y z a) s := by
  fin_cases a
  · have h := ((slope_derivative V T y z s hV hT hv ht).mul_const y).add
      ((slope_derivative T V z y s hT hV ht hv).mul_const z)
    convert h using 1
    · rfl
    · change curvatureVV (V s) (T s)*y^2+2*curvatureVT (V s) (T s)*y*z+curvatureVV (T s) (V s)*z^2=
        (curvatureVV (V s) (T s)*y+curvatureVT (V s) (T s)*z)*y+
        (curvatureVV (T s) (V s)*z+curvatureVT (T s) (V s)*y)*z
      simp only [curvatureVT,radical_swap (T s) (V s)]
      ring
  · exact hasDerivAt_const s y
  · exact hasDerivAt_const s z

theorem gram_tangent (v t y z : ℝ) (hv : 0<1-v^2) (ht : 0<1-t^2) :
    (∑ a : Fin 3, ActualContact.gramGradient (point v t) a*velocity v t y z a)=0 := by
  have hs := ne_of_gt (radical_pos hv ht)
  simp only [Fin.sum_univ_three,ActualContact.gramGradient,point,velocity,slope,
    LocalLDL.lowerGraph,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Fin.reduceAdd]
  rw [radical_swap t v]
  change _+_+_=0
  dsimp only [radical] at hs ⊢
  field_simp
  ring

theorem quadratic_identity (H : Matrix (Fin 3) (Fin 3) ℝ) (Ru v t y z : ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, H i j*velocity v t y z j*velocity v t y z i)+
      Ru*acceleration v t y z 0=
      ∑ a : Fin 2, ∑ b : Fin 2, hessian H Ru v t a b*(![y,z] b)*(![y,z] a) := by
  simp only [hessian,jacobian,curvature,velocity,acceleration,Matrix.mul_apply,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.transpose_apply,Matrix.of_apply,
    Fin.sum_univ_three,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  ring
end ThomsonNine.GramGraph

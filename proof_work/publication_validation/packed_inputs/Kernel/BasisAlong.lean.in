import Kernel.BasisJet
import Algebra.JetAlong
noncomputable section
namespace ThomsonNine.ActualKernel.BasisJet
open ThomsonNine.ContactJet

theorem feature_along (x : Point) (k i : Fin 11) (axis : Fin 3) :
    AlongCorrect (fun y => feature k i (y axis)) x (featureJet x k i axis) :=
  along_horner (along_coordinate x axis) (coefficients k i)
theorem pair_along (x : Point) (k i j : Fin 11) (a b : Fin 3) :
    AlongCorrect (fun y => pairFeature k i j (y a) (y b)) x (pairJet x k i j a b) := by
  by_cases h : i=j
  · simpa only [pairFeature,pairJet,h,ite_true] using
      ((feature_along x k i a).mul (feature_along x k j b)).add (along_constant 0 x)
  · simpa only [pairFeature,pairJet,h,ite_false] using
      ((feature_along x k i a).mul (feature_along x k j b)).add
        ((feature_along x k j a).mul (feature_along x k i b))
theorem raw_along (x : Point) (k i j : Fin 11) (σ : Fin 3 → Fin 3) :
    AlongCorrect (rawFunction k i j σ) x (rawJet x k i j σ) :=
  ((along_q (along_coordinate x (σ 0)) (along_coordinate x (σ 1)) (along_coordinate x (σ 2)) k).mul
    (pair_along x k i j (σ 0) (σ 1))).mul (along_constant (1/6) x)
theorem basis_along (x : Point) (k i j : Fin 11) :
    AlongCorrect (basisFunction k i j) x (basisJet x k i j) :=
  along_sum permutations (rawFunction k i j) (rawJet x k i j) x (fun _ _ => raw_along x k i j _)
end ThomsonNine.ActualKernel.BasisJet

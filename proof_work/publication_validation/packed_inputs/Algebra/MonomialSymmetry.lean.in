import Algebra.QPolynomials
import Kernel.QCacheData
import Mathlib.Data.List.OfFn

noncomputable section
namespace ThomsonNine.MonomialSymmetry
open ThomsonNine.QPolynomial
open ThomsonNine.ActualKernel.QCache

def inverse : Fin 6 → Fin 6 := ![0,1,2,4,3,5]
theorem permutation_inverse : ∀ σ : Fin 6, ∀ i : Fin 3, permutation (inverse σ) (permutation σ i)=i := by decide +kernel

theorem shifted_monomial (e : Exponent) (a b : ℕ) (σ : Fin 6) (u v t : ℝ) :
    monomial (fun i => (![e 0+a,e 1+b,e 2] : Exponent) (permutation (inverse σ) i)) u v t =
      (![u,v,t] (permutation σ 0))^a*(![u,v,t] (permutation σ 1))^b*
        monomial e (![u,v,t] (permutation σ 0)) (![u,v,t] (permutation σ 1)) (![u,v,t] (permutation σ 2)) := by
  fin_cases σ <;> simp [inverse,permutation,monomial,pow_add] <;> ring

theorem list_indexed_sum {α : Type*} (l : List α) (default : α) (f : α → ℝ) :
    ((List.finRange l.length).map (fun i => f ((l[i.val]?).getD default))).sum=(l.map f).sum := by
  have h : (List.finRange l.length).map (fun i => f ((l[i.val]?).getD default))=l.map f := by
    rw [← List.ofFn_eq_map]
    have hget (i : Fin l.length) : ((l[i.val]?).getD default)=l[i.val] := by
      rw [List.getElem?_eq_getElem i.isLt]
      rfl
    simpa only [hget] using List.ofFn_getElem_eq_map l f
  rw [h]

theorem finRange_sum (n : ℕ) (f : Fin n → ℝ) :
    ((List.finRange n).map f).sum=∑ i : Fin n, f i := by
  have h := List.sum_toFinset f (List.nodup_finRange n)
  have he : (List.finRange n).toFinset=(Finset.univ : Finset (Fin n)) := by ext i; simp
  rw [← h,he]

theorem flatMap_sum_map {α β : Type*} (l : List α) (g : α → List β) (f : β → ℝ) :
    ((l.flatMap g).map f).sum=(l.map (fun a => ((g a).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]
theorem map_mul_sum {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map (fun i => c*f i)).sum=c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,mul_add]
end ThomsonNine.MonomialSymmetry

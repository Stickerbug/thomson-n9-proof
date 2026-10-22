import R.Model
import Algebra.FiniteCollector

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualR.Collection
open ThomsonNine.ActualR.Data
open scoped BigOperators

def hId (a : Fin 3) (n : Fin 28) : ℕ := a.val*28+n.val
def fId (j : Fin 756) : ℕ := 84+j.val
def dId (a : Fin 3) (j : Fin 756) : ℕ := 840+a.val*756+j.val
def sourceCoefficient (H : Fin 28 → ℝ) (F : Fin 756 → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  if n<84 then H ⟨n%28,Nat.mod_lt _ (by decide)⟩
  else if n<840 then -7*F ⟨(n-84)%756,Nat.mod_lt _ (by decide)⟩
  else if n<3108 then -F ⟨(n-840)%756,Nat.mod_lt _ (by decide)⟩
  else -c
theorem source_h (H : Fin 28 → ℝ) (F : Fin 756 → ℝ) (c : ℝ) (a : Fin 3) (n : Fin 28) :
    sourceCoefficient H F c (hId a n)=H n := by
  have hb : hId a n<84 := by unfold hId; omega
  have he : (⟨hId a n%28,Nat.mod_lt _ (by decide)⟩ : Fin 28)=n := by
    apply Fin.ext
    dsimp [hId]
    omega
  simp only [sourceCoefficient,if_pos hb,he]
theorem source_f (H : Fin 28 → ℝ) (F : Fin 756 → ℝ) (c : ℝ) (j : Fin 756) :
    sourceCoefficient H F c (fId j)= -7*F j := by
  have ha : ¬fId j<84 := by unfold fId; omega
  have hb : fId j<840 := by unfold fId; omega
  have he : (⟨(fId j-84)%756,Nat.mod_lt _ (by decide)⟩ : Fin 756)=j := by
    apply Fin.ext
    dsimp [fId]
    omega
  simp only [sourceCoefficient,if_neg ha,if_pos hb,he]
theorem source_d (H : Fin 28 → ℝ) (F : Fin 756 → ℝ) (c : ℝ) (a : Fin 3) (j : Fin 756) :
    sourceCoefficient H F c (dId a j)= -F j := by
  have ha : ¬dId a j<84 := by unfold dId; omega
  have hb : ¬dId a j<840 := by unfold dId; omega
  have hd : dId a j<3108 := by unfold dId; omega
  have he : (⟨(dId a j-840)%756,Nat.mod_lt _ (by decide)⟩ : Fin 756)=j := by
    apply Fin.ext
    dsimp [dId]
    omega
  simp only [sourceCoefficient,if_neg ha,if_neg hb,if_pos hd,he]
theorem source_c (H : Fin 28 → ℝ) (F : Fin 756 → ℝ) (c : ℝ) :
    sourceCoefficient H F c 3108= -c := by norm_num [sourceCoefficient]

def axisExponent (a : Fin 3) (n : ℕ) : Fin 3 → ℕ := fun j => if j=a then n else 0
def sourceExponent (n : ℕ) : Fin 3 → ℕ :=
  if n<84 then axisExponent ⟨(n/28)%3,Nat.mod_lt _ (by decide)⟩ (n%28)
  else if n<840 then ActualF.Data.support ⟨(n-84)%756,Nat.mod_lt _ (by decide)⟩
  else if n<3108 then
    let j : Fin 756 := ⟨(n-840)%756,Nat.mod_lt _ (by decide)⟩
    axisExponent ⟨((n-840)/756)%3,Nat.mod_lt _ (by decide)⟩
      (ActualF.Data.support j 1+ActualF.Data.support j 2)
  else fun _ => 0
theorem exponent_h (a : Fin 3) (n : Fin 28) : sourceExponent (hId a n)=axisExponent a n := by
  have hb : hId a n<84 := by unfold hId; omega
  have ha : (⟨(hId a n/28)%3,Nat.mod_lt _ (by decide)⟩ : Fin 3)=a := by
    apply Fin.ext
    dsimp [hId]
    omega
  have hn : hId a n%28=n.val := by unfold hId; omega
  simp only [sourceExponent,if_pos hb,ha,hn]
theorem exponent_f (j : Fin 756) : sourceExponent (fId j)=ActualF.Data.support j := by
  have ha : ¬fId j<84 := by unfold fId; omega
  have hb : fId j<840 := by unfold fId; omega
  have he : (⟨(fId j-84)%756,Nat.mod_lt _ (by decide)⟩ : Fin 756)=j := by
    apply Fin.ext
    dsimp [fId]
    omega
  simp only [sourceExponent,if_neg ha,if_pos hb,he]
theorem exponent_d (a : Fin 3) (j : Fin 756) :
    sourceExponent (dId a j)=axisExponent a (ActualF.Data.support j 1+ActualF.Data.support j 2) := by
  have ha : ¬dId a j<84 := by unfold dId; omega
  have hb : ¬dId a j<840 := by unfold dId; omega
  have hd : dId a j<3108 := by unfold dId; omega
  have he : (⟨(dId a j-840)%756,Nat.mod_lt _ (by decide)⟩ : Fin 756)=j := by
    apply Fin.ext
    dsimp [dId]
    omega
  have heA : (⟨((dId a j-840)/756)%3,Nat.mod_lt _ (by decide)⟩ : Fin 3)=a := by
    apply Fin.ext
    dsimp [dId]
    omega
  simp only [sourceExponent,if_neg ha,if_neg hb,if_pos hd,he,heA]
theorem exponent_c : sourceExponent 3108=(fun _ => 0) := by norm_num [sourceExponent]

def axisChoice (j : Fin 807) : Fin 3 :=
  if Data.sourceExponent j 0≠0 then 0 else if Data.sourceExponent j 1≠0 then 1 else 2
def axes (j : Fin 807) : List (Fin 3) := if j=0 then [0,1,2] else [axisChoice j]
def hGroup (j : Fin 807) : List ℕ :=
  (axes j).flatMap (fun a => (pureDegree j).toList.map (hId a))
def fGroup (j : Fin 807) : List ℕ := (Findex j).toList.map fId
def dGroup (j : Fin 807) : List ℕ :=
  (axes j).flatMap (fun a => (pureDegree j).toList.flatMap (fun n => (diagonalIndices n).map (dId a)))
def cGroup (j : Fin 807) : List ℕ := if j=0 then [3108] else []
def groups (j : Fin 807) : List ℕ := hGroup j++fGroup j++dGroup j++cGroup j
end ThomsonNine.ActualR.Collection

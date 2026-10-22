import MainCoverage.TreeModel
import PackedTensor.TensorModel

noncomputable section
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor

def left (level index : ℕ) : ℝ := -1+(39/25 : ℝ)*(index : ℝ)/(2:ℝ)^level
def width (level : ℕ) : ℝ := (39/25 : ℝ)/(2:ℝ)^level
def point (level index : ℕ) (t : ℝ) : ℝ := left level index+width level*t
def boxPoint (s : State) (z : Fin 3 → ℝ) : Fin 3 → ℝ := fun a => point (s.levels a) (s.indices a) (z a)
def valid (s : State) : Prop := ∀ a, s.indices a<2^(s.levels a)

theorem width_pos (level : ℕ) : 0<width level := div_pos (by norm_num) (pow_pos (by norm_num) _)
theorem low_cast (s : State) (a : Fin 3) : (low s a : ℝ)=left (s.levels a) (s.indices a) := by
  simp [low,left,Nat.shiftLeft_eq]
theorem high_cast (s : State) (a : Fin 3) : (high s a : ℝ)=left (s.levels a) (s.indices a)+width (s.levels a) := by
  simp [high,left,width,Nat.shiftLeft_eq,Nat.cast_add,Nat.cast_one]
  ring

theorem point_bounds (s : State) (z : Fin 3 → ℝ) (hz : ∀ a, 0≤z a ∧ z a≤1) (a : Fin 3) :
    (low s a : ℝ)≤boxPoint s z a ∧ boxPoint s z a≤(high s a : ℝ) := by
  rw [low_cast,high_cast]
  have hw := width_pos (s.levels a)
  dsimp only [boxPoint,point]
  constructor <;> nlinarith [(hz a).1,(hz a).2]

theorem point_split (level index : ℕ) (side : Bool) (t : ℝ) :
    point (level+1) (2*index+(if side then 1 else 0)) t=
      point level index ((if side then 1+t else t)/2) := by
  cases side <;> simp [point,left,width,pow_succ,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem box_child (s : State) (mask : ℕ) (side : Bool) (z : Fin 3 → ℝ) :
    boxPoint (child s mask side) z=boxPoint s (halfPoint (splitAxis s) side z) := by
  funext a
  by_cases ha : a=splitAxis s
  · subst a
    simp only [boxPoint,child,Function.update_self,halfPoint]
    exact point_split _ _ side _
  · simp only [boxPoint,child,Function.update_of_ne ha,halfPoint]

theorem child_valid (s : State) (mask : ℕ) (side : Bool) (h : valid s) : valid (child s mask side) := by
  intro a
  by_cases ha : a=splitAxis s
  · subst a
    simp only [child,Function.update_self,pow_succ]
    have hi := h (splitAxis s)
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  · simpa only [child,Function.update_of_ne ha] using h a

def childCoordinates (a : Fin 3) (side : Bool) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Function.update z a (if side then 2*z a-1 else 2*z a)

theorem half_childCoordinates (a : Fin 3) (side : Bool) (z : Fin 3 → ℝ) :
    halfPoint a side (childCoordinates a side z)=z := by
  funext b
  by_cases hb : b=a
  · subst b
    cases side <;> simp [halfPoint,childCoordinates] <;> ring
  · simp [halfPoint,childCoordinates,Function.update_of_ne hb,hb]

theorem childCoordinates_mem (a : Fin 3) (z : Fin 3 → ℝ) (hz : ∀ b, 0≤z b ∧ z b≤1)
    (side : Bool) (hside : if side then (1:ℝ)/2≤z a else z a≤(1:ℝ)/2) :
    ∀ b, 0≤childCoordinates a side z b ∧ childCoordinates a side z b≤1 := by
  intro b
  by_cases hb : b=a
  · subst b
    cases side <;> simp only [childCoordinates,Function.update_self,Bool.false_eq_true,ite_false,ite_true] at *
    all_goals constructor <;> nlinarith [(hz a).1,(hz a).2]
  · simpa only [childCoordinates,Function.update_of_ne hb] using hz b

theorem boxPoint_root_range (s : State) (h : valid s) (z : Fin 3 → ℝ)
    (hz : ∀ a, 0≤z a ∧ z a≤1) (a : Fin 3) : -1≤boxPoint s z a ∧ boxPoint s z a≤14/25 := by
  have hi : (s.indices a : ℝ)+1≤(2:ℝ)^(s.levels a) := by exact_mod_cast (h a)
  have hn : (0:ℝ)≤s.indices a := Nat.cast_nonneg _
  have hp : (0:ℝ)<(2:ℝ)^(s.levels a) := pow_pos (by norm_num) _
  have h0 : -1≤left (s.levels a) (s.indices a) := by
    dsimp only [left]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hn) (le_of_lt hp))
  have h1 : left (s.levels a) (s.indices a)+width (s.levels a)≤(14:ℝ)/25 := by
    dsimp only [left,width]
    have he : -1+(39/25:ℝ)*(s.indices a : ℝ)/(2:ℝ)^(s.levels a)+(39/25:ℝ)/(2:ℝ)^(s.levels a)=
        -1+(39/25:ℝ)*((s.indices a : ℝ)+1)/(2:ℝ)^(s.levels a) := by ring
    rw [he]
    have hh := (div_le_iff₀ hp).mpr (show (39/25:ℝ)*((s.indices a : ℝ)+1)≤(39/25:ℝ)*(2:ℝ)^(s.levels a) by nlinarith)
    linarith
  have hb := point_bounds s z hz a
  rw [low_cast,high_cast] at hb
  exact ⟨h0.trans hb.1,hb.2.trans h1⟩

theorem order_leaf (s : State) (a b : Fin 3) (h : orderOK s a b=true)
    (z : Fin 3 → ℝ) (hz : ∀ c, 0≤z c ∧ z c≤1) (ho : Monotone (boxPoint s z)) : False := by
  have hp : a.val<b.val ∧ (s.indices b+1)*(1 <<< s.levels a)<s.indices a*(1 <<< s.levels b) :=
    of_decide_eq_true h
  have hcross : ((s.indices b : ℝ)+1)*(2:ℝ)^(s.levels a)<(s.indices a : ℝ)*(2:ℝ)^(s.levels b) := by
    have hh := hp.2
    simp only [Nat.shiftLeft_eq,one_mul] at hh
    exact_mod_cast hh
  have hpa : (0:ℝ)<(2:ℝ)^(s.levels a) := pow_pos (by norm_num) _
  have hpb : (0:ℝ)<(2:ℝ)^(s.levels b) := pow_pos (by norm_num) _
  have hd := (div_lt_div_iff₀ hpb hpa).mpr hcross
  have he : left (s.levels b) (s.indices b)+width (s.levels b)<left (s.levels a) (s.indices a) := by
    unfold left width
    have hb : (39/25:ℝ)*(s.indices b : ℝ)/(2:ℝ)^(s.levels b)+(39/25:ℝ)/(2:ℝ)^(s.levels b)=
        (39/25:ℝ)*(((s.indices b : ℝ)+1)/(2:ℝ)^(s.levels b)) := by ring
    rw [add_assoc,hb]
    have hm := mul_lt_mul_of_pos_left hd (by norm_num : (0:ℝ)<39/25)
    simpa only [div_eq_mul_inv,mul_assoc,add_comm] using add_lt_add_left hm (-1)
  have ha_bounds := point_bounds s z hz a
  have hb_bounds := point_bounds s z hz b
  rw [low_cast] at ha_bounds
  rw [high_cast] at hb_bounds
  have hab := ho (show a≤b from le_of_lt hp.1)
  linarith
end ThomsonNine.PackedMain

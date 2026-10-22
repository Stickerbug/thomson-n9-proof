import PackedTensor.Instances
import PackedTensor.Broadcast
import PackedRadix.Sum
import Mathlib.Data.Fin.VecNotation

set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix

def offset : ℕ := 1 <<< 125
def bound : ℕ := (1 <<< 126)-1
def scale : ℕ := 1 <<< 96
def block (bits : ℕ) : ℕ := (1 <<< bits)-1

structure AxisEntry where
  level : ℕ
  index : ℕ
  word : ℕ
deriving Inhabited

def axisValues (e : AxisEntry) (c : Fin 11) : ℕ := limb 128 e.word c.val
def spread (e : AxisEntry) (step : ℕ) : ℕ :=
  (List.finRange 11).foldl (fun out c => out + ((axisValues e c) <<< (128*step*c.val))) 0
def broadcast (e : AxisEntry) (axis : Fin 3) : ℕ :=
  if axis=0 then spread e 121*(block (128*121)/block 128)
  else if axis=1 then spread e 11*(block (128*11)/block 128)*(block (128*1331)/block (128*121))
  else e.word*(block (128*1331)/block (128*11))

structure State where
  depth : ℕ
  levels : Fin 3 → ℕ
  indices : Fin 3 → ℕ
  kernels : Fin 4 → ℕ
  gram : ℕ

inductive Tree where
  | positive (slot : Fin 4) (h0 h1 h2 : ℕ)
  | gram
  | order (a b : Fin 3)
  | local (id : ℕ)
  | split (mask : ℕ) (left right : Tree)
deriving Inhabited

def need : Tree → ℕ
  | .positive slot _ _ _ => 1 <<< slot.val
  | .gram => 16
  | .order _ _ => 0
  | .local _ => 0
  | .split mask _ _ => mask
def wanted (mask bit : ℕ) : Bool := mask.testBit bit
def splitAxis (s : State) : Fin 3 := ⟨s.depth%3,Nat.mod_lt _ (by omega)⟩
def child (s : State) (mask : ℕ) (side : Bool) : State :=
  let a := splitAxis s
  {depth := s.depth+1,
   levels := Function.update s.levels a (s.levels a+1),
   indices := Function.update s.indices a (2*s.indices a+(if side then 1 else 0)),
   kernels := fun q => if wanted mask q.val then half 1331 bound planes11 a side (s.kernels q) else 0,
   gram := if wanted mask 4 then half 27 bound planes3 a side s.gram else 0}

def stepOK (s : State) (mask : ℕ) (side : Bool) : Bool :=
  decide ((∀ q : Fin 4, wanted mask q.val=true → halfOK 1331 bound planes11 (splitAxis s) side (s.kernels q)=true) ∧
    (wanted mask 4=true → halfOK 27 bound planes3 (splitAxis s) side s.gram=true))

def positiveOK (lookup : ℕ → AxisEntry) (s : State) (slot : Fin 4) (h0 h1 h2 : ℕ) : Bool :=
  let entries : Fin 3 → AxisEntry := ![lookup h0,lookup h1,lookup h2]
  let packets : Fin 4 → ℕ := ![s.kernels slot,broadcast (entries 0) 0,broadcast (entries 1) 1,broadcast (entries 2) 2]
  decide (∀ a, (entries a).level=s.levels a ∧ (entries a).index=s.indices a ∧
    broadcastOK 1331 bound planes11 a (axisValues (entries a)) (broadcast (entries a) a)=true) &&
    positiveSumOK 128 1331 bound (4*offset) 4 packets

def gramOK (s : State) : Bool :=
  decide (∀ i j k : Fin 3, offset<limb 128 s.gram (index 3 i j k))
def orderOK (s : State) (a b : Fin 3) : Bool :=
  decide (a.val<b.val ∧ (s.indices b+1)*(1 <<< s.levels a)<s.indices a*(1 <<< s.levels b))
def low (s : State) (a : Fin 3) : ℚ := -1+(39/25 : ℚ)*s.indices a/(1 <<< s.levels a : ℕ)
def high (s : State) (a : Fin 3) : ℚ := -1+(39/25 : ℚ)*(s.indices a+1)/(1 <<< s.levels a : ℕ)
def localOK (cores : ℕ → Fin 3 → ℚ × ℚ) (s : State) (id : ℕ) : Bool :=
  decide (id<12 ∧ ∀ a, (cores id a).1≤low s a ∧ high s a≤(cores id a).2)

def check (lookup : ℕ → AxisEntry) (cores : ℕ → Fin 3 → ℚ × ℚ) (s : State) : Tree → Bool
  | .positive slot h0 h1 h2 => positiveOK lookup s slot h0 h1 h2
  | .gram => gramOK s
  | .order a b => orderOK s a b
  | .local id => localOK cores s id
  | .split mask left right =>
    decide (mask=need left ||| need right) &&
      stepOK s (need left) false && check lookup cores (child s (need left) false) left &&
      stepOK s (need right) true && check lookup cores (child s (need right) true) right

def fullChild (s : State) (side : Bool) : State := child s 31 side
def atPath (root : State) (path : List Bool) : State := path.foldl fullChild root
def pathOK : State → List Bool → Bool
  | _,[] => true
  | s,side::rest => stepOK s 31 side && pathOK (fullChild s side) rest

def stateEqual (s t : State) : Bool := decide (s.depth=t.depth ∧
  (∀ a, s.levels a=t.levels a) ∧ (∀ a, s.indices a=t.indices a) ∧
  (∀ q, s.kernels q=t.kernels q) ∧ s.gram=t.gram)
theorem stateEqual_sound (s t : State) (h : stateEqual s t=true) : s=t := by
  have hp : s.depth=t.depth ∧ (∀ a, s.levels a=t.levels a) ∧
      (∀ a, s.indices a=t.indices a) ∧ (∀ q, s.kernels q=t.kernels q) ∧ s.gram=t.gram := of_decide_eq_true h
  rcases s with ⟨d,l,i,k,g⟩
  rcases t with ⟨d',l',i',k',g'⟩
  have hd : d=d' := hp.1
  have hl : l=l' := funext hp.2.1
  have hi : i=i' := funext hp.2.2.1
  have hk : k=k' := funext hp.2.2.2.1
  have hg : g=g' := hp.2.2.2.2
  subst d';subst l';subst i';subst k';subst g'
  rfl

def nodeGuards (s : State) (mask : ℕ) (l r : Tree) : Bool :=
  decide (mask=need l ||| need r) && stepOK s (need l) false && stepOK s (need r) true

theorem check_split_true (lookup : ℕ → AxisEntry) (cores : ℕ → Fin 3 → ℚ × ℚ)
    (s : State) (mask : ℕ) (l r : Tree) (hg : nodeGuards s mask l r=true)
    (hl : check lookup cores (child s (need l) false) l=true)
    (hr : check lookup cores (child s (need r) true) r=true) : check lookup cores s (.split mask l r)=true := by
  have hp : decide (mask=need l ||| need r)=true ∧ stepOK s (need l) false=true ∧ stepOK s (need r) true=true := by
    simpa only [nodeGuards,Bool.and_eq_true_iff,and_assoc] using hg
  simpa only [check,Bool.and_eq_true_iff,and_assoc] using
    (show decide (mask=need l ||| need r)=true ∧ stepOK s (need l) false=true ∧
      check lookup cores (child s (need l) false) l=true ∧ stepOK s (need r) true=true ∧
      check lookup cores (child s (need r) true) r=true from ⟨hp.1,hp.2.1,hl,hp.2.2,hr⟩)
end ThomsonNine.PackedMain

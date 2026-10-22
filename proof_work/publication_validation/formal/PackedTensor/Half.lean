import PackedTensor.Selection

namespace ThomsonNine.PackedTensor
open ThomsonNine.PackedRadix
def rowAt (rows : List ℕ) (j : ℕ) : ℕ := (rows[j]?).getD 0
def makeRows (n g step : ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | d+1,x => x::makeRows n g step d (average 128 n g x (x >>> (128*step)))

def rowsOK (d n g step x : ℕ) (rows : List ℕ) : Bool :=
  decide (rows.length=d ∧ rowAt rows 0=x ∧ ∀ j : Fin (d-1),
    averageOK 128 n g (rowAt rows j.val) ((rowAt rows j.val) >>> (128*step))=true ∧
      rowAt rows (j.val+1)=average 128 n g (rowAt rows j.val) ((rowAt rows j.val) >>> (128*step)))

def assemble {d : ℕ} [NeZero d] (planes : Fin 3 → Fin d → ℕ) (axis : Fin 3)
    (right : Bool) (rows : List ℕ) : ℕ :=
  (List.finRange d).foldl (fun out c => out ||| (if right then rowAt rows (d-1-c.val) &&& planes axis c
    else (rowAt rows c.val &&& planes axis 0) <<< (128*(stride d axis*c.val)))) 0

def half {d : ℕ} [NeZero d] (n g : ℕ) (planes : Fin 3 → Fin d → ℕ) (axis : Fin 3)
    (right : Bool) (x : ℕ) : ℕ :=
  assemble planes axis right (makeRows n g (stride d axis) d x)

def halfOK {d : ℕ} [NeZero d] (n g : ℕ) (planes : Fin 3 → Fin d → ℕ) (axis : Fin 3)
    (right : Bool) (x : ℕ) : Bool :=
  let rows := makeRows n g (stride d axis) d x
  let out := assemble planes axis right rows
  rowsOK d n g (stride d axis) x rows && selectionOK planes axis right (rowAt rows) out &&
    decide (out &&& fastMask 128 n g=out)

theorem rows_initial {d n g step x : ℕ} {rows : List ℕ} (h : rowsOK d n g step x rows=true) :
    rowAt rows 0=x := (of_decide_eq_true h).2.1

theorem rows_step {d n g step x : ℕ} {rows : List ℕ} (hg : 2*g+1<2^128)
    (h : rowsOK d n g step x rows=true) (j i : ℕ) (hj : j+1<d) (hi : i<n) :
    limb 128 (rowAt rows (j+1)) i=(limb 128 (rowAt rows j) i+limb 128 (rowAt rows j) (i+step))/2 := by
  have hp := (of_decide_eq_true h).2.2 ⟨j,by omega⟩
  rw [hp.2]
  exact averageShiftOK_sound 128 n g (rowAt rows j) step (by omega) hg hp.1 i hi

theorem half_checks {d : ℕ} [NeZero d] (n g : ℕ) (planes : Fin 3 → Fin d → ℕ) (axis : Fin 3)
    (right : Bool) (x : ℕ) (h : halfOK n g planes axis right x=true) :
    rowsOK d n g (stride d axis) x (makeRows n g (stride d axis) d x)=true ∧
    selectionOK planes axis right (rowAt (makeRows n g (stride d axis) d x)) (half n g planes axis right x)=true ∧
    half n g planes axis right x &&& fastMask 128 n g=half n g planes axis right x := by
  have hp := Bool.and_eq_true_iff.mp h
  have hq := Bool.and_eq_true_iff.mp hp.1
  exact ⟨hq.1,hq.2,of_decide_eq_true hp.2⟩

theorem half_left_limb {d : ℕ} [NeZero d] (n g : ℕ) (planes : Fin 3 → Fin d → ℕ)
    (hplanes : PlaneSpec planes) (axis : Fin 3) (x : ℕ)
    (h : halfOK n g planes axis false x=true) (p : CubeIndex d) :
    limb 128 (half n g planes axis false x) (flat p)=
      limb 128 (rowAt (makeRows n g (stride d axis) d x) (coord axis p).val) (zeroIndex axis p) :=
  selection_left planes hplanes axis _ _ (half_checks n g planes axis false x h).2.1 p

theorem half_right_limb {d : ℕ} [NeZero d] (n g : ℕ) (planes : Fin 3 → Fin d → ℕ)
    (hplanes : PlaneSpec planes) (axis : Fin 3) (x : ℕ)
    (h : halfOK n g planes axis true x=true) (p : CubeIndex d) :
    limb 128 (half n g planes axis true x) (flat p)=
      limb 128 (rowAt (makeRows n g (stride d axis) d x) (d-1-(coord axis p).val)) (flat p) :=
  selection_right planes hplanes axis _ _ (half_checks n g planes axis true x h).2.1 p
end ThomsonNine.PackedTensor

import PackedRadix.Checker
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PackedTensor
def index (d : ℕ) (i j k : Fin d) : ℕ := (i.val*d+j.val)*d+k.val
def coordinate (d : ℕ) (axis : Fin 3) (i j k : Fin d) : Fin d :=
  if axis=0 then i else if axis=1 then j else k
def block (bits : ℕ) : ℕ := (1 <<< bits)-1
def makePlane (d axis c : ℕ) : ℕ :=
  if axis=0 then block (128*d*d) <<< (128*d*d*c)
  else if axis=1 then (block (128*d)*(block (128*d*d*d)/block (128*d*d))) <<< (128*d*c)
  else (block 128*(block (128*d*d*d)/block (128*d))) <<< (128*c)
def planes3 (axis : Fin 3) (c : Fin 3) : ℕ := makePlane 3 axis.val c.val
def planes11 (axis : Fin 3) (c : Fin 11) : ℕ := makePlane 11 axis.val c.val
end ThomsonNine.PackedTensor

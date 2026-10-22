import PackedTensor.DenseTransform

namespace ThomsonNine.PackedTensor
def unflat (d : ℕ) [NeZero d] (id : ℕ) : CubeIndex d :=
  (Fin.ofNat d (id/(d*d)),Fin.ofNat d (id/d),Fin.ofNat d id)
end ThomsonNine.PackedTensor

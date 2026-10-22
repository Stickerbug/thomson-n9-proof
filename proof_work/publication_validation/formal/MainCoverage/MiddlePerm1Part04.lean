import MainCoverage.MiddleData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem perm_inverse_1_part4 : ∀ j : Fin 756, 256≤j.val → j.val<320 →
    permIndex (inverse 1) (permIndex 1 j)=j := by decide +kernel
theorem perm_exponent_1_part4 : ∀ j : Fin 756, 256≤j.val → j.val<320 → ∀ b : Fin 3,
    ActualF.Data.support (permIndex 1 j) b=ActualF.Data.support j (ActualKernel.QCache.permutation 1 b) := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

import MainCoverage.MiddleData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem perm_inverse_5_part7 : ∀ j : Fin 756, 448≤j.val → j.val<512 →
    permIndex (inverse 5) (permIndex 5 j)=j := by decide +kernel
theorem perm_exponent_5_part7 : ∀ j : Fin 756, 448≤j.val → j.val<512 → ∀ b : Fin 3,
    ActualF.Data.support (permIndex 5 j) b=ActualF.Data.support j (ActualKernel.QCache.permutation 5 b) := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

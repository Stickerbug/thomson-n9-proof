import MainCoverage.MiddleData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem perm_inverse_3_part8 : ∀ j : Fin 756, 512≤j.val → j.val<576 →
    permIndex (inverse 3) (permIndex 3 j)=j := by decide +kernel
theorem perm_exponent_3_part8 : ∀ j : Fin 756, 512≤j.val → j.val<576 → ∀ b : Fin 3,
    ActualF.Data.support (permIndex 3 j) b=ActualF.Data.support j (ActualKernel.QCache.permutation 3 b) := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

import MainCoverage.MiddleData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem perm_inverse_0_part10 : ∀ j : Fin 756, 640≤j.val → j.val<704 →
    permIndex (inverse 0) (permIndex 0 j)=j := by decide +kernel
theorem perm_exponent_0_part10 : ∀ j : Fin 756, 640≤j.val → j.val<704 → ∀ b : Fin 3,
    ActualF.Data.support (permIndex 0 j) b=ActualF.Data.support j (ActualKernel.QCache.permutation 0 b) := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

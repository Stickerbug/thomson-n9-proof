import MainCoverage.MiddleData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem perm_inverse_3_part2 : ∀ j : Fin 756, 128≤j.val → j.val<192 →
    permIndex (inverse 3) (permIndex 3 j)=j := by decide +kernel
theorem perm_exponent_3_part2 : ∀ j : Fin 756, 128≤j.val → j.val<192 → ∀ b : Fin 3,
    ActualF.Data.support (permIndex 3 j) b=ActualF.Data.support j (ActualKernel.QCache.permutation 3 b) := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

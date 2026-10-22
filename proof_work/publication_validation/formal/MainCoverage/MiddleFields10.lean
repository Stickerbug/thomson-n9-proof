import MainCoverage.MiddleData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
open scoped BigOperators
theorem middle_fields_10 : ∀ j : Fin 756, 640≤j.val → j.val<704 →
    symMid j=(∑ σ : Fin 6, mid (permIndex σ j))/6 ∧
      kernelCoeff j=-7*symMid j-(if j=0 then cUpper+10*eps else 0) := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

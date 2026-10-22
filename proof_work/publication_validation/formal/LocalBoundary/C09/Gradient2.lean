import LocalBoundary.C09.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C09
theorem gradient_fields2 : (gradientComputed 2).lo=(gradientCache 2).lo ∧ (gradientComputed 2).hi=(gradientCache 2).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C09

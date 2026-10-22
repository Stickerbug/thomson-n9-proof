import LocalBoundary.C06.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C06
theorem gradient_fields0 : (gradientComputed 0).lo=(gradientCache 0).lo ∧ (gradientComputed 0).hi=(gradientCache 0).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C06

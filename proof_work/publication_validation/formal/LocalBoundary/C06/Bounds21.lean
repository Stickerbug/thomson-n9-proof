import LocalBoundary.C06.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C06
theorem fields21 : (hessianComputed 2 1).lo=(hessianCache 2 1).lo ∧ (hessianComputed 2 1).hi=(hessianCache 2 1).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C06

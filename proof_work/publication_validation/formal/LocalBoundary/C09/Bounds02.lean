import LocalBoundary.C09.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C09
theorem fields02 : (hessianComputed 0 2).lo=(hessianCache 0 2).lo ∧ (hessianComputed 0 2).hi=(hessianCache 0 2).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C09

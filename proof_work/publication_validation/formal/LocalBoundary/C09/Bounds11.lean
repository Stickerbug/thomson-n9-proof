import LocalBoundary.C09.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C09
theorem fields11 : (hessianComputed 1 1).lo=(hessianCache 1 1).lo ∧ (hessianComputed 1 1).hi=(hessianCache 1 1).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C09

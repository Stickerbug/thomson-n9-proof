import LocalInterior.C11.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C11
theorem fields10 : (hessianComputed 1 0).lo=(hessianCache 1 0).lo ∧ (hessianComputed 1 0).hi=(hessianCache 1 0).hi := by decide +kernel
end ThomsonNine.ActualLocal.C11

import LocalInterior.C08.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C08
theorem fields20 : (hessianComputed 2 0).lo=(hessianCache 2 0).lo ∧ (hessianComputed 2 0).hi=(hessianCache 2 0).hi := by decide +kernel
end ThomsonNine.ActualLocal.C08

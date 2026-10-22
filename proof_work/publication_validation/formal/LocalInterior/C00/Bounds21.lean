import LocalInterior.C00.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C00
theorem fields21 : (hessianComputed 2 1).lo=(hessianCache 2 1).lo ∧ (hessianComputed 2 1).hi=(hessianCache 2 1).hi := by decide +kernel
end ThomsonNine.ActualLocal.C00

import ThomsonNine.Construction.LocalInterior.C04.Model

-- Isolated source: LocalInterior.C04.Bounds10
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C04
theorem fields10 : (hessianComputed 1 0).lo=(hessianCache 1 0).lo ∧ (hessianComputed 1 0).hi=(hessianCache 1 0).hi := by decide +kernel
end ThomsonNine.ActualLocal.C04

end

-- Isolated source: LocalInterior.C04.Bounds11
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C04
theorem fields11 : (hessianComputed 1 1).lo=(hessianCache 1 1).lo ∧ (hessianComputed 1 1).hi=(hessianCache 1 1).hi := by decide +kernel
end ThomsonNine.ActualLocal.C04

end

-- Isolated source: LocalInterior.C04.Bounds12
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C04
theorem fields12 : (hessianComputed 1 2).lo=(hessianCache 1 2).lo ∧ (hessianComputed 1 2).hi=(hessianCache 1 2).hi := by decide +kernel
end ThomsonNine.ActualLocal.C04

end

import ThomsonNine.Construction.LocalInterior.C02.Model

-- Isolated source: LocalInterior.C02.Bounds00
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C02
theorem fields00 : (hessianComputed 0 0).lo=(hessianCache 0 0).lo ∧ (hessianComputed 0 0).hi=(hessianCache 0 0).hi := by decide +kernel
end ThomsonNine.ActualLocal.C02

end

-- Isolated source: LocalInterior.C02.Bounds01
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C02
theorem fields01 : (hessianComputed 0 1).lo=(hessianCache 0 1).lo ∧ (hessianComputed 0 1).hi=(hessianCache 0 1).hi := by decide +kernel
end ThomsonNine.ActualLocal.C02

end

-- Isolated source: LocalInterior.C02.Bounds02
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C02
theorem fields02 : (hessianComputed 0 2).lo=(hessianCache 0 2).lo ∧ (hessianComputed 0 2).hi=(hessianCache 0 2).hi := by decide +kernel
end ThomsonNine.ActualLocal.C02

end

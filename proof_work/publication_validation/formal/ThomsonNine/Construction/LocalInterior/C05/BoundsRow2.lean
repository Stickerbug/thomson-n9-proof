import ThomsonNine.Construction.LocalInterior.C05.Model

-- Isolated source: LocalInterior.C05.Bounds20
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C05
theorem fields20 : (hessianComputed 2 0).lo=(hessianCache 2 0).lo ∧ (hessianComputed 2 0).hi=(hessianCache 2 0).hi := by decide +kernel
end ThomsonNine.ActualLocal.C05

end

-- Isolated source: LocalInterior.C05.Bounds21
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C05
theorem fields21 : (hessianComputed 2 1).lo=(hessianCache 2 1).lo ∧ (hessianComputed 2 1).hi=(hessianCache 2 1).hi := by decide +kernel
end ThomsonNine.ActualLocal.C05

end

-- Isolated source: LocalInterior.C05.Bounds22
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocal.C05
theorem fields22 : (hessianComputed 2 2).lo=(hessianCache 2 2).lo ∧ (hessianComputed 2 2).hi=(hessianCache 2 2).hi := by decide +kernel
end ThomsonNine.ActualLocal.C05

end

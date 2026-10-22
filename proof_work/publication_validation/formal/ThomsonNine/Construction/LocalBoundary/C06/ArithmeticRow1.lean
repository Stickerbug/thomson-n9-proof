import ThomsonNine.Construction.LocalBoundary.C06.Model

-- Isolated source: LocalBoundary.C06.Bounds10
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C06
theorem fields10 : (hessianComputed 1 0).lo=(hessianCache 1 0).lo ∧ (hessianComputed 1 0).hi=(hessianCache 1 0).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C06

end

-- Isolated source: LocalBoundary.C06.Bounds11
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C06
theorem fields11 : (hessianComputed 1 1).lo=(hessianCache 1 1).lo ∧ (hessianComputed 1 1).hi=(hessianCache 1 1).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C06

end

-- Isolated source: LocalBoundary.C06.Bounds12
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C06
theorem fields12 : (hessianComputed 1 2).lo=(hessianCache 1 2).lo ∧ (hessianComputed 1 2).hi=(hessianCache 1 2).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C06

end

-- Isolated source: LocalBoundary.C06.Gradient1
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C06
theorem gradient_fields1 : (gradientComputed 1).lo=(gradientCache 1).lo ∧ (gradientComputed 1).hi=(gradientCache 1).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C06

end

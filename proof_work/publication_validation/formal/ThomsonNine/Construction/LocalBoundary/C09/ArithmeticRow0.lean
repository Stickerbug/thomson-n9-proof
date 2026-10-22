import ThomsonNine.Construction.LocalBoundary.C09.Model

-- Isolated source: LocalBoundary.C09.Bounds00
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C09
theorem fields00 : (hessianComputed 0 0).lo=(hessianCache 0 0).lo ∧ (hessianComputed 0 0).hi=(hessianCache 0 0).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C09

end

-- Isolated source: LocalBoundary.C09.Bounds01
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C09
theorem fields01 : (hessianComputed 0 1).lo=(hessianCache 0 1).lo ∧ (hessianComputed 0 1).hi=(hessianCache 0 1).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C09

end

-- Isolated source: LocalBoundary.C09.Bounds02
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C09
theorem fields02 : (hessianComputed 0 2).lo=(hessianCache 0 2).lo ∧ (hessianComputed 0 2).hi=(hessianCache 0 2).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C09

end

-- Isolated source: LocalBoundary.C09.Gradient0
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualBoundary.C09
theorem gradient_fields0 : (gradientComputed 0).lo=(gradientCache 0).lo ∧ (gradientComputed 0).hi=(gradientCache 0).hi := by decide +kernel
end ThomsonNine.ActualBoundary.C09

end

import MainCoverage.TraceData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem diagonal_exponents_18 :
    (diagonalGroups 18).all (fun j => decide (ActualF.Data.support (Fin.ofNat 756 j) 1+ActualF.Data.support (Fin.ofNat 756 j) 2=18))=true := by decide +kernel
theorem diagonal_coefficients_18 :
    diagonalCoeff 18=((diagonalGroups 18).map (fun j => symMid (Fin.ofNat 756 j))).sum := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

import MainCoverage.TraceData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem diagonal_exponents_15 :
    (diagonalGroups 15).all (fun j => decide (ActualF.Data.support (Fin.ofNat 756 j) 1+ActualF.Data.support (Fin.ofNat 756 j) 2=15))=true := by decide +kernel
theorem diagonal_coefficients_15 :
    diagonalCoeff 15=((diagonalGroups 15).map (fun j => symMid (Fin.ofNat 756 j))).sum := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

import MainCoverage.TraceData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem diagonal_exponents_1 :
    (diagonalGroups 1).all (fun j => decide (ActualF.Data.support (Fin.ofNat 756 j) 1+ActualF.Data.support (Fin.ofNat 756 j) 2=1))=true := by decide +kernel
theorem diagonal_coefficients_1 :
    diagonalCoeff 1=((diagonalGroups 1).map (fun j => symMid (Fin.ofNat 756 j))).sum := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

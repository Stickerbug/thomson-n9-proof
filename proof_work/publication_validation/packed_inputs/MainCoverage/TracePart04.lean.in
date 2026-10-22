import MainCoverage.TraceData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
theorem diagonal_exponents_4 :
    (diagonalGroups 4).all (fun j => decide (ActualF.Data.support (Fin.ofNat 756 j) 1+ActualF.Data.support (Fin.ofNat 756 j) 2=4))=true := by decide +kernel
theorem diagonal_coefficients_4 :
    diagonalCoeff 4=((diagonalGroups 4).map (fun j => symMid (Fin.ofNat 756 j))).sum := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

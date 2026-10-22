import MainCoverage.MiddleData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.MainEnvelope.Archive
open scoped BigOperators
theorem epsilon_fields : epsilon=eps := by decide +kernel
theorem c_upper_valid : ActualF.Constants.cInterval.hi≤cUpper := by decide +kernel
theorem support_zero : ActualF.Data.support 0=![0,0,0] := by decide +kernel
end ThomsonNine.MainEnvelope.Archive

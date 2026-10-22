import PackedTensor.RowMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedTensor
theorem row_spec_3 : rowSpec 3 := by decide +kernel
end ThomsonNine.PackedTensor

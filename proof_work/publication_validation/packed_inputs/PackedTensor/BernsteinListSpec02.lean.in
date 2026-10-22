import PackedTensor.BernsteinList
import PackedTensor.RowSpec03
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedTensor
 theorem exact_basis_spec_2 : exactBasisSpec 2 := by decide +kernel
 theorem basis_list_spec_2 : basisSpec 2 := exactBasisSpec_sound 2 exact_basis_spec_2
 #print axioms basis_list_spec_2
end ThomsonNine.PackedTensor

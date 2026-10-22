import MainCoverage.MiddlePerm4Part00
import MainCoverage.MiddlePerm4Part01
import MainCoverage.MiddlePerm4Part02
import MainCoverage.MiddlePerm4Part03
import MainCoverage.MiddlePerm4Part04
import MainCoverage.MiddlePerm4Part05
import MainCoverage.MiddlePerm4Part06
import MainCoverage.MiddlePerm4Part07
import MainCoverage.MiddlePerm4Part08
import MainCoverage.MiddlePerm4Part09
import MainCoverage.MiddlePerm4Part10
import MainCoverage.MiddlePerm4Part11
namespace ThomsonNine.MainEnvelope.Archive
theorem perm_inverse_4 (j : Fin 756) : permIndex (inverse 4) (permIndex 4 j)=j := by
  have hj := j.isLt
  by_cases h0 : j.val<64
  · exact perm_inverse_4_part0 j (by omega) h0
  by_cases h1 : j.val<128
  · exact perm_inverse_4_part1 j (by omega) h1
  by_cases h2 : j.val<192
  · exact perm_inverse_4_part2 j (by omega) h2
  by_cases h3 : j.val<256
  · exact perm_inverse_4_part3 j (by omega) h3
  by_cases h4 : j.val<320
  · exact perm_inverse_4_part4 j (by omega) h4
  by_cases h5 : j.val<384
  · exact perm_inverse_4_part5 j (by omega) h5
  by_cases h6 : j.val<448
  · exact perm_inverse_4_part6 j (by omega) h6
  by_cases h7 : j.val<512
  · exact perm_inverse_4_part7 j (by omega) h7
  by_cases h8 : j.val<576
  · exact perm_inverse_4_part8 j (by omega) h8
  by_cases h9 : j.val<640
  · exact perm_inverse_4_part9 j (by omega) h9
  by_cases h10 : j.val<704
  · exact perm_inverse_4_part10 j (by omega) h10
  exact perm_inverse_4_part11 j (by omega) (by omega)
theorem perm_exponent_4 (j : Fin 756) : ∀ b : Fin 3, ActualF.Data.support (permIndex 4 j) b=ActualF.Data.support j (ActualKernel.QCache.permutation 4 b) := by
  have hj := j.isLt
  by_cases h0 : j.val<64
  · exact perm_exponent_4_part0 j (by omega) h0
  by_cases h1 : j.val<128
  · exact perm_exponent_4_part1 j (by omega) h1
  by_cases h2 : j.val<192
  · exact perm_exponent_4_part2 j (by omega) h2
  by_cases h3 : j.val<256
  · exact perm_exponent_4_part3 j (by omega) h3
  by_cases h4 : j.val<320
  · exact perm_exponent_4_part4 j (by omega) h4
  by_cases h5 : j.val<384
  · exact perm_exponent_4_part5 j (by omega) h5
  by_cases h6 : j.val<448
  · exact perm_exponent_4_part6 j (by omega) h6
  by_cases h7 : j.val<512
  · exact perm_exponent_4_part7 j (by omega) h7
  by_cases h8 : j.val<576
  · exact perm_exponent_4_part8 j (by omega) h8
  by_cases h9 : j.val<640
  · exact perm_exponent_4_part9 j (by omega) h9
  by_cases h10 : j.val<704
  · exact perm_exponent_4_part10 j (by omega) h10
  exact perm_exponent_4_part11 j (by omega) (by omega)
end ThomsonNine.MainEnvelope.Archive

import ThomsonNine.Construction.AAA.ChunkBatch00
import ThomsonNine.Construction.AAA.ChunkBatch01
import ThomsonNine.Construction.AAA.ChunkBatch02
import ThomsonNine.Construction.AAA.ChunkBatch03
import ThomsonNine.Construction.AAA.ChunkBatch04
import ThomsonNine.Construction.AAA.ChunkBatch05
import ThomsonNine.Construction.AAA.ChunkBatch06
import ThomsonNine.Construction.AAA.ChunkBatch07
import ThomsonNine.Construction.AAA.ChunkBatch08

-- Isolated source: AAA.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualLocalAAA
open ThomsonNine.FixedInterval ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.LocalSparseHessianAAA
def entries : List Entry := chunk00++chunk01++chunk02++chunk03++chunk04++chunk05++chunk06++chunk07++chunk08++chunk09++chunk10++chunk11++chunk12++chunk13++chunk14++chunk15++chunk16++chunk17++chunk18++chunk19++chunk20++chunk21++chunk22++chunk23++chunk24++chunk25++chunk26++chunk27++chunk28++chunk29++chunk30++chunk31++chunk32++chunk33++chunk34++chunk35++chunk36++chunk37++chunk38++chunk39++chunk40++chunk41++chunk42++chunk43++chunk44++chunk45++chunk46++chunk47++chunk48++chunk49++chunk50++chunk51++chunk52++chunk53++chunk54++chunk55++chunk56++chunk57++chunk58++chunk59++chunk60++chunk61++chunk62++chunk63++chunk64++chunk65++chunk66++chunk67
theorem entries_valid : entries.all (fun E => decide (Valid E))=true := by
  simp only [entries,List.all_append,chunk00_valid,chunk01_valid,chunk02_valid,chunk03_valid,chunk04_valid,chunk05_valid,chunk06_valid,chunk07_valid,chunk08_valid,chunk09_valid,chunk10_valid,chunk11_valid,chunk12_valid,chunk13_valid,chunk14_valid,chunk15_valid,chunk16_valid,chunk17_valid,chunk18_valid,chunk19_valid,chunk20_valid,chunk21_valid,chunk22_valid,chunk23_valid,chunk24_valid,chunk25_valid,chunk26_valid,chunk27_valid,chunk28_valid,chunk29_valid,chunk30_valid,chunk31_valid,chunk32_valid,chunk33_valid,chunk34_valid,chunk35_valid,chunk36_valid,chunk37_valid,chunk38_valid,chunk39_valid,chunk40_valid,chunk41_valid,chunk42_valid,chunk43_valid,chunk44_valid,chunk45_valid,chunk46_valid,chunk47_valid,chunk48_valid,chunk49_valid,chunk50_valid,chunk51_valid,chunk52_valid,chunk53_valid,chunk54_valid,chunk55_valid,chunk56_valid,chunk57_valid,chunk58_valid,chunk59_valid,chunk60_valid,chunk61_valid,chunk62_valid,chunk63_valid,chunk64_valid,chunk65_valid,chunk66_valid,chunk67_valid,Bool.and_self]
theorem valid_of_mem (E : Entry) (hE : E∈entries) : Valid E := by
  have h := List.all_eq_true.mp entries_valid E hE
  exact of_decide_eq_true h
local instance : DecidableEq TermIndex := fun a b =>
  if h : ActualR.Data.sourceIndex a=ActualR.Data.sourceIndex b then
    isTrue (by
      have he := congrArg ActualR.Data.termIndex h
      simpa only [ActualR.Data.termIndex_sourceIndex] using he)
  else isFalse (fun he => h (congrArg ActualR.Data.sourceIndex he))
theorem entries_indices : entries.map Entry.index=GatheredBinding.allTerms := by decide +kernel
end ThomsonNine.ActualLocalAAA

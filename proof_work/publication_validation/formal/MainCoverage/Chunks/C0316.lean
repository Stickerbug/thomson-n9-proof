import MainCoverage.Chunks.C0316Data
import MainCoverage.Chunks.C0316Prefix
import MainCoverage.Chunks.C0316Guard00
import MainCoverage.Chunks.C0316Leaf00
import MainCoverage.Chunks.C0316Leaf01
import MainCoverage.Chunks.C0316Leaf02
import MainCoverage.Chunks.C0316Leaf03
import MainCoverage.Chunks.C0316Leaf04
import MainCoverage.Chunks.C0316Leaf05
import MainCoverage.Chunks.C0316Leaf06
import MainCoverage.Chunks.C0316Leaf07
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0316Checked011 : check axisLookup localCores fact0316S011 fact0316T011=true := by
  rw [fact0316Shape011]
  exact check_split_true axisLookup localCores fact0316S011 fact0316M011 fact0316T012 fact0316T013 fact0316Guard011 fact0316Checked012 fact0316Checked013
theorem fact0316Checked009 : check axisLookup localCores fact0316S009 fact0316T009=true := by
  rw [fact0316Shape009]
  exact check_split_true axisLookup localCores fact0316S009 fact0316M009 fact0316T010 fact0316T011 fact0316Guard009 fact0316Checked010 fact0316Checked011
theorem fact0316Checked007 : check axisLookup localCores fact0316S007 fact0316T007=true := by
  rw [fact0316Shape007]
  exact check_split_true axisLookup localCores fact0316S007 fact0316M007 fact0316T008 fact0316T009 fact0316Guard007 fact0316Checked008 fact0316Checked009
theorem fact0316Checked006 : check axisLookup localCores fact0316S006 fact0316T006=true := by
  rw [fact0316Shape006]
  exact check_split_true axisLookup localCores fact0316S006 fact0316M006 fact0316T007 fact0316T014 fact0316Guard006 fact0316Checked007 fact0316Checked014
theorem fact0316Checked004 : check axisLookup localCores fact0316S004 fact0316T004=true := by
  rw [fact0316Shape004]
  exact check_split_true axisLookup localCores fact0316S004 fact0316M004 fact0316T005 fact0316T006 fact0316Guard004 fact0316Checked005 fact0316Checked006
theorem fact0316Checked002 : check axisLookup localCores fact0316S002 fact0316T002=true := by
  rw [fact0316Shape002]
  exact check_split_true axisLookup localCores fact0316S002 fact0316M002 fact0316T003 fact0316T004 fact0316Guard002 fact0316Checked003 fact0316Checked004
theorem fact0316Checked000 : check axisLookup localCores fact0316S000 fact0316T000=true := by
  rw [fact0316Shape000]
  exact check_split_true axisLookup localCores fact0316S000 fact0316M000 fact0316T001 fact0316T002 fact0316Guard000 fact0316Checked001 fact0316Checked002
theorem checked0316 : pathOK rootState path0316=true ∧ check axisLookup localCores (atPath rootState path0316) tree0316=true := by
  constructor
  · exact prefix0316_checked
  · rw [cache0316_equal]
    exact fact0316Checked000
end ThomsonNine.PackedMain

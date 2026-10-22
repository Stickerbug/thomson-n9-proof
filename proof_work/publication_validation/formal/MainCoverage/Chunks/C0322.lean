import MainCoverage.Chunks.C0322Data
import MainCoverage.Chunks.C0322Prefix
import MainCoverage.Chunks.C0322Guard00
import MainCoverage.Chunks.C0322Leaf00
import MainCoverage.Chunks.C0322Leaf01
import MainCoverage.Chunks.C0322Leaf02
import MainCoverage.Chunks.C0322Leaf03
import MainCoverage.Chunks.C0322Leaf04
import MainCoverage.Chunks.C0322Leaf05
import MainCoverage.Chunks.C0322Leaf06
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0322Checked006 : check axisLookup localCores fact0322S006 fact0322T006=true := by
  rw [fact0322Shape006]
  exact check_split_true axisLookup localCores fact0322S006 fact0322M006 fact0322T007 fact0322T008 fact0322Guard006 fact0322Checked007 fact0322Checked008
theorem fact0322Checked005 : check axisLookup localCores fact0322S005 fact0322T005=true := by
  rw [fact0322Shape005]
  exact check_split_true axisLookup localCores fact0322S005 fact0322M005 fact0322T006 fact0322T009 fact0322Guard005 fact0322Checked006 fact0322Checked009
theorem fact0322Checked003 : check axisLookup localCores fact0322S003 fact0322T003=true := by
  rw [fact0322Shape003]
  exact check_split_true axisLookup localCores fact0322S003 fact0322M003 fact0322T004 fact0322T005 fact0322Guard003 fact0322Checked004 fact0322Checked005
theorem fact0322Checked002 : check axisLookup localCores fact0322S002 fact0322T002=true := by
  rw [fact0322Shape002]
  exact check_split_true axisLookup localCores fact0322S002 fact0322M002 fact0322T003 fact0322T010 fact0322Guard002 fact0322Checked003 fact0322Checked010
theorem fact0322Checked001 : check axisLookup localCores fact0322S001 fact0322T001=true := by
  rw [fact0322Shape001]
  exact check_split_true axisLookup localCores fact0322S001 fact0322M001 fact0322T002 fact0322T011 fact0322Guard001 fact0322Checked002 fact0322Checked011
theorem fact0322Checked000 : check axisLookup localCores fact0322S000 fact0322T000=true := by
  rw [fact0322Shape000]
  exact check_split_true axisLookup localCores fact0322S000 fact0322M000 fact0322T001 fact0322T012 fact0322Guard000 fact0322Checked001 fact0322Checked012
theorem checked0322 : pathOK rootState path0322=true ∧ check axisLookup localCores (atPath rootState path0322) tree0322=true := by
  constructor
  · exact prefix0322_checked
  · rw [cache0322_equal]
    exact fact0322Checked000
end ThomsonNine.PackedMain

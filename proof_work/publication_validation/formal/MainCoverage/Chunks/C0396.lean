import MainCoverage.Chunks.C0396Data
import MainCoverage.Chunks.C0396Prefix
import MainCoverage.Chunks.C0396Guard00
import MainCoverage.Chunks.C0396Leaf00
import MainCoverage.Chunks.C0396Leaf01
import MainCoverage.Chunks.C0396Leaf02
import MainCoverage.Chunks.C0396Leaf03
import MainCoverage.Chunks.C0396Leaf04
import MainCoverage.Chunks.C0396Leaf05
import MainCoverage.Chunks.C0396Leaf06
import MainCoverage.Chunks.C0396Leaf07
import MainCoverage.Chunks.C0396Leaf08
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0396Checked010 : check axisLookup localCores fact0396S010 fact0396T010=true := by
  rw [fact0396Shape010]
  exact check_split_true axisLookup localCores fact0396S010 fact0396M010 fact0396T011 fact0396T012 fact0396Guard010 fact0396Checked011 fact0396Checked012
theorem fact0396Checked008 : check axisLookup localCores fact0396S008 fact0396T008=true := by
  rw [fact0396Shape008]
  exact check_split_true axisLookup localCores fact0396S008 fact0396M008 fact0396T009 fact0396T010 fact0396Guard008 fact0396Checked009 fact0396Checked010
theorem fact0396Checked007 : check axisLookup localCores fact0396S007 fact0396T007=true := by
  rw [fact0396Shape007]
  exact check_split_true axisLookup localCores fact0396S007 fact0396M007 fact0396T008 fact0396T013 fact0396Guard007 fact0396Checked008 fact0396Checked013
theorem fact0396Checked006 : check axisLookup localCores fact0396S006 fact0396T006=true := by
  rw [fact0396Shape006]
  exact check_split_true axisLookup localCores fact0396S006 fact0396M006 fact0396T007 fact0396T014 fact0396Guard006 fact0396Checked007 fact0396Checked014
theorem fact0396Checked004 : check axisLookup localCores fact0396S004 fact0396T004=true := by
  rw [fact0396Shape004]
  exact check_split_true axisLookup localCores fact0396S004 fact0396M004 fact0396T005 fact0396T006 fact0396Guard004 fact0396Checked005 fact0396Checked006
theorem fact0396Checked003 : check axisLookup localCores fact0396S003 fact0396T003=true := by
  rw [fact0396Shape003]
  exact check_split_true axisLookup localCores fact0396S003 fact0396M003 fact0396T004 fact0396T015 fact0396Guard003 fact0396Checked004 fact0396Checked015
theorem fact0396Checked002 : check axisLookup localCores fact0396S002 fact0396T002=true := by
  rw [fact0396Shape002]
  exact check_split_true axisLookup localCores fact0396S002 fact0396M002 fact0396T003 fact0396T016 fact0396Guard002 fact0396Checked003 fact0396Checked016
theorem fact0396Checked000 : check axisLookup localCores fact0396S000 fact0396T000=true := by
  rw [fact0396Shape000]
  exact check_split_true axisLookup localCores fact0396S000 fact0396M000 fact0396T001 fact0396T002 fact0396Guard000 fact0396Checked001 fact0396Checked002
theorem checked0396 : pathOK rootState path0396=true ∧ check axisLookup localCores (atPath rootState path0396) tree0396=true := by
  constructor
  · exact prefix0396_checked
  · rw [cache0396_equal]
    exact fact0396Checked000
end ThomsonNine.PackedMain

import MainCoverage.Chunks.C0321Data
import MainCoverage.Chunks.C0321Prefix
import MainCoverage.Chunks.C0321Guard00
import MainCoverage.Chunks.C0321Leaf00
import MainCoverage.Chunks.C0321Leaf01
import MainCoverage.Chunks.C0321Leaf02
import MainCoverage.Chunks.C0321Leaf03
import MainCoverage.Chunks.C0321Leaf04
import MainCoverage.Chunks.C0321Leaf05
import MainCoverage.Chunks.C0321Leaf06
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0321Checked009 : check axisLookup localCores fact0321S009 fact0321T009=true := by
  rw [fact0321Shape009]
  exact check_split_true axisLookup localCores fact0321S009 fact0321M009 fact0321T010 fact0321T011 fact0321Guard009 fact0321Checked010 fact0321Checked011
theorem fact0321Checked007 : check axisLookup localCores fact0321S007 fact0321T007=true := by
  rw [fact0321Shape007]
  exact check_split_true axisLookup localCores fact0321S007 fact0321M007 fact0321T008 fact0321T009 fact0321Guard007 fact0321Checked008 fact0321Checked009
theorem fact0321Checked006 : check axisLookup localCores fact0321S006 fact0321T006=true := by
  rw [fact0321Shape006]
  exact check_split_true axisLookup localCores fact0321S006 fact0321M006 fact0321T007 fact0321T012 fact0321Guard006 fact0321Checked007 fact0321Checked012
theorem fact0321Checked005 : check axisLookup localCores fact0321S005 fact0321T005=true := by
  rw [fact0321Shape005]
  exact check_split_true axisLookup localCores fact0321S005 fact0321M005 fact0321T006 fact0321T013 fact0321Guard005 fact0321Checked006 fact0321Checked013
theorem fact0321Checked004 : check axisLookup localCores fact0321S004 fact0321T004=true := by
  rw [fact0321Shape004]
  exact check_split_true axisLookup localCores fact0321S004 fact0321M004 fact0321T005 fact0321T014 fact0321Guard004 fact0321Checked005 fact0321Checked014
theorem fact0321Checked003 : check axisLookup localCores fact0321S003 fact0321T003=true := by
  rw [fact0321Shape003]
  exact check_split_true axisLookup localCores fact0321S003 fact0321M003 fact0321T004 fact0321T015 fact0321Guard003 fact0321Checked004 fact0321Checked015
theorem fact0321Checked002 : check axisLookup localCores fact0321S002 fact0321T002=true := by
  rw [fact0321Shape002]
  exact check_split_true axisLookup localCores fact0321S002 fact0321M002 fact0321T003 fact0321T016 fact0321Guard002 fact0321Checked003 fact0321Checked016
theorem fact0321Checked000 : check axisLookup localCores fact0321S000 fact0321T000=true := by
  rw [fact0321Shape000]
  exact check_split_true axisLookup localCores fact0321S000 fact0321M000 fact0321T001 fact0321T002 fact0321Guard000 fact0321Checked001 fact0321Checked002
theorem checked0321 : pathOK rootState path0321=true ∧ check axisLookup localCores (atPath rootState path0321) tree0321=true := by
  constructor
  · exact prefix0321_checked
  · rw [cache0321_equal]
    exact fact0321Checked000
end ThomsonNine.PackedMain

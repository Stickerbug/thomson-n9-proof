import MainCoverage.Chunks.C0330Data
import MainCoverage.Chunks.C0330Prefix
import MainCoverage.Chunks.C0330Guard00
import MainCoverage.Chunks.C0330Leaf00
import MainCoverage.Chunks.C0330Leaf01
import MainCoverage.Chunks.C0330Leaf02
import MainCoverage.Chunks.C0330Leaf03
import MainCoverage.Chunks.C0330Leaf04
import MainCoverage.Chunks.C0330Leaf05
import MainCoverage.Chunks.C0330Leaf06
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0330Checked009 : check axisLookup localCores fact0330S009 fact0330T009=true := by
  rw [fact0330Shape009]
  exact check_split_true axisLookup localCores fact0330S009 fact0330M009 fact0330T010 fact0330T011 fact0330Guard009 fact0330Checked010 fact0330Checked011
theorem fact0330Checked006 : check axisLookup localCores fact0330S006 fact0330T006=true := by
  rw [fact0330Shape006]
  exact check_split_true axisLookup localCores fact0330S006 fact0330M006 fact0330T007 fact0330T008 fact0330Guard006 fact0330Checked007 fact0330Checked008
theorem fact0330Checked004 : check axisLookup localCores fact0330S004 fact0330T004=true := by
  rw [fact0330Shape004]
  exact check_split_true axisLookup localCores fact0330S004 fact0330M004 fact0330T005 fact0330T006 fact0330Guard004 fact0330Checked005 fact0330Checked006
theorem fact0330Checked003 : check axisLookup localCores fact0330S003 fact0330T003=true := by
  rw [fact0330Shape003]
  exact check_split_true axisLookup localCores fact0330S003 fact0330M003 fact0330T004 fact0330T009 fact0330Guard003 fact0330Checked004 fact0330Checked009
theorem fact0330Checked002 : check axisLookup localCores fact0330S002 fact0330T002=true := by
  rw [fact0330Shape002]
  exact check_split_true axisLookup localCores fact0330S002 fact0330M002 fact0330T003 fact0330T012 fact0330Guard002 fact0330Checked003 fact0330Checked012
theorem fact0330Checked000 : check axisLookup localCores fact0330S000 fact0330T000=true := by
  rw [fact0330Shape000]
  exact check_split_true axisLookup localCores fact0330S000 fact0330M000 fact0330T001 fact0330T002 fact0330Guard000 fact0330Checked001 fact0330Checked002
theorem checked0330 : pathOK rootState path0330=true ∧ check axisLookup localCores (atPath rootState path0330) tree0330=true := by
  constructor
  · exact prefix0330_checked
  · rw [cache0330_equal]
    exact fact0330Checked000
end ThomsonNine.PackedMain

import MainCoverage.Chunks.C0394Data
import MainCoverage.Chunks.C0394Prefix
import MainCoverage.Chunks.C0394Guard00
import MainCoverage.Chunks.C0394Guard01
import MainCoverage.Chunks.C0394Leaf00
import MainCoverage.Chunks.C0394Leaf01
import MainCoverage.Chunks.C0394Leaf02
import MainCoverage.Chunks.C0394Leaf03
import MainCoverage.Chunks.C0394Leaf04
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0394Checked015 : check axisLookup localCores fact0394S015 fact0394T015=true := by
  rw [fact0394Shape015]
  exact check_split_true axisLookup localCores fact0394S015 fact0394M015 fact0394T016 fact0394T017 fact0394Guard015 fact0394Checked016 fact0394Checked017
theorem fact0394Checked014 : check axisLookup localCores fact0394S014 fact0394T014=true := by
  rw [fact0394Shape014]
  exact check_split_true axisLookup localCores fact0394S014 fact0394M014 fact0394T015 fact0394T018 fact0394Guard014 fact0394Checked015 fact0394Checked018
theorem fact0394Checked011 : check axisLookup localCores fact0394S011 fact0394T011=true := by
  rw [fact0394Shape011]
  exact check_split_true axisLookup localCores fact0394S011 fact0394M011 fact0394T012 fact0394T013 fact0394Guard011 fact0394Checked012 fact0394Checked013
theorem fact0394Checked009 : check axisLookup localCores fact0394S009 fact0394T009=true := by
  rw [fact0394Shape009]
  exact check_split_true axisLookup localCores fact0394S009 fact0394M009 fact0394T010 fact0394T011 fact0394Guard009 fact0394Checked010 fact0394Checked011
theorem fact0394Checked007 : check axisLookup localCores fact0394S007 fact0394T007=true := by
  rw [fact0394Shape007]
  exact check_split_true axisLookup localCores fact0394S007 fact0394M007 fact0394T008 fact0394T009 fact0394Guard007 fact0394Checked008 fact0394Checked009
theorem fact0394Checked006 : check axisLookup localCores fact0394S006 fact0394T006=true := by
  rw [fact0394Shape006]
  exact check_split_true axisLookup localCores fact0394S006 fact0394M006 fact0394T007 fact0394T014 fact0394Guard006 fact0394Checked007 fact0394Checked014
theorem fact0394Checked004 : check axisLookup localCores fact0394S004 fact0394T004=true := by
  rw [fact0394Shape004]
  exact check_split_true axisLookup localCores fact0394S004 fact0394M004 fact0394T005 fact0394T006 fact0394Guard004 fact0394Checked005 fact0394Checked006
theorem fact0394Checked002 : check axisLookup localCores fact0394S002 fact0394T002=true := by
  rw [fact0394Shape002]
  exact check_split_true axisLookup localCores fact0394S002 fact0394M002 fact0394T003 fact0394T004 fact0394Guard002 fact0394Checked003 fact0394Checked004
theorem fact0394Checked000 : check axisLookup localCores fact0394S000 fact0394T000=true := by
  rw [fact0394Shape000]
  exact check_split_true axisLookup localCores fact0394S000 fact0394M000 fact0394T001 fact0394T002 fact0394Guard000 fact0394Checked001 fact0394Checked002
theorem checked0394 : pathOK rootState path0394=true ∧ check axisLookup localCores (atPath rootState path0394) tree0394=true := by
  constructor
  · exact prefix0394_checked
  · rw [cache0394_equal]
    exact fact0394Checked000
end ThomsonNine.PackedMain

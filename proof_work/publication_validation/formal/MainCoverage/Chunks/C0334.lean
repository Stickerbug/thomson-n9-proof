import MainCoverage.Chunks.C0334Data
import MainCoverage.Chunks.C0334Prefix
import MainCoverage.Chunks.C0334Guard00
import MainCoverage.Chunks.C0334Leaf00
import MainCoverage.Chunks.C0334Leaf01
import MainCoverage.Chunks.C0334Leaf02
import MainCoverage.Chunks.C0334Leaf03
import MainCoverage.Chunks.C0334Leaf04
import MainCoverage.Chunks.C0334Leaf05
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0334Checked007 : check axisLookup localCores fact0334S007 fact0334T007=true := by
  rw [fact0334Shape007]
  exact check_split_true axisLookup localCores fact0334S007 fact0334M007 fact0334T008 fact0334T009 fact0334Guard007 fact0334Checked008 fact0334Checked009
theorem fact0334Checked006 : check axisLookup localCores fact0334S006 fact0334T006=true := by
  rw [fact0334Shape006]
  exact check_split_true axisLookup localCores fact0334S006 fact0334M006 fact0334T007 fact0334T010 fact0334Guard006 fact0334Checked007 fact0334Checked010
theorem fact0334Checked005 : check axisLookup localCores fact0334S005 fact0334T005=true := by
  rw [fact0334Shape005]
  exact check_split_true axisLookup localCores fact0334S005 fact0334M005 fact0334T006 fact0334T011 fact0334Guard005 fact0334Checked006 fact0334Checked011
theorem fact0334Checked002 : check axisLookup localCores fact0334S002 fact0334T002=true := by
  rw [fact0334Shape002]
  exact check_split_true axisLookup localCores fact0334S002 fact0334M002 fact0334T003 fact0334T004 fact0334Guard002 fact0334Checked003 fact0334Checked004
theorem fact0334Checked001 : check axisLookup localCores fact0334S001 fact0334T001=true := by
  rw [fact0334Shape001]
  exact check_split_true axisLookup localCores fact0334S001 fact0334M001 fact0334T002 fact0334T005 fact0334Guard001 fact0334Checked002 fact0334Checked005
theorem fact0334Checked000 : check axisLookup localCores fact0334S000 fact0334T000=true := by
  rw [fact0334Shape000]
  exact check_split_true axisLookup localCores fact0334S000 fact0334M000 fact0334T001 fact0334T012 fact0334Guard000 fact0334Checked001 fact0334Checked012
theorem checked0334 : pathOK rootState path0334=true ∧ check axisLookup localCores (atPath rootState path0334) tree0334=true := by
  constructor
  · exact prefix0334_checked
  · rw [cache0334_equal]
    exact fact0334Checked000
end ThomsonNine.PackedMain

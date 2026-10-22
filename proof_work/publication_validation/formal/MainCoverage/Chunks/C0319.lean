import MainCoverage.Chunks.C0319Data
import MainCoverage.Chunks.C0319Prefix
import MainCoverage.Chunks.C0319Guard00
import MainCoverage.Chunks.C0319Leaf00
import MainCoverage.Chunks.C0319Leaf01
import MainCoverage.Chunks.C0319Leaf02
import MainCoverage.Chunks.C0319Leaf03
import MainCoverage.Chunks.C0319Leaf04
import MainCoverage.Chunks.C0319Leaf05
import MainCoverage.Chunks.C0319Leaf06
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0319Checked008 : check axisLookup localCores fact0319S008 fact0319T008=true := by
  rw [fact0319Shape008]
  exact check_split_true axisLookup localCores fact0319S008 fact0319M008 fact0319T009 fact0319T010 fact0319Guard008 fact0319Checked009 fact0319Checked010
theorem fact0319Checked007 : check axisLookup localCores fact0319S007 fact0319T007=true := by
  rw [fact0319Shape007]
  exact check_split_true axisLookup localCores fact0319S007 fact0319M007 fact0319T008 fact0319T011 fact0319Guard007 fact0319Checked008 fact0319Checked011
theorem fact0319Checked005 : check axisLookup localCores fact0319S005 fact0319T005=true := by
  rw [fact0319Shape005]
  exact check_split_true axisLookup localCores fact0319S005 fact0319M005 fact0319T006 fact0319T007 fact0319Guard005 fact0319Checked006 fact0319Checked007
theorem fact0319Checked003 : check axisLookup localCores fact0319S003 fact0319T003=true := by
  rw [fact0319Shape003]
  exact check_split_true axisLookup localCores fact0319S003 fact0319M003 fact0319T004 fact0319T005 fact0319Guard003 fact0319Checked004 fact0319Checked005
theorem fact0319Checked002 : check axisLookup localCores fact0319S002 fact0319T002=true := by
  rw [fact0319Shape002]
  exact check_split_true axisLookup localCores fact0319S002 fact0319M002 fact0319T003 fact0319T012 fact0319Guard002 fact0319Checked003 fact0319Checked012
theorem fact0319Checked000 : check axisLookup localCores fact0319S000 fact0319T000=true := by
  rw [fact0319Shape000]
  exact check_split_true axisLookup localCores fact0319S000 fact0319M000 fact0319T001 fact0319T002 fact0319Guard000 fact0319Checked001 fact0319Checked002
theorem checked0319 : pathOK rootState path0319=true ∧ check axisLookup localCores (atPath rootState path0319) tree0319=true := by
  constructor
  · exact prefix0319_checked
  · rw [cache0319_equal]
    exact fact0319Checked000
end ThomsonNine.PackedMain

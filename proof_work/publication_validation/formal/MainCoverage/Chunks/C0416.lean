import MainCoverage.Chunks.C0416Data
import MainCoverage.Chunks.C0416Prefix
import MainCoverage.Chunks.C0416Guard00
import MainCoverage.Chunks.C0416Guard01
import MainCoverage.Chunks.C0416Leaf00
import MainCoverage.Chunks.C0416Leaf01
import MainCoverage.Chunks.C0416Leaf02
import MainCoverage.Chunks.C0416Leaf03
import MainCoverage.Chunks.C0416Leaf04
import MainCoverage.Chunks.C0416Leaf05
import MainCoverage.Chunks.C0416Leaf06
import MainCoverage.Chunks.C0416Leaf07
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem fact0416Checked015 : check axisLookup localCores fact0416S015 fact0416T015=true := by
  rw [fact0416Shape015]
  exact check_split_true axisLookup localCores fact0416S015 fact0416M015 fact0416T016 fact0416T017 fact0416Guard015 fact0416Checked016 fact0416Checked017
theorem fact0416Checked014 : check axisLookup localCores fact0416S014 fact0416T014=true := by
  rw [fact0416Shape014]
  exact check_split_true axisLookup localCores fact0416S014 fact0416M014 fact0416T015 fact0416T018 fact0416Guard014 fact0416Checked015 fact0416Checked018
theorem fact0416Checked010 : check axisLookup localCores fact0416S010 fact0416T010=true := by
  rw [fact0416Shape010]
  exact check_split_true axisLookup localCores fact0416S010 fact0416M010 fact0416T011 fact0416T012 fact0416Guard010 fact0416Checked011 fact0416Checked012
theorem fact0416Checked009 : check axisLookup localCores fact0416S009 fact0416T009=true := by
  rw [fact0416Shape009]
  exact check_split_true axisLookup localCores fact0416S009 fact0416M009 fact0416T010 fact0416T013 fact0416Guard009 fact0416Checked010 fact0416Checked013
theorem fact0416Checked007 : check axisLookup localCores fact0416S007 fact0416T007=true := by
  rw [fact0416Shape007]
  exact check_split_true axisLookup localCores fact0416S007 fact0416M007 fact0416T008 fact0416T009 fact0416Guard007 fact0416Checked008 fact0416Checked009
theorem fact0416Checked004 : check axisLookup localCores fact0416S004 fact0416T004=true := by
  rw [fact0416Shape004]
  exact check_split_true axisLookup localCores fact0416S004 fact0416M004 fact0416T005 fact0416T006 fact0416Guard004 fact0416Checked005 fact0416Checked006
theorem fact0416Checked002 : check axisLookup localCores fact0416S002 fact0416T002=true := by
  rw [fact0416Shape002]
  exact check_split_true axisLookup localCores fact0416S002 fact0416M002 fact0416T003 fact0416T004 fact0416Guard002 fact0416Checked003 fact0416Checked004
theorem fact0416Checked001 : check axisLookup localCores fact0416S001 fact0416T001=true := by
  rw [fact0416Shape001]
  exact check_split_true axisLookup localCores fact0416S001 fact0416M001 fact0416T002 fact0416T007 fact0416Guard001 fact0416Checked002 fact0416Checked007
theorem fact0416Checked000 : check axisLookup localCores fact0416S000 fact0416T000=true := by
  rw [fact0416Shape000]
  exact check_split_true axisLookup localCores fact0416S000 fact0416M000 fact0416T001 fact0416T014 fact0416Guard000 fact0416Checked001 fact0416Checked014
theorem checked0416 : pathOK rootState path0416=true ∧ check axisLookup localCores (atPath rootState path0416) tree0416=true := by
  constructor
  · exact prefix0416_checked
  · rw [cache0416_equal]
    exact fact0416Checked000
end ThomsonNine.PackedMain

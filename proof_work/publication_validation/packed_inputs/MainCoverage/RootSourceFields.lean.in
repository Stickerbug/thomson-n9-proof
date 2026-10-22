import MainCoverage.RootSourcePart00
import MainCoverage.RootSourcePart01
import MainCoverage.RootSourcePart02
import MainCoverage.RootSourcePart03
import MainCoverage.RootSourcePart04
import MainCoverage.RootSourcePart05
import MainCoverage.RootSourcePart06
import MainCoverage.RootSourcePart07
import MainCoverage.RootSourcePart08
import MainCoverage.RootSourcePart09
import MainCoverage.RootSourcePart10
import MainCoverage.RootSourcePart11
import MainCoverage.RootSourcePartition
import Algebra.FiniteRange
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain.RootSource
open ThomsonNine.PackedTensor
def SourceProperty (j : Fin 756) : Prop :=
  (RootTensor.K00.coeff0 (unflat 11 (sourceIndex j)) : ℚ)/(RootTensor.K00.denominator0 : ℚ)=MainEnvelope.Archive.kernelCoeff j ∧
    ∀ a : Fin 3, (coord a (unflat 11 (sourceIndex j))).val=ActualF.Data.support j a
theorem all_source_fields (j : Fin 756) : SourceProperty j := by
  have hall (id : ℕ) (hid : id<756) : SourceProperty (Fin.ofNat 756 id) := by
    by_cases h0 : id<64
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 0 64 source_fields_0 id (by omega) (by omega)
    by_cases h1 : id<128
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 64 64 source_fields_1 id (by omega) (by omega)
    by_cases h2 : id<192
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 128 64 source_fields_2 id (by omega) (by omega)
    by_cases h3 : id<256
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 192 64 source_fields_3 id (by omega) (by omega)
    by_cases h4 : id<320
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 256 64 source_fields_4 id (by omega) (by omega)
    by_cases h5 : id<384
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 320 64 source_fields_5 id (by omega) (by omega)
    by_cases h6 : id<448
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 384 64 source_fields_6 id (by omega) (by omega)
    by_cases h7 : id<512
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 448 64 source_fields_7 id (by omega) (by omega)
    by_cases h8 : id<576
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 512 64 source_fields_8 id (by omega) (by omega)
    by_cases h9 : id<640
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 576 64 source_fields_9 id (by omega) (by omega)
    by_cases h10 : id<704
    · exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 640 64 source_fields_10 id (by omega) (by omega)
    exact FiniteCollector.bounded_offset (fun n => SourceProperty (Fin.ofNat 756 n)) 704 52 source_fields_11 id (by omega) (by omega)
  simpa only [Fin.ofNat_val_eq_self] using hall j.val j.isLt
end ThomsonNine.PackedMain.RootSource

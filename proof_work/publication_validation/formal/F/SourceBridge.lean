import F.SourceData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualF.Data
open ThomsonNine.CertificateMatrices
open ThomsonNine.ActualHermite.CoefficientData
def blockCount : Fin 11 → ℕ := ![726, 1200, 2916, 3840, 5586, 5832, 6600, 5760, 4590, 2592, 870]
theorem encoded_blocks (k : Fin 11) : (blockSources k).map encode=List.range' (offset k) (blockCount k) := by
  fin_cases k
  · exact encodedBlock00
  · exact encodedBlock01
  · exact encodedBlock02
  · exact encodedBlock03
  · exact encodedBlock04
  · exact encodedBlock05
  · exact encodedBlock06
  · exact encodedBlock07
  · exact encodedBlock08
  · exact encodedBlock09
  · exact encodedBlock10
theorem encoded_ranges : (List.finRange 11).flatMap (fun k => List.range' (offset k) (blockCount k))=List.range count := by decide +kernel
theorem encoded_all : allSources.map encode=List.range count := by
  rw [allSources,List.map_flatMap]
  have hf : (fun k : Fin 11 => (blockSources k).map encode)=(fun k => List.range' (offset k) (blockCount k)) := funext encoded_blocks
  rw [hf]
  exact encoded_ranges
theorem decoded_blocks (k : Fin 11) : (blockSources k).all (fun s => decide (decode (encode s)=s))=true := by
  fin_cases k
  · exact decodedBlock00
  · exact decodedBlock01
  · exact decodedBlock02
  · exact decodedBlock03
  · exact decodedBlock04
  · exact decodedBlock05
  · exact decodedBlock06
  · exact decodedBlock07
  · exact decodedBlock08
  · exact decodedBlock09
  · exact decodedBlock10

theorem decoded_all_bool : allSources.all (fun s => decide (decode (encode s)=s))=true := by
  rw [allSources,List.all_flatMap]
  exact List.all_eq_true.mpr (fun k _ => decoded_blocks k)

theorem decoded_all (s : Source) (hs : s∈allSources) : decode (encode s)=s := by
  have h := (List.all_eq_true.mp decoded_all_bool) s hs
  exact of_decide_eq_true h
theorem decoded_range : (List.range count).map decode=allSources := by
  rw [← encoded_all,List.map_map]
  calc
    allSources.map (fun s => decode (encode s)) = allSources.map id := List.map_congr_left (fun s hs => decoded_all s hs)
    _ = allSources := List.map_id allSources
end ThomsonNine.ActualF.Data

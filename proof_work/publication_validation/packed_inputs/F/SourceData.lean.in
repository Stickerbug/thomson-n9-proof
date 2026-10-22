import Matrices.Bounds
import Algebra.QPolynomials
import Algebra.FiniteCollector
import Algebra.FixedIntegerScale
import Kernel.QCacheData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualF.Data
open ThomsonNine.CertificateMatrices
open ThomsonNine.ActualHermite.CoefficientData
abbrev Exponent := Fin 3 → ℕ
structure Source where
  block : Fin 11
  left : ℕ
  right : ℕ
  permutation : Fin 6
  term : ℕ
deriving DecidableEq
def count : ℕ := 40512
def offset : Fin 11 → ℕ := ![0,
726,
1926,
4842,
8682,
14268,
20100,
26700,
32460,
37050,
39642]
def blockOf (n : ℕ) : Fin 11 := if n<726 then 0 else if n<1926 then 1 else if n<4842 then 2 else if n<8682 then 3 else if n<14268 then 4 else if n<20100 then 5 else if n<26700 then 6 else if n<32460 then 7 else if n<37050 then 8 else if n<39642 then 9 else 10
def termCount (k : Fin 11) : ℕ := (QPolynomial.terms k).length
theorem termCount_positive : ∀ k : Fin 11, 0<termCount k := by decide +kernel
theorem ambient_positive (k : Fin 11) : 0<ambientDim k := by unfold ambientDim; omega
def decode (n : ℕ) : Source :=
  let k := blockOf n
  let p := (n-offset k)/termCount k
  ⟨k,p/6/ambientDim k,(p/6)%ambientDim k,⟨p%6,Nat.mod_lt _ (by decide)⟩,(n-offset k)%termCount k⟩
def encode (s : Source) : ℕ :=
  offset s.block+((s.left*ambientDim s.block+s.right)*6+s.permutation.val)*termCount s.block+s.term
def blockSources (k : Fin 11) : List Source :=
    (List.finRange (ambientDim k)).flatMap (fun a =>
      (List.finRange (ambientDim k)).flatMap (fun b =>
        (List.finRange 6).flatMap (fun σ =>
          (List.finRange (termCount k)).map (fun t => ⟨k,a.val,b.val,σ,t.val⟩))))
def allSources : List Source := (List.finRange 11).flatMap blockSources
theorem encodedBlock00 : (blockSources 0).map encode=List.range' 0 726 := by decide +kernel
theorem decodedBlock00 : (blockSources 0).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock01 : (blockSources 1).map encode=List.range' 726 1200 := by decide +kernel
theorem decodedBlock01 : (blockSources 1).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock02 : (blockSources 2).map encode=List.range' 1926 2916 := by decide +kernel
theorem decodedBlock02 : (blockSources 2).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock03 : (blockSources 3).map encode=List.range' 4842 3840 := by decide +kernel
theorem decodedBlock03 : (blockSources 3).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock04 : (blockSources 4).map encode=List.range' 8682 5586 := by decide +kernel
theorem decodedBlock04 : (blockSources 4).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock05 : (blockSources 5).map encode=List.range' 14268 5832 := by decide +kernel
theorem decodedBlock05 : (blockSources 5).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock06 : (blockSources 6).map encode=List.range' 20100 6600 := by decide +kernel
theorem decodedBlock06 : (blockSources 6).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock07 : (blockSources 7).map encode=List.range' 26700 5760 := by decide +kernel
theorem decodedBlock07 : (blockSources 7).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock08 : (blockSources 8).map encode=List.range' 32460 4590 := by decide +kernel
theorem decodedBlock08 : (blockSources 8).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock09 : (blockSources 9).map encode=List.range' 37050 2592 := by decide +kernel
theorem decodedBlock09 : (blockSources 9).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel
theorem encodedBlock10 : (blockSources 10).map encode=List.range' 39642 870 := by decide +kernel
theorem decodedBlock10 : (blockSources 10).all (fun s => decide (decode (encode s)=s))=true := by decide +kernel

end ThomsonNine.ActualF.Data

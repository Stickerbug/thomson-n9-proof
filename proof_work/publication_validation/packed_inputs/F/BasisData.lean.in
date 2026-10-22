import Contact.Metadata
import Matrices.Model

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualF.BasisData
open ThomsonNine.CertificateMatrices
abbrev Triple := Fin 11 × Fin 11 × Fin 11

def allSources : List Triple := (List.finRange 11).flatMap (fun k =>
  (List.finRange (reducedDim k)).flatMap (fun i =>
    (List.finRange (reducedDim k)).map (fun j => (k,reducedIndex k i,reducedIndex k j))))
def left (h : Fin 190) : Triple := ((ActualContact.indices h).block,(ActualContact.indices h).left,(ActualContact.indices h).right)
def right (h : Fin 190) : Triple := ((ActualContact.indices h).block,(ActualContact.indices h).right,(ActualContact.indices h).left)
def offDiagonal (h : Fin 190) : Bool := (ActualContact.indices h).left≠(ActualContact.indices h).right
def group (h : Fin 190) : List Triple := [left h]++if offDiagonal h then [right h]else[]
def gathered : List Triple := (List.finRange 190).flatMap group

theorem partition : gathered.Perm allSources := by decide +kernel
theorem left_index : ∀ h : Fin 190,
    indices (left h).1 (left h).2.1 (left h).2.2=h := by decide +kernel
theorem right_index : ∀ h : Fin 190,
    indices (right h).1 (right h).2.1 (right h).2.2=h := by decide +kernel
end ThomsonNine.ActualF.BasisData

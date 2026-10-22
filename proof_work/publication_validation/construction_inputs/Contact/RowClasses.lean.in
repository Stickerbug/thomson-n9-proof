import ThomsonNine.Construction.Contact.WeightedDerivative

-- Isolated source: Contact.RowClasses
noncomputable section
namespace ThomsonNine.ActualContact

def rowClass : Fin 45 → Fin 12 := ![0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,6,6,6,7,7,7,8,8,8,8,9,9,9,10,10,10,10,11,11,11,11]
theorem rows_nodes_class : ∀ (row : Fin 45) (j : Fin 3),
    (rows row).nodes j=(rows (valueRows (rowClass row))).nodes j := by decide +kernel

theorem row_point_class (row : Fin 45) : point row=point (valueRows (rowClass row)) := by
  funext j
  exact congrArg ActualHermite.node (rows_nodes_class row j)

def classGradient (X : Fin 190 → ℝ) (j : Fin 12) (a : Fin 3) := contactGradient X (point (valueRows j)) a
theorem gradient_eq_class (X : Fin 190 → ℝ) (row : Fin 45) (a : Fin 3) :
    contactGradient X (point row) a=classGradient X (rowClass row) a :=
  congrArg (fun p => contactGradient X p a) (row_point_class row)
end ThomsonNine.ActualContact

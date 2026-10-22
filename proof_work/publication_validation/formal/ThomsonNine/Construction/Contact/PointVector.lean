import ThomsonNine.Construction.Contact.FJet

-- Isolated source: Contact.PointVector
noncomputable section
namespace ThomsonNine.ActualContact

theorem point_as_vector (row : Fin 45) : point row=
    ![ActualHermite.node ((rows row).nodes 0),ActualHermite.node ((rows row).nodes 1),ActualHermite.node ((rows row).nodes 2)] :=
  (point_eta (point row)).symm
end ThomsonNine.ActualContact

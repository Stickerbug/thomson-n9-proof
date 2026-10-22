import ThomsonNine.Construction.LocalInterior.C00.SourceBox
import ThomsonNine.Construction.LocalInterior.C01.SourceBox
import ThomsonNine.Construction.LocalInterior.C02.SourceBox
import ThomsonNine.Construction.LocalInterior.C03.SourceBox
import ThomsonNine.Construction.LocalInterior.C04.SourceBox
import ThomsonNine.Construction.LocalInterior.C05.SourceBox
import ThomsonNine.Construction.LocalBoundary.C06.Nonnegative
import ThomsonNine.Construction.LocalBoundary.C07.Nonnegative
import ThomsonNine.Construction.LocalInterior.C08.SourceBox
import ThomsonNine.Construction.LocalBoundary.C09.Nonnegative
import ThomsonNine.Construction.LocalInterior.C10.SourceBox
import ThomsonNine.Construction.LocalInterior.C11.SourceBox

-- Isolated source: LocalAll.Nonnegative
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.ActualLocal
def sourceBox : Fin 12 → Fin 3 → Interval.RatInterval := ![C00.sourceBox,C01.sourceBox,C02.sourceBox,C03.sourceBox,C04.sourceBox,C05.sourceBox,ActualBoundary.C06.sourceBox,ActualBoundary.C07.sourceBox,C08.sourceBox,ActualBoundary.C09.sourceBox,C10.sourceBox,C11.sourceBox]
theorem all_twelve_residual_nonnegative (localId : Fin 12) (p : Fin 3 → ℝ)
    (hp : ∀ a, (sourceBox localId a).mem (p a))
    (hg : 0≤Semantics.gram (p 0) (p 1) (p 2)) : 0≤ActualR.residual p := by
  fin_cases localId
  · exact C00.actual_residual_nonnegative_on_source p hp
  · exact C01.actual_residual_nonnegative_on_source p hp
  · exact C02.actual_residual_nonnegative_on_source p hp
  · exact C03.actual_residual_nonnegative_on_source p hp
  · exact C04.actual_residual_nonnegative_on_source p hp
  · exact C05.actual_residual_nonnegative_on_source p hp
  · exact ActualBoundary.C06.actual_residual_nonnegative p hp hg
  · exact ActualBoundary.C07.actual_residual_nonnegative p hp hg
  · exact C08.actual_residual_nonnegative_on_source p hp
  · exact ActualBoundary.C09.actual_residual_nonnegative p hp hg
  · exact C10.actual_residual_nonnegative_on_source p hp
  · exact C11.actual_residual_nonnegative_on_source p hp
end ThomsonNine.ActualLocal

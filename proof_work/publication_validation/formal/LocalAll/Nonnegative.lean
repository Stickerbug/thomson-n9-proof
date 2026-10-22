import LocalInterior.C00.SourceBox
import LocalInterior.C01.SourceBox
import LocalInterior.C02.SourceBox
import LocalInterior.C03.SourceBox
import LocalInterior.C04.SourceBox
import LocalInterior.C05.SourceBox
import LocalBoundary.C06.Nonnegative
import LocalBoundary.C07.Nonnegative
import LocalInterior.C08.SourceBox
import LocalBoundary.C09.Nonnegative
import LocalInterior.C10.SourceBox
import LocalInterior.C11.SourceBox
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

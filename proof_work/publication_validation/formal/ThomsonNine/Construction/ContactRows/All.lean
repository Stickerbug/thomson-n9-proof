import ThomsonNine.Construction.ContactRows.Row00
import ThomsonNine.Construction.ContactRows.Row01
import ThomsonNine.Construction.ContactRows.Row02
import ThomsonNine.Construction.ContactRows.Row03
import ThomsonNine.Construction.ContactRows.Row04
import ThomsonNine.Construction.ContactRows.Row05
import ThomsonNine.Construction.ContactRows.Row06
import ThomsonNine.Construction.ContactRows.Row07
import ThomsonNine.Construction.ContactRows.Row08
import ThomsonNine.Construction.ContactRows.Row09
import ThomsonNine.Construction.ContactRows.Row10
import ThomsonNine.Construction.ContactRows.Row11
import ThomsonNine.Construction.ContactRows.Row12
import ThomsonNine.Construction.ContactRows.Row13
import ThomsonNine.Construction.ContactRows.Row14
import ThomsonNine.Construction.ContactRows.Row15
import ThomsonNine.Construction.ContactRows.Row16
import ThomsonNine.Construction.ContactRows.Row17
import ThomsonNine.Construction.ContactRows.Row18
import ThomsonNine.Construction.ContactRows.Row19
import ThomsonNine.Construction.ContactRows.Row20
import ThomsonNine.Construction.ContactRows.Row21
import ThomsonNine.Construction.ContactRows.Row22
import ThomsonNine.Construction.ContactRows.Row23
import ThomsonNine.Construction.ContactRows.Row24
import ThomsonNine.Construction.ContactRows.Row25
import ThomsonNine.Construction.ContactRows.Row26
import ThomsonNine.Construction.ContactRows.Row27
import ThomsonNine.Construction.ContactRows.Row28
import ThomsonNine.Construction.ContactRows.Row29
import ThomsonNine.Construction.ContactRows.Row30
import ThomsonNine.Construction.ContactRows.Row31
import ThomsonNine.Construction.ContactRows.Row32

-- Isolated source: ContactRows.All
noncomputable section
namespace ThomsonNine.ActualContact.CachedRows
open ThomsonNine.ActualHermite.CoefficientData
def matrix : Fin 33 → Fin 190 → FixedInterval.Bounds := ![
Row00.cachedM,
Row01.cachedM,
Row02.cachedM,
Row03.cachedM,
Row04.cachedM,
Row05.cachedM,
Row06.cachedM,
Row07.cachedM,
Row08.cachedM,
Row09.cachedM,
Row10.cachedM,
Row11.cachedM,
Row12.cachedM,
Row13.cachedM,
Row14.cachedM,
Row15.cachedM,
Row16.cachedM,
Row17.cachedM,
Row18.cachedM,
Row19.cachedM,
Row20.cachedM,
Row21.cachedM,
Row22.cachedM,
Row23.cachedM,
Row24.cachedM,
Row25.cachedM,
Row26.cachedM,
Row27.cachedM,
Row28.cachedM,
Row29.cachedM,
Row30.cachedM,
Row31.cachedM,
Row32.cachedM
]
theorem matrix_mem (i : Fin 33) (h : Fin 190) : FixedInterval.Mem unitScale (matrix i h) (M (selectedRows i) h) := by
  fin_cases i
  · exact Row00.cachedM_mem h
  · exact Row01.cachedM_mem h
  · exact Row02.cachedM_mem h
  · exact Row03.cachedM_mem h
  · exact Row04.cachedM_mem h
  · exact Row05.cachedM_mem h
  · exact Row06.cachedM_mem h
  · exact Row07.cachedM_mem h
  · exact Row08.cachedM_mem h
  · exact Row09.cachedM_mem h
  · exact Row10.cachedM_mem h
  · exact Row11.cachedM_mem h
  · exact Row12.cachedM_mem h
  · exact Row13.cachedM_mem h
  · exact Row14.cachedM_mem h
  · exact Row15.cachedM_mem h
  · exact Row16.cachedM_mem h
  · exact Row17.cachedM_mem h
  · exact Row18.cachedM_mem h
  · exact Row19.cachedM_mem h
  · exact Row20.cachedM_mem h
  · exact Row21.cachedM_mem h
  · exact Row22.cachedM_mem h
  · exact Row23.cachedM_mem h
  · exact Row24.cachedM_mem h
  · exact Row25.cachedM_mem h
  · exact Row26.cachedM_mem h
  · exact Row27.cachedM_mem h
  · exact Row28.cachedM_mem h
  · exact Row29.cachedM_mem h
  · exact Row30.cachedM_mem h
  · exact Row31.cachedM_mem h
  · exact Row32.cachedM_mem h
end ThomsonNine.ActualContact.CachedRows

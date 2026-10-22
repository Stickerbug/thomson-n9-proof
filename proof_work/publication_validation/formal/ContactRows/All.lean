import ContactRows.Row00
import ContactRows.Row01
import ContactRows.Row02
import ContactRows.Row03
import ContactRows.Row04
import ContactRows.Row05
import ContactRows.Row06
import ContactRows.Row07
import ContactRows.Row08
import ContactRows.Row09
import ContactRows.Row10
import ContactRows.Row11
import ContactRows.Row12
import ContactRows.Row13
import ContactRows.Row14
import ContactRows.Row15
import ContactRows.Row16
import ContactRows.Row17
import ContactRows.Row18
import ContactRows.Row19
import ContactRows.Row20
import ContactRows.Row21
import ContactRows.Row22
import ContactRows.Row23
import ContactRows.Row24
import ContactRows.Row25
import ContactRows.Row26
import ContactRows.Row27
import ContactRows.Row28
import ContactRows.Row29
import ContactRows.Row30
import ContactRows.Row31
import ContactRows.Row32
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

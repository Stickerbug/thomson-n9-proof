import MainCoverage.GramInput
namespace ThomsonNine.PackedMain
def penalty : Fin 4 → ℚ := ![(0/1 : ℚ),(44042624479030570480523/10000000000000000000000000 : ℚ),(192182733082245821773/2000000000000000000000000 : ℚ),(999991174568109501/10000000000000000000000000 : ℚ)]
theorem penalty_nonnegative : ∀ q : Fin 4, 0≤penalty q := by decide +kernel
end ThomsonNine.PackedMain

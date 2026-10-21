import ThomsonNine.LocalSparseHessianAAABase

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace ThomsonNine.LocalSparseHessianAAA

open ThomsonNine.Interval ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.Interval.RatInterval

private def qAlo : ℚ := (-23260502653412395759915218865887494744431862527651078925437095781474179809304552915249143548774931355781057660296672958897719859738712896646146006642599758158139526313133054327771569251144888407 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi : ℚ := (-5815125663353098939978804716471873686107965631912769731359273945368544952326138228812285887193732838945264415074168239724429964918744073688840377613066752743560091396224696993086835636439887069 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qCabs : ℚ := (23260502653412395759915218865887494744431862527651078925437095781474179809304552915249143548774931355781057660296672958897719859738712896646146006642599758158139526313133054327771569251144888407 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qR3 : ℚ := (4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399787515795978901507518321381491904736963963218846616770044231309886583077782138141511 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qR2 : ℚ := (4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399781600138375363440713232930311551870986822847162020399473578433078434535894101296631830069 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qB : ℚ := (46521005306824791519830437731774989488863725055302157850874191562948359618609105830498287097549862711682753532389285913108563824914898577450888487172058978637117291670980913406283537 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)

example (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : ∀ i n, (powerTable n).mem (x i ^ n)) :
    |hessianTerm c x .t288| ≤ (qB : ℝ) := by
  have hA := hC .t288
  have hAlo : (coefficientInterval .t288).lo = qAlo := rfl
  have hAhi : (coefficientInterval .t288).hi = qAhi := rfl
  have h1 : (-qCabs : ℚ) ≤ qAlo := by
    rw [Rat.le_iff]; norm_num [qCabs, qAlo]
  have h2 : qAhi ≤ qCabs := by
    rw [Rat.le_iff]; norm_num [qAhi, qCabs]
  have hcabs : |c .t288| ≤ (qCabs : ℝ) := by
    apply abs_le.mpr
    constructor
    · have h1' : (-qCabs : ℝ) ≤ (qAlo : ℝ) := by exact_mod_cast h1
      have hA1 := hA.1
      rw [hAlo] at hA1
      exact le_trans h1' hA1
    · have h2' : (qAhi : ℝ) ≤ (qCabs : ℝ) := by exact_mod_cast h2
      have hA2 := hA.2
      rw [hAhi] at hA2
      exact le_trans hA2 h2'
  have hp3 : |x 1 ^ 3| ≤ (qR3 : ℝ) := by
    have h := hP 1 3
    have htab : powerTable 3 = power_03 := by simp [powerTable, finitePower]
    rw [htab] at h
    apply abs_le.mpr
    constructor
    · have hlo : (-qR3 : ℚ) ≤ power_03.lo := by
        rw [Rat.le_iff]; norm_num [qR3, power_03]
      exact le_trans (by exact_mod_cast hlo) h.1
    · have hhi : power_03.hi ≤ qR3 := by
        rw [Rat.le_iff]; norm_num [qR3, power_03]
      exact le_trans h.2 (by exact_mod_cast hhi)
  have hp2 : |x 2 ^ 1| ≤ (qR2 : ℝ) := by
    have h := hP 2 1
    have htab : powerTable 1 = power_01 := by simp [powerTable, finitePower]
    rw [htab] at h
    apply abs_le.mpr
    constructor
    · have hlo : (-qR2 : ℚ) ≤ power_01.lo := by
        rw [Rat.le_iff]; norm_num [qR2, power_01]
      exact le_trans (by exact_mod_cast hlo) h.1
    · have hhi : power_01.hi ≤ qR2 := by
        rw [Rat.le_iff]; norm_num [qR2, power_01]
      exact le_trans h.2 (by exact_mod_cast hhi)
  have hterm : hessianTerm c x .t288 = c .t288 * 2 * (x 1 ^ 3 * x 2 ^ 1) := by
    unfold hessianTerm
    rw [show exponents .t288 = ![2, 3, 1] from rfl]
    simp [lowerExponent, derivativeCoeff, monomial]
  have hM : |x 1 ^ 3 * x 2 ^ 1| ≤ (qR3 * qR2 : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hp3 hp2 (abs_nonneg _) (by exact_mod_cast (show (0 : ℚ) ≤ qR3 by rw [Rat.le_iff]; norm_num [qR3, power_03]))
  have hc2 : |c .t288| * 2 ≤ (qCabs * 2 : ℝ) := by
    exact mul_le_mul_of_nonneg_right hcabs (by norm_num)
  have hprod : |c .t288 * 2 * (x 1 ^ 3 * x 2 ^ 1)| ≤
      ((qCabs * 2 * qR3 * qR2 : ℚ) : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc |c .t288| * 2 * |x 1 ^ 3 * x 2 ^ 1|
        = (|c .t288| * 2) * |x 1 ^ 3 * x 2 ^ 1| := by ring
      _ ≤ (qCabs * 2) * (qR3 * qR2) :=
          mul_le_mul hc2 hM (abs_nonneg _) (by exact_mod_cast (show (0 : ℚ) ≤ qCabs * 2 by norm_num [qCabs]))
      _ = ((qCabs * 2 * qR3 * qR2 : ℚ) : ℝ) := by push_cast; ring
  have hB : (qCabs * 2 * qR3 * qR2 : ℚ) ≤ qB := by
    rw [Rat.le_iff]; norm_num [qCabs, qR3, qR2, qB]
  calc |hessianTerm c x .t288|
      = |c .t288 * 2 * (x 1 ^ 3 * x 2 ^ 1)| := by rw [hterm]
    _ ≤ ((qCabs * 2 * qR3 * qR2 : ℚ) : ℝ) := hprod
    _ ≤ (qB : ℝ) := by exact_mod_cast hB

end ThomsonNine.LocalSparseHessianAAA

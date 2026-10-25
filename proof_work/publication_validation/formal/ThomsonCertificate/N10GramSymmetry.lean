import ThomsonCertificate.N10TripleBoundary

namespace ThomsonTen

open ThomsonNine.ThreePoint

theorem gramDet_swap_uv (u v t : ℝ) :
    gramDet v u t = gramDet u v t := by
  simp [gramDet]
  ring

theorem gramDet_swap_ut (u v t : ℝ) :
    gramDet t v u = gramDet u v t := by
  simp [gramDet]
  ring

theorem gramDet_swap_vt (u v t : ℝ) :
    gramDet u t v = gramDet u v t := by
  simp [gramDet]
  ring

theorem gramOK_swap_uv {u v t : ℝ} :
    GramOK u v t → GramOK v u t := by
  intro h
  rw [gramOK_uses_gramDet] at h ⊢
  rcases h with ⟨hu, hv, ht, hd⟩
  exact ⟨hv, hu, ht, by simpa [gramDet_swap_uv] using hd⟩

theorem gramOK_swap_ut {u v t : ℝ} :
    GramOK u v t → GramOK t v u := by
  intro h
  rw [gramOK_uses_gramDet] at h ⊢
  rcases h with ⟨hu, hv, ht, hd⟩
  exact ⟨ht, hv, hu, by simpa [gramDet_swap_ut] using hd⟩

theorem gramOK_swap_vt {u v t : ℝ} :
    GramOK u v t → GramOK u t v := by
  intro h
  rw [gramOK_uses_gramDet] at h ⊢
  rcases h with ⟨hu, hv, ht, hd⟩
  exact ⟨hu, ht, hv, by simpa [gramDet_swap_vt] using hd⟩

theorem gramDet_lower_ring_type_nonneg (h : ℝ) :
    0 ≤ gramDet (-h) (-h) (h^2) := by
  rw [gramDet_lower_ring_type]
  positivity

theorem gramOK_poles_ring {h : ℝ} (hh0 : -1 ≤ h) (hh1 : h ≤ 1) :
    GramOK (-1) (-h) h := by
  rw [gramOK_uses_gramDet]
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (h + 1), sq_nonneg (1 - h)]
  · nlinarith [sq_nonneg (h + 1), sq_nonneg (1 - h)]
  · rw [gramDet_poles_ring]

theorem gramOK_lower_ring {h : ℝ} (hh0 : -1 ≤ h) (hh1 : h ≤ 1) :
    GramOK (-h) (-h) (h^2) := by
  have hsq : h^2 ≤ 1 := by
    have hp : 0 ≤ h + 1 := by linarith
    have hm : 0 ≤ 1 - h := by linarith
    nlinarith [mul_nonneg hp hm]
  rw [gramOK_uses_gramDet]
  refine ⟨?_, ?_, ?_, gramDet_lower_ring_type_nonneg h⟩
  · nlinarith [hsq]
  · nlinarith [sq_nonneg (h + 1), sq_nonneg (1 - h)]
  · nlinarith [sq_nonneg (h + 1), sq_nonneg (1 - h)]

end ThomsonTen

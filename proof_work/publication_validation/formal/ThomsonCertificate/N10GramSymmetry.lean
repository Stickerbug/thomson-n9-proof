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

end ThomsonTen

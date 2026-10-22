import PackedTensor.AffineMatrix
import PackedTensor.Linear

noncomputable section
namespace ThomsonNine.PackedTensor
open scoped BigOperators
open ThomsonNine.PackedRadix

def scaledInt {d : ℕ} (b : CubeIndex d → ℤ) (den : ℕ) : CubeIndex d → ℝ := fun p => (b p : ℝ)/(den : ℝ)

theorem scaled_mapAxis {d : ℕ} (M : Fin d → Fin d → ℤ) (axis : Fin 3) (b : CubeIndex d → ℤ)
    (mDen bDen : ℕ) :
    mapAxis (fun i j => (M i j : ℝ)/(mDen : ℝ)) axis (scaledInt b bDen)=
      scaledInt (mapAxisInt M axis b) (mDen*bDen) := by
  funext p
  change mapAxis (fun i j => (M i j : ℝ)/(mDen : ℝ)) axis (fun q => (b q : ℝ)/(bDen : ℝ)) p=
    (mapAxisInt M axis b p : ℝ)/((mDen*bDen : ℕ) : ℝ)
  simpa only [Nat.cast_mul] using mapAxis_cast M axis b mDen bDen p

theorem integer_tensor_transform (n : ℕ) (M : Fin (n+1) → Fin (n+1) → ℚ)
    (MI : Fin (n+1) → Fin (n+1) → ℤ) (mDen : ℕ) (l w : ℚ)
    (hM : ∀ i j, M i j=(MI i j : ℚ)/(mDen : ℚ)) (hSpec : affineMatrixSpec n M l w)
    (b0 b1 b2 b3 : CubeIndex (n+1) → ℤ) (den : ℕ)
    (h1 : ∀ p, b1 p=mapAxisInt MI 0 b0 p)
    (h2 : ∀ p, b2 p=mapAxisInt MI 1 b1 p)
    (h3 : ∀ p, b3 p=mapAxisInt MI 2 b2 p) (z : Fin 3 → ℝ) :
    tensorValue n (scaledInt b3 (mDen*(mDen*(mDen*den)))) z=
      tri (scaledInt b0 den) (fun i => ((l : ℝ)+(w : ℝ)*z 0)^i.val)
        (fun j => ((l : ℝ)+(w : ℝ)*z 1)^j.val) (fun k => ((l : ℝ)+(w : ℝ)*z 2)^k.val) := by
  have hm : (fun i j => (M i j : ℝ))=(fun i j => (MI i j : ℝ)/(mDen : ℝ)) := by
    funext i j
    exact_mod_cast hM i j
  have H1 : mapAxis (fun i j => (MI i j : ℝ)/(mDen : ℝ)) 0 (scaledInt b0 den)=scaledInt b1 (mDen*den) := by
    rw [scaled_mapAxis,← funext h1]
  have H2 : mapAxis (fun i j => (MI i j : ℝ)/(mDen : ℝ)) 1 (scaledInt b1 (mDen*den))=
      scaledInt b2 (mDen*(mDen*den)) := by rw [scaled_mapAxis,← funext h2]
  have H3 : mapAxis (fun i j => (MI i j : ℝ)/(mDen : ℝ)) 2 (scaledInt b2 (mDen*(mDen*den)))=
      scaledInt b3 (mDen*(mDen*(mDen*den))) := by rw [scaled_mapAxis,← funext h3]
  have he := affine_tensor_transform n M l w hSpec (scaledInt b0 den) z
  rw [hm,H1,H2,H3] at he
  exact he

theorem integer_comparison (encoded offset scale den : ℕ) (v : ℤ)
    (hs : (0 : ℝ)<scale) (hd : (0 : ℝ)<den)
    (h : ((encoded : ℤ)-(offset : ℤ))*(den : ℤ)≤(scale : ℤ)*v) :
    ((encoded : ℝ)-(offset : ℝ))/(scale : ℝ)≤(v : ℝ)/(den : ℝ) := by
  have hr : ((encoded : ℝ)-(offset : ℝ))*(den : ℝ)≤(scale : ℝ)*(v : ℝ) := by exact_mod_cast h
  apply (div_le_div_iff₀ hs hd).mpr
  simpa only [mul_comm] using hr

theorem packet_lower_integer (n offset scale den packet : ℕ) (v : CubeIndex (n+1) → ℤ)
    (hs : (0 : ℝ)<scale) (hd : (0 : ℝ)<den)
    (h : ∀ p, ((limb 128 packet (flat p) : ℤ)-(offset : ℤ))*(den : ℤ)≤(scale : ℤ)*v p)
    (z : Fin 3 → ℝ) (hz : ∀ a, 0≤z a ∧ z a≤1) :
    packetValue n offset scale packet z≤tensorValue n (scaledInt v den) z := by
  have hc (p : CubeIndex (n+1)) := integer_comparison (limb 128 packet (flat p)) offset scale den (v p) hs hd (h p)
  exact tensor_mono n _ _ hc z hz

theorem integer_curve_transform (n : ℕ) (M : Fin (n+1) → Fin (n+1) → ℚ)
    (MI : Fin (n+1) → Fin (n+1) → ℤ) (mDen : ℕ) (l w : ℚ)
    (hM : ∀ i j, M i j=(MI i j : ℚ)/(mDen : ℚ)) (hSpec : affineMatrixSpec n M l w)
    (v0 v1 : Fin (n+1) → ℤ) (den : ℕ) (hv : ∀ i, v1 i=∑ j, MI i j*v0 j) (s : ℝ) :
    curve n (fun i => (v1 i : ℝ)/((mDen*den : ℕ) : ℝ)) s=
      ∑ j : Fin (n+1), ((v0 j : ℝ)/(den : ℝ))*((l : ℝ)+(w : ℝ)*s)^j.val := by
  have hm (i j : Fin (n+1)) : (M i j : ℝ)=(MI i j : ℝ)/(mDen : ℝ) := by exact_mod_cast hM i j
  have hc (i : Fin (n+1)) : (v1 i : ℝ)/((mDen*den : ℕ) : ℝ)=
      ∑ j, (M i j : ℝ)*((v0 j : ℝ)/(den : ℝ)) := by
    simp only [hv i,Int.cast_sum,Int.cast_mul,Nat.cast_mul,hm,div_mul_div_comm,Finset.sum_div]
  rw [funext hc,curve_map]
  simp_rw [affineMatrixSpec_sound n M l w hSpec]
end ThomsonNine.PackedTensor

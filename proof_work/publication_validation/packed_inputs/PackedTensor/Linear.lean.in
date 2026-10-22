import PackedTensor.Positive
import PackedTensor.Broadcast

noncomputable section
namespace ThomsonNine.PackedTensor
open scoped BigOperators
open ThomsonNine.PackedRadix

theorem tensor_add (n : ℕ) (b c : CubeIndex (n+1) → ℝ) (x : Fin 3 → ℝ) :
    tensorValue n (fun p => b p+c p) x=tensorValue n b x+tensorValue n c x := by
  simp only [tensorValue,Semantics.tensor,add_mul,Finset.sum_add_distrib]

theorem curve_div (n : ℕ) (b : Fin (n+1) → ℝ) (S s : ℝ) :
    curve n (fun i => b i/S) s=curve n b s/S := by
  simp only [curve,div_mul_eq_mul_div,Finset.sum_div]
theorem curve_neg (n : ℕ) (b : Fin (n+1) → ℝ) (s : ℝ) :
    curve n (fun i => -b i) s= -curve n b s := by
  simp only [curve,neg_mul,Finset.sum_neg_distrib]

theorem tensor_sum {α : Type*} (n : ℕ) (s : Finset α) (b : α → CubeIndex (n+1) → ℝ) (x : Fin 3 → ℝ) :
    tensorValue n (fun p => ∑ a∈s, b a p) x=∑ a∈s, tensorValue n (b a) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensorValue,Semantics.tensor]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,tensor_add,ih]

theorem tensor_constant (n : ℕ) (c : ℝ) (x : Fin 3 → ℝ) : tensorValue n (fun _ => c) x=c := by
  have h := tensor_axis0 n (fun _ => c) x
  simpa only [curve,← Finset.mul_sum,bernstein_sum_one,mul_one] using h

theorem broadcast_value (n lanes g offset scale : ℕ) (planes : Fin 3 → Fin (n+1) → ℕ)
    (hplanes : PlaneSpec planes) (a : Fin 3) (values : Fin (n+1) → ℕ) (packet : ℕ)
    (hn : (n+1)*(n+1)*(n+1)≤lanes) (h : broadcastOK lanes g planes a values packet=true)
    (x : Fin 3 → ℝ) :
    packetValue n offset scale packet x=
      curve n (fun i => ((values i : ℝ)-(offset : ℝ))/(scale : ℝ)) (x a) := by
  have hc : packetCoefficients n offset scale packet=
      fun p => ((values (coord a p) : ℝ)-(offset : ℝ))/(scale : ℝ) := by
    funext p
    simp only [packetCoefficients,decode,broadcast_sound lanes g planes hplanes a values packet hn h p]
  rw [packetValue,hc]
  exact tensor_axis n (fun i => ((values i : ℝ)-(offset : ℝ))/(scale : ℝ)) a x

theorem packet_value_ge (n offset scale packet : ℕ) (c : ℝ)
    (hc : ∀ p, c≤packetCoefficients n offset scale packet p)
    (x : Fin 3 → ℝ) (hx : ∀ a, 0≤x a ∧ x a≤1) : c≤packetValue n offset scale packet x := by
  exact (tensor_constant n c x).symm.trans_le (tensor_mono n _ _ hc x hx)

theorem packet_value_floor (n offset scale packet : ℕ) (hs : (0:ℝ)<scale)
    (x : Fin 3 → ℝ) (hx : ∀ a, 0≤x a ∧ x a≤1) :
    -(offset : ℝ)/(scale : ℝ)≤packetValue n offset scale packet x := by
  have hc (p : CubeIndex (n+1)) : -(offset : ℝ)/(scale : ℝ)≤packetCoefficients n offset scale packet p := by
    unfold packetCoefficients decode
    apply (div_le_div_iff_of_pos_right hs).mpr
    have hh : (0:ℝ)≤(limb 128 packet (flat p) : ℝ) := Nat.cast_nonneg _
    linarith
  exact packet_value_ge n offset scale packet _ hc x hx

attribute [local irreducible] packetValue

theorem four_packet_positive (n lanes g offset scale : ℕ)
    (planes : Fin 3 → Fin (n+1) → ℕ) (hplanes : PlaneSpec planes)
    (K B0 B1 B2 : ℕ) (values0 values1 values2 : Fin (n+1) → ℕ)
    (hb0 : broadcastOK lanes g planes 0 values0 B0=true)
    (hb1 : broadcastOK lanes g planes 1 values1 B1=true)
    (hb2 : broadcastOK lanes g planes 2 values2 B2=true)
    (hg : 4*g<2^128) (hbias : 4*offset<2^128)
    (h : positiveSumOK 128 lanes g (4*offset) 4 (![K,B0,B1,B2] : Fin 4 → ℕ)=true)
    (hs : (0 : ℝ)<scale) (hn : (n+1)*(n+1)*(n+1)≤lanes)
    (x : Fin 3 → ℝ) (hx : ∀ a, 0≤x a ∧ x a≤1) :
    0≤packetValue n offset scale K x+
      curve n (fun i => ((values0 i : ℝ)-(offset : ℝ))/(scale : ℝ)) (x 0)+
      curve n (fun i => ((values1 i : ℝ)-(offset : ℝ))/(scale : ℝ)) (x 1)+
      curve n (fun i => ((values2 i : ℝ)-(offset : ℝ))/(scale : ℝ)) (x 2) := by
  let packets : Fin 4 → ℕ := ![K,B0,B1,B2]
  have hp := packet_sum_nonnegative n lanes g offset scale 4 packets hg hbias h hs hn x hx
  rw [tensor_sum] at hp
  have hrefold (packet : ℕ) : tensorValue n (packetCoefficients n offset scale packet) x=
      packetValue n offset scale packet x := by unfold packetValue;rfl
  simp only [hrefold,Fin.sum_univ_succ,Fin.sum_univ_zero,packets,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero] at hp
  have hv0 := broadcast_value n lanes g offset scale planes hplanes 0 values0 B0 hn hb0 x
  have hv1 := broadcast_value n lanes g offset scale planes hplanes 1 values1 B1 hn hb1 x
  have hv2 := broadcast_value n lanes g offset scale planes hplanes 2 values2 B2 hn hb2 x
  linarith only [hp,hv0,hv1,hv2]
end ThomsonNine.PackedTensor

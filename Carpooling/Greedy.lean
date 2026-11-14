import Carpooling.Permutohedron

/-!
  The scale-free post-drift greedy rule preserves every scaled permutohedron
  `P_m(B)` with `B ≥ (m-1)d/2` (carpooling paper Theorem 4.2), and its relative
  interior when `m ≥ 3` (Remark 4.3).
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- Real-arithmetic core of Theorem 4.2: with `c = 1/(m-1)`, the greedy
    minimality, `x_k + x(A) ≤ 1`, `d ≤ 2Bc`, and Lemma 4.1 combine into the
    per-subset slack inequality. -/
lemma greedy_core {p B d c qk xk qAS qA0 xA b0 b1 b2 : ℝ}
    (hp : 0 ≤ p) (hd : 0 ≤ d) (hdB : d ≤ 2 * B * c)
    (hmin : p * (qk - d * xk) ≤ qAS - d * xA) (hx : xk + xA ≤ 1)
    (hid : (p + 1) * b0 - p * b1 - b2 = p * (p + 1) * c) :
    p * (qk + (qAS + qA0) + B * b1) + (qA0 + B * b2) + B * p * (p - 1) * c ≤
      (p + 1) * ((qAS + qA0 - d * xA) + B * b0) := by
  have F1 : p * d * (xk + xA) ≤ p * d := by
    have h := mul_le_mul_of_nonneg_left hx (mul_nonneg hp hd)
    linarith
  have F2 : p * d ≤ p * (2 * B * c) := mul_le_mul_of_nonneg_left hdB hp
  have F3 : B * ((p + 1) * b0 - p * b1 - b2) = B * (p * (p + 1) * c) := by rw [hid]
  linarith [F1, F2, F3, hmin]

/-- `p (p - 1) ≥ 0` for a natural number `p`. -/
lemma nat_mul_pred_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith

/-- Per-subset slack inequality behind Theorem 4.2. For a greedy `k ∉ A`, with
    `A_S = A ∩ supp x`, `p = |A_S|` and `A_0 = A \ supp x`,
    `(p+1)(q'(A) + Bβ_{|A|}) ≥ p (q(A ∪ {k}) + Bβ_{|A|+1})
      + (q(A_0) + Bβ_{|A_0|}) + B p (p-1)/(m-1)`. -/
lemma greedy_slack (hm : 2 ≤ m) {B d : ℝ} (hd : 0 ≤ d)
    (hdB : d ≤ 2 / ((m : ℝ) - 1) * B) {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : (∑ i, x i) = 1) {q : Fin m → ℝ} {k : Fin m} (hk : IsGreedy d x q k)
    {A AS A0 : Finset (Fin m)} (hkA : k ∉ A)
    (hAS : AS = A.filter (fun i => i ∈ supp x))
    (hA0 : A0 = A.filter (fun i => i ∉ supp x)) :
    (AS.card : ℝ) * ((∑ i ∈ insert k A, q i) + B * beta m (insert k A).card) +
        ((∑ i ∈ A0, q i) + B * beta m A0.card) +
        B * AS.card * (AS.card - 1) / ((m : ℝ) - 1) ≤
      ((AS.card : ℝ) + 1) * ((∑ i ∈ A, step d x k q i) + B * beta m A.card) := by
  set c : ℝ := ((m : ℝ) - 1)⁻¹ with hc
  set p : ℝ := (AS.card : ℝ) with hp
  have hsplit_q : (∑ i ∈ A, q i) = (∑ i ∈ AS, q i) + ∑ i ∈ A0, q i := by
    rw [hAS, hA0, Finset.sum_filter_add_sum_filter_not]
  have hsplit_card : AS.card + A0.card = A.card := by
    rw [hAS, hA0, Finset.card_filter_add_card_filter_not]
  have hxA0 : (∑ i ∈ A0, x i) = 0 :=
    sum_eq_zero_of_disjoint_supp fun i hi => by
      rw [hA0, Finset.mem_filter] at hi
      exact hi.2
  have hxA : (∑ i ∈ A, x i) = ∑ i ∈ AS, x i := by
    rw [hAS, ← Finset.sum_filter_add_sum_filter_not A (fun i => i ∈ supp x) x, ← hA0, hxA0,
      add_zero]
  have hstepA : (∑ i ∈ A, step d x k q i) = (∑ i ∈ A, q i) - d * ∑ i ∈ A, x i := by
    rw [sum_step, if_neg hkA]
    ring
  have hins_q : (∑ i ∈ insert k A, q i) = q k + ∑ i ∈ A, q i := Finset.sum_insert hkA
  have hins_x : x k + ∑ i ∈ A, x i ≤ 1 := by
    have h := sum_subset_le_one hx0 hx1 (insert k A)
    rwa [Finset.sum_insert hkA] at h
  have hmin : p * (q k - d * x k) ≤ (∑ i ∈ AS, q i) - d * ∑ i ∈ A, x i := by
    have h := Finset.card_nsmul_le_sum AS (fun i => q i - d * x i) (q k - d * x k)
      (fun i hi => by
        rw [hAS, Finset.mem_filter] at hi
        exact hk.2 i hi.2)
    rw [nsmul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
    rw [hxA]
    exact h
  have hb1 : beta m ((insert k A).card : ℝ) = beta m ((A.card : ℝ) + 1) := by
    rw [Finset.card_insert_of_notMem hkA]
    push_cast
    rfl
  have hb2 : beta m (A0.card : ℝ) = beta m ((A.card : ℝ) - p) := by
    have h : (A0.card : ℝ) = (A.card : ℝ) - (AS.card : ℝ) := by
      rw [← hsplit_card]
      push_cast
      ring
    rw [h]
  have hid := beta_exchange hm (A.card : ℝ) p
  rw [div_eq_mul_inv] at hid
  have hdB' : d ≤ 2 * B * c := by
    rw [hc]
    rw [div_mul_eq_mul_div, div_eq_mul_inv] at hdB
    linarith
  have core := greedy_core (p := p) (B := B) (d := d) (c := c) (qk := q k) (xk := x k)
    (qAS := ∑ i ∈ AS, q i) (qA0 := ∑ i ∈ A0, q i) (xA := ∑ i ∈ A, x i)
    (b0 := beta m (A.card : ℝ)) (b1 := beta m ((A.card : ℝ) + 1))
    (b2 := beta m ((A.card : ℝ) - p))
    (Nat.cast_nonneg _) hd hdB' hmin hins_x hid
  rw [hins_q, hb1, hb2, hstepA, hsplit_q]
  have hdiv : B * p * (p - 1) / ((m : ℝ) - 1) = B * p * (p - 1) * c := by
    rw [hc, div_eq_mul_inv]
  rw [hdiv]
  linarith [core]

/-- `0 ≤ X` from `0 ≤ (p + 1) X` with `p ≥ 0`. -/
lemma nonneg_of_succ_mul_nonneg {p X : ℝ} (hp : 0 ≤ p) (h : 0 ≤ (p + 1) * X) : 0 ≤ X :=
  (mul_nonneg_iff_of_pos_left (by linarith)).mp h

/-- **Theorem 4.2 (scale-free post-drift greedy invariance).** If `q ∈ P_m(B)`
    and `0 ≤ d ≤ 2B/(m-1)`, every greedy choice `k ∈ argmin_{k ∈ S} (q_k - d x_k)`
    keeps the successor in `P_m(B)`. The rule does not depend on `B`. -/
theorem greedy_mem_Pm (hm : 2 ≤ m) {B d : ℝ} (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hdB : d ≤ 2 / ((m : ℝ) - 1) * B) {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : (∑ i, x i) = 1) {q : Fin m → ℝ} (hq : q ∈ Pm m B) {k : Fin m}
    (hk : IsGreedy d x q k) : step d x k q ∈ Pm m B := by
  refine ⟨by rw [sum_step_univ hx1]; exact hq.1, fun A => ?_⟩
  have hqA := hq.2
  simp only at hqA ⊢
  by_cases hkA : k ∈ A
  · rw [sum_step, if_pos hkA]
    have h1 := hqA A
    have h2 := mul_nonneg hd (sub_nonneg.mpr (sum_subset_le_one hx0 hx1 A))
    linarith
  · have hs := greedy_slack hm hd hdB hx0 hx1 hk hkA rfl rfl
    set p : ℝ := ((A.filter (fun i => i ∈ supp x)).card : ℝ) with hp
    have hp0 : 0 ≤ p := Nat.cast_nonneg _
    have hslack : 0 ≤ B * p * (p - 1) / ((m : ℝ) - 1) := by
      apply div_nonneg _ (cast_sub_one_pos hm).le
      rw [mul_assoc]
      exact mul_nonneg hB (nat_mul_pred_nonneg _)
    have h1 := hqA (insert k A)
    have h2 := hqA (A.filter (fun i => i ∉ supp x))
    have h3 : 0 ≤ p * ((∑ i ∈ insert k A, q i) + B * beta m (insert k A).card) :=
      mul_nonneg hp0 (by linarith)
    have h4 : 0 ≤ (∑ i ∈ A, step d x k q i) + B * beta m A.card :=
      nonneg_of_succ_mul_nonneg hp0 (by linarith)
    linarith

/-- **Remark 4.3 (strict interior preservation).** For `m ≥ 3` and `B > 0`,
    greedy steps keep `relint P_m(B)` invariant. -/
theorem greedy_mem_relintPm (hm : 3 ≤ m) {B d : ℝ} (hB : 0 < B) (hd : 0 ≤ d)
    (hdB : d ≤ 2 / ((m : ℝ) - 1) * B) {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : (∑ i, x i) = 1) {q : Fin m → ℝ} (hq : q ∈ relintPm m B) {k : Fin m}
    (hk : IsGreedy d x q k) : step d x k q ∈ relintPm m B := by
  have hm2 : 2 ≤ m := by omega
  have hqP := relintPm_subset hm2 hq
  refine ⟨by rw [sum_step_univ hx1]; exact hq.1, fun A hA1 hAm => ?_⟩
  by_cases hkA : k ∈ A
  · rw [sum_step, if_pos hkA]
    have h1 := hq.2 A hA1 hAm
    have h2 := mul_nonneg hd (sub_nonneg.mpr (sum_subset_le_one hx0 hx1 A))
    linarith
  · set AS := A.filter (fun i => i ∈ supp x) with hAS
    set A0 := A.filter (fun i => i ∉ supp x) with hA0
    have hs := greedy_slack hm2 hd hdB hx0 hx1 hk hkA hAS hA0
    have hsplit_card : AS.card + A0.card = A.card := by
      rw [hAS, hA0, Finset.card_filter_add_card_filter_not]
    set p : ℝ := (AS.card : ℝ) with hp
    have hp0 : 0 ≤ p := Nat.cast_nonneg _
    have hslack : 0 ≤ B * p * (p - 1) / ((m : ℝ) - 1) := by
      apply div_nonneg _ (cast_sub_one_pos hm2).le
      rw [mul_assoc]
      exact mul_nonneg hB.le (nat_mul_pred_nonneg _)
    have h1 := hqP.2 (insert k A)
    have h2 := hqP.2 A0
    simp only at h1 h2
    have hcardI : (insert k A).card = A.card + 1 := Finset.card_insert_of_notMem hkA
    have hpos : 0 < (p + 1) * ((∑ i ∈ A, step d x k q i) + B * beta m A.card) := by
      rcases Nat.lt_or_ge AS.card 1 with hp1 | hp1
      · have hAS0 : AS.card = 0 := by omega
        have hA0c : A0.card = A.card := by omega
        have h2s := hq.2 A0 (by omega) (by omega)
        have hp00 : p = 0 := by rw [hp, hAS0, Nat.cast_zero]
        rw [hp00] at hs hslack ⊢
        linarith
      · rcases Nat.lt_or_ge 1 AS.card with hp2 | hp2
        · have hpp : 0 < B * p * (p - 1) / ((m : ℝ) - 1) := by
            apply div_pos _ (cast_sub_one_pos hm2)
            have : (2 : ℝ) ≤ p := by rw [hp]; exact_mod_cast hp2
            have : 0 < p * (p - 1) := by nlinarith
            rw [mul_assoc]
            exact mul_pos hB this
          have h3 : 0 ≤ p * ((∑ i ∈ insert k A, q i) + B * beta m (insert k A).card) :=
            mul_nonneg hp0 (by linarith)
          linarith
        · have hp1' : p = 1 := by
            rw [hp]
            exact_mod_cast (show AS.card = 1 by omega)
          rw [hp1'] at hs hslack ⊢
          by_cases hsmall : A.card + 1 ≤ m - 1
          · have h1s := hq.2 (insert k A) (by omega) (by omega)
            linarith
          · have h2s := hq.2 A0 (by omega) (by omega)
            linarith
    have hX : 0 < (∑ i ∈ A, step d x k q i) + B * beta m A.card :=
      (mul_pos_iff_of_pos_left (by linarith)).mp hpos
    linarith

end Carpooling

import FGPT.Theorem

/-!
  Support-function formulation (FGPT paper §7.3).
-/

open Finset

namespace FGPT

variable {m : ℕ}

/-- Support function of the move simplex `V_x = conv{e_k - x : k ∈ S}`,
    `h_{V_x}(u) = max_{k ∈ S} u_k - ⟨u, x⟩` (paper §7.3). -/
noncomputable def hV (x u : Fin m → ℝ) : ℝ :=
  (if h : (supp x).Nonempty then (supp x).sup' h u else 0) - ∑ i, u i * x i

/-- `h_{V_x}(-e_i) = x_i` when `s ≥ 2` (paper §7.3). -/
lemma hV_neg_single {x : Fin m → ℝ} (hs : 2 ≤ suppCard x) (i : Fin m) :
    hV x (-Pi.single i 1) = x i := by
  have h1 : 1 < (supp x).card := hs
  have hne : (supp x).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
  obtain ⟨k, hk, hki⟩ : ∃ k ∈ supp x, k ≠ i := by
    rcases eq_or_ne a i with rfl | hai
    · exact ⟨b, hb, hab.symm⟩
    · exact ⟨a, ha, hai⟩
  have hmax : (supp x).sup' hne (-Pi.single i (1 : ℝ)) = 0 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      simp only [Pi.neg_apply, Pi.single_apply]
      split_ifs <;> norm_num
    · have h := Finset.le_sup' (-Pi.single i (1 : ℝ)) hk
      have hv : (-Pi.single i (1 : ℝ) : Fin m → ℝ) k = 0 := by
        simp [hki]
      rw [hv] at h
      exact h
  have hsum : (∑ j, (-Pi.single i (1 : ℝ) : Fin m → ℝ) j * x j) = -x i := by
    simp [Pi.single_apply]
  rw [hV, dif_pos hne, hmax, hsum]
  ring

/-- `h_{V_x}(e_k) = 1 - x_k` for `k ∈ S` (paper §7.3). -/
lemma hV_single {x : Fin m → ℝ} {k : Fin m} (hk : k ∈ supp x) :
    hV x (Pi.single k 1) = 1 - x k := by
  have hne : (supp x).Nonempty := ⟨k, hk⟩
  have hmax : (supp x).sup' hne (Pi.single k (1 : ℝ)) = 1 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · have h := Finset.le_sup' (Pi.single k (1 : ℝ)) hk
      have hv : (Pi.single k (1 : ℝ) : Fin m → ℝ) k = 1 := by simp
      rw [hv] at h
      exact h
  have hsum : (∑ j, (Pi.single k (1 : ℝ) : Fin m → ℝ) j * x j) = x k := by
    simp [Pi.single_apply]
  rw [hV, dif_pos hne, hmax, hsum]

/-- `σ₂(x) = max_{i ≠ j} (h_{V_x}(-e_i) + h_{V_x}(-e_j))` (paper §7.3). -/
theorem sigma2_eq_hV {x : Fin m → ℝ} (hs : 2 ≤ suppCard x) :
    sigma2 x =
      if h : ((univ : Finset (Fin m)).offDiag).Nonempty then
        (univ : Finset (Fin m)).offDiag.sup' h
          (fun p => hV x (-Pi.single p.1 1) + hV x (-Pi.single p.2 1))
      else 0 := by
  unfold sigma2
  simp only [hV_neg_single hs]

/-- `s - 1 = ∑_{k ∈ S} h_{V_x}(e_k)` (paper §7.3). -/
theorem suppCard_sub_one_eq_hV {x : Fin m → ℝ} (hx1 : (∑ i, x i) = 1) :
    (suppCard x : ℝ) - 1 = ∑ k ∈ supp x, hV x (Pi.single k 1) := by
  have hsx1 : (∑ i ∈ supp x, x i) = 1 := by
    rw [← hx1]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    exact hi
  rw [Finset.sum_congr rfl (fun k hk => hV_single hk), Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one, hsx1, suppCard]

/-- Support function of a set `K`, `h_K(u) = sup_{q ∈ K} ⟨u, q⟩` (paper §7.3). -/
noncomputable def supportFun (K : Set (Fin m → ℝ)) (u : Fin m → ℝ) : ℝ :=
  sSup ((fun q => ∑ i, u i * q i) '' K)

/-- Indicator vector `1_A`. -/
def indicatorVec (A : Finset (Fin m)) : Fin m → ℝ :=
  fun i => if i ∈ A then 1 else 0

/-- The maximum of `q(A)` over `Q_m` is `min(r, m - r)` with `r = |A|`
    (paper §7.3). -/
lemma isGreatest_subset_sum_Qbox (A : Finset (Fin m)) :
    IsGreatest ((fun q => ∑ i ∈ A, q i) '' Qbox m)
      (min (A.card : ℝ) ((Aᶜ).card : ℝ)) := by
  set r : ℝ := (A.card : ℝ) with hr
  set n : ℝ := ((Aᶜ).card : ℝ) with hn
  set c : ℝ := min r n with hc
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hcr : c ≤ r := min_le_left _ _
  have hcn : c ≤ n := min_le_right _ _
  have hc0 : 0 ≤ c := le_min hr0 hn0
  have hrc : r * (c / r) = c := by
    rcases eq_or_ne r 0 with h | h
    · have : c = 0 := le_antisymm (h ▸ hcr) hc0
      rw [h, this]
      ring
    · field_simp
  have hnc : n * (c / n) = c := by
    rcases eq_or_ne n 0 with h | h
    · have : c = 0 := le_antisymm (h ▸ hcn) hc0
      rw [h, this]
      ring
    · field_simp
  have hcr1 : c / r ≤ 1 := by
    rcases eq_or_ne r 0 with h | h
    · rw [h, div_zero]
      norm_num
    · exact (div_le_one (lt_of_le_of_ne hr0 (Ne.symm h))).2 hcr
  have hcn1 : c / n ≤ 1 := by
    rcases eq_or_ne n 0 with h | h
    · rw [h, div_zero]
      norm_num
    · exact (div_le_one (lt_of_le_of_ne hn0 (Ne.symm h))).2 hcn
  have hcr0 : 0 ≤ c / r := div_nonneg hc0 hr0
  have hcn0 : 0 ≤ c / n := div_nonneg hc0 hn0
  constructor
  · set q : Fin m → ℝ := fun i => if i ∈ A then c / r else -(c / n) with hq
    have hA : (∑ i ∈ A, q i) = c := by
      rw [Finset.sum_congr rfl (fun i hi => if_pos hi), Finset.sum_const, nsmul_eq_mul, ← hr,
        hrc]
    have hAc : (∑ i ∈ Aᶜ, q i) = -c := by
      rw [Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_compl.mp hi)),
        Finset.sum_const, nsmul_eq_mul, ← hn, mul_neg, hnc]
    refine ⟨q, ⟨?_, fun i => ?_⟩, hA⟩
    · rw [← Finset.sum_add_sum_compl A q, hA, hAc]
      ring
    · rw [abs_le]
      simp only [hq]
      split_ifs <;> constructor <;> linarith
  · rintro v ⟨q, ⟨hqsum, hqabs⟩, rfl⟩
    have hle : ∀ B : Finset (Fin m), (∑ i ∈ B, q i) ≤ (B.card : ℝ) := by
      intro B
      have h := Finset.sum_le_sum (s := B) (fun i _ => (abs_le.mp (hqabs i)).2)
      simpa using h
    apply le_min (hle A)
    have hsplit := Finset.sum_add_sum_compl A q
    rw [hqsum] at hsplit
    have h : -(((Aᶜ).card : ℝ)) ≤ ∑ i ∈ Aᶜ, q i := by
      have h' := Finset.sum_le_sum (s := Aᶜ) (fun i _ => (abs_le.mp (hqabs i)).1)
      simpa using h'
    change (∑ i ∈ A, q i) ≤ _
    linarith

/-- `q ↦ -q` preserves `Q_m`. -/
lemma neg_mem_Qbox {q : Fin m → ℝ} (hq : q ∈ Qbox m) : -q ∈ Qbox m := by
  obtain ⟨hsum, habs⟩ := hq
  refine ⟨?_, fun i => ?_⟩
  · simp only [Pi.neg_apply, Finset.sum_neg_distrib, hsum, neg_zero]
  · simp only [Pi.neg_apply, abs_neg]
    exact habs i

/-- `h_{Q_m}(1_A) = min(r, m - r)` (paper §7.3). -/
theorem supportFun_Qbox_indicator (A : Finset (Fin m)) :
    supportFun (Qbox m) (indicatorVec A) = min (A.card : ℝ) ((Aᶜ).card : ℝ) := by
  have hfun : (fun q : Fin m → ℝ => ∑ i, indicatorVec A i * q i) =
      fun q => ∑ i ∈ A, q i := by
    funext q
    simp only [indicatorVec, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [supportFun, hfun]
  exact (isGreatest_subset_sum_Qbox A).csSup_eq

/-- `h_{Q_m}(-1_A) = min(r, m - r)` (paper §7.3). -/
theorem supportFun_Qbox_neg_indicator (A : Finset (Fin m)) :
    supportFun (Qbox m) (-indicatorVec A) = min (A.card : ℝ) ((Aᶜ).card : ℝ) := by
  have hfun : (fun q : Fin m → ℝ => ∑ i, (-indicatorVec A) i * q i) =
      fun q => ∑ i ∈ A, (-q) i := by
    funext q
    simp only [Pi.neg_apply, indicatorVec, neg_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, Finset.sum_ite_mem,
      Finset.univ_inter]
  have himg : (fun q : Fin m → ℝ => ∑ i ∈ A, (-q) i) '' Qbox m =
      (fun q : Fin m → ℝ => ∑ i ∈ A, q i) '' Qbox m := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨-q, neg_mem_Qbox hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨-q, neg_mem_Qbox hq, by simp⟩
  rw [supportFun, hfun, himg]
  exact (isGreatest_subset_sum_Qbox A).csSup_eq

end FGPT

import Carpooling.Greedy

/-!
  Permutohedral Predecessor Theorem (carpooling paper Theorem 4.4(a)):
  `P_m` is fixed by every nontrivial generator iff `0 < d ≤ 2/(m-1)`.
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- The trap state `(-(m-2)/(m-1), -(m-2)/(m-1), 2/(m-1), …, 2/(m-1))` from the
    necessity half of Theorem 4.4(a), written for `m = n + 2`. -/
noncomputable def qTrap (n : ℕ) : Fin (n + 2) → ℝ :=
  fun r => if (r : ℕ) < 2 then -((n : ℝ) / (n + 1)) else 2 / (n + 1)

/-- At most two indices of `Fin (n + 2)` have value below `2`. -/
lemma card_filter_lt_two_le (n : ℕ) (A : Finset (Fin (n + 2))) :
    (A.filter (fun i : Fin (n + 2) => (i : ℕ) < 2)).card ≤ 2 := by
  have h := Finset.card_le_card_of_injOn (fun i : Fin (n + 2) => (i : ℕ))
    (s := A.filter (fun i : Fin (n + 2) => (i : ℕ) < 2)) (t := Finset.range 2)
    (fun i hi => by
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      simpa using hi.2)
    (fun i _ j _ hij => Fin.ext hij)
  simpa using h

/-- The trap state lies in `P_m` (proof of Theorem 4.4(a)). -/
lemma qTrap_mem (n : ℕ) : qTrap n ∈ Pm (n + 2) 1 := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  refine ⟨?_, fun A => ?_⟩
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [qTrap, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one,
      show (0 : ℕ) < 2 from by norm_num, show (0 + 1 : ℕ) < 2 from by norm_num, if_true,
      show ∀ j : ℕ, ¬ (j + 1 + 1 < 2) from fun j => by omega, if_false,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · simp only
    set a := (A.filter (fun i : Fin (n + 2) => (i : ℕ) < 2)).card with ha
    set b := (A.filter (fun i : Fin (n + 2) => ¬ (i : ℕ) < 2)).card with hb
    have hab : a + b = A.card := Finset.card_filter_add_card_filter_not _
    have ha2 : a ≤ 2 := card_filter_lt_two_le n A
    have har : a ≤ A.card := by omega
    have hrm : A.card ≤ n + 2 := by
      have h := Finset.card_le_univ A
      rwa [Fintype.card_fin] at h
    have e1 : (∑ i ∈ A.filter (fun i : Fin (n + 2) => (i : ℕ) < 2), qTrap n i) =
        (a : ℝ) * (-((n : ℝ) / (n + 1))) := by
      have hc : ∀ i ∈ A.filter (fun i : Fin (n + 2) => (i : ℕ) < 2),
          qTrap n i = -((n : ℝ) / (n + 1)) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        simp only [qTrap, if_pos hi.2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    have e2 : (∑ i ∈ A.filter (fun i : Fin (n + 2) => ¬ (i : ℕ) < 2), qTrap n i) =
        (b : ℝ) * (2 / (n + 1)) := by
      have hc : ∀ i ∈ A.filter (fun i : Fin (n + 2) => ¬ (i : ℕ) < 2),
          qTrap n i = 2 / (n + 1) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        simp only [qTrap, if_neg hi.2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_filter_add_sum_filter_not A (fun i : Fin (n + 2) => (i : ℕ) < 2), e1, e2]
    unfold beta
    have hr : (A.card : ℝ) = a + b := by rw [← hab]; push_cast; ring
    rw [hr]
    push_cast
    rw [show ((n : ℝ) + 2 - 1) = n + 1 by ring]
    have key : ((n : ℝ) + 2) * a ≤ 2 * (a + b) + (a + b) * (n + 2 - (a + b)) := by
      have ha2' : (a : ℝ) ≤ 2 := by exact_mod_cast ha2
      have hrm' : (a : ℝ) + b ≤ n + 2 := by exact_mod_cast (hab ▸ hrm)
      have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      rcases Nat.lt_or_ge (a + b) 2 with hsmall | hbig
      · have hs' : (a : ℝ) + b ≤ 1 := by exact_mod_cast (show a + b ≤ 1 by omega)
        nlinarith
      · have hb' : (2 : ℝ) ≤ a + b := by exact_mod_cast hbig
        nlinarith [mul_nonneg (sub_nonneg.mpr hb') (sub_nonneg.mpr hrm')]
    have hdiff : (a : ℝ) * (-((n : ℝ) / (n + 1))) + b * (2 / (n + 1)) -
        -(1 * ((a + b) * (n + 2 - (a + b)) / (n + 1))) =
        (2 * (a + b) + (a + b) * (n + 2 - (a + b)) - (n + 2) * a) / (n + 1) := by
      field_simp
      ring
    have hnn : 0 ≤ (2 * ((a : ℝ) + b) + (a + b) * (n + 2 - (a + b)) - (n + 2) * a) / (n + 1) :=
      div_nonneg (by linarith) hn1.le
    linarith

/-- **Theorem 4.4(a) (Permutohedral Predecessor Theorem).** For `d > 0`,
    `Pre_{d,x}(P_m) = P_m` holds for every nontrivial probability vector `x`
    iff `d ≤ 2/(m-1)`. -/
theorem pred_Pm_eq_self_iff (hm : 2 ≤ m) {d : ℝ} (hd0 : 0 < d) :
    (∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 → 2 ≤ suppCard x →
      pred d x (Pm m 1) = Pm m 1) ↔ d ≤ 2 / ((m : ℝ) - 1) := by
  constructor
  · intro hall
    by_contra hlt
    push Not at hlt
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hij : (0 : Fin (n + 2)) ≠ 1 := zero_ne_one
    obtain ⟨⟨hx0, hx1, hs⟩, -⟩ := xPair_spec hij
    have h := hall _ hx0 hx1 hs
    rw [pred_eq_self_iff] at h
    obtain ⟨k, -, hk⟩ := h (qTrap n) (qTrap_mem n)
    obtain ⟨j, hj2, hkj⟩ : ∃ j : Fin (n + 2), (j : ℕ) < 2 ∧ k ≠ j := by
      by_cases hk1 : k = 1
      · exact ⟨0, by simp, by rw [hk1]; exact hij.symm⟩
      · exact ⟨1, by simp, hk1⟩
    have hxj : xPair (0 : Fin (n + 2)) 1 j = 1 / 2 := by
      have hj01 : j = 0 ∨ j = 1 := by
        rcases j with ⟨jv, hjv⟩
        interval_cases jv
        · left; rfl
        · right; rfl
      rcases hj01 with rfl | rfl <;> simp [xPair, hij, hij.symm]
    have hc := hk.2 {j}
    simp only [Finset.card_singleton, Nat.cast_one, one_mul] at hc
    rw [beta_one hm, sum_step, Finset.sum_singleton, Finset.sum_singleton,
      if_neg (by simpa using hkj), hxj] at hc
    simp only [qTrap, if_pos hj2] at hc
    push_cast at hlt
    rw [show ((n : ℝ) + 2 - 1) = n + 1 by ring] at hlt
    have hfrac : -((n : ℝ) / (n + 1)) = -1 + 1 / (n + 1) := by
      field_simp
      ring
    rw [hfrac] at hc
    have hdd : d ≤ 2 / (n + 1) := by
      have : d / 2 ≤ 1 / (n + 1) := by linarith
      calc d = 2 * (d / 2) := by ring
        _ ≤ 2 * (1 / (n + 1)) := by linarith
        _ = 2 / (n + 1) := by ring
    linarith
  · intro hle x hx0 hx1 _
    rw [pred_eq_self_iff]
    intro q hq
    obtain ⟨k, hk⟩ := exists_isGreedy d hx1 q
    exact ⟨k, hk.1, greedy_mem_Pm hm zero_le_one hd0.le (by rw [mul_one]; exact hle)
      hx0 hx1 hq hk⟩

end Carpooling

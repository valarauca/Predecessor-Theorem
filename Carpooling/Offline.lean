import Carpooling.Online

/-!
  Offline weighted carpooling (carpooling paper §6): prefix rounding
  (Corollary 6.1), the weighted carpooling conjecture for `m ≤ 3`
  (Corollary 6.2), and the zero-share padding argument behind Proposition 6.3.
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- Prefix discrepancy of agent `i` after jobs `1, …, t` under the integral
    assignment `k`: `∑_{j ≤ t} d_j (y_{ij} - x_{ij})` with `y_{ij} = [k_j = i]`
    (paper §6). -/
noncomputable def prefixDisc (d : ℕ → ℝ) (x : ℕ → Fin m → ℝ) (k : ℕ → Fin m)
    (t : ℕ) (i : Fin m) : ℝ :=
  ∑ j ∈ Finset.Icc 1 t, d j * ((if i = k j then (1 : ℝ) else 0) - x j i)

/-- The online state is the vector of prefix discrepancies. -/
lemma traj_eq_prefixDisc (d : ℕ → ℝ) (x : ℕ → Fin m → ℝ) (k : ℕ → Fin m) (t : ℕ) :
    traj d x k t = prefixDisc d x k t := by
  induction t with
  | zero =>
    funext i
    simp [traj, prefixDisc]
  | succ t ih =>
    funext i
    simp only [traj, step, ih, prefixDisc]
    rw [Finset.sum_Icc_succ_top (by omega)]

/-- Greedy assignments are support-respecting: `y_{ij} = 0` whenever `x_{ij} = 0`. -/
lemma greedyRun_supp {d : ℕ → ℝ} {x : ℕ → Fin m → ℝ} {k : ℕ → Fin m}
    (hk : IsGreedyRun d x k) (t : ℕ) : k (t + 1) ∈ supp (x (t + 1)) :=
  (hk t).1

/-- **Corollary 6.1 (offline prefix rounding), `m ≥ 3`.** Processing jobs
    `1, …, n` with the greedy rule, every prefix `t ≤ n` and proper nonempty
    agent set `A` satisfy `|∑_{i ∈ A} ∑_{j ≤ t} d_j (y_{ij} - x_{ij})| <
    |A| (m - |A|)/2 · D` with `D = max_{j ≤ n} d_j > 0`. -/
theorem offline_subset_disc_lt (hm : 3 ≤ m) {n : ℕ} {d : ℕ → ℝ} {x : ℕ → Fin m → ℝ}
    {k : ℕ → Fin m} (hd : ∀ t, 0 ≤ d (t + 1)) (hD : 0 < Dmax d n)
    (hx0 : ∀ t i, 0 ≤ x t i) (hx1 : ∀ t, (∑ i, x t i) = 1) (hk : IsGreedyRun d x k)
    {t : ℕ} (htn : t ≤ n) {A : Finset (Fin m)} (h1 : 1 ≤ A.card) (h2 : A.card ≤ m - 1) :
    |∑ i ∈ A, prefixDisc d x k t i| <
      (A.card : ℝ) * ((m : ℝ) - A.card) / 2 * Dmax d n := by
  rw [← traj_eq_prefixDisc]
  have hr : 0 < (A.card : ℝ) * ((m : ℝ) - A.card) / 2 := by
    have ha : (1 : ℝ) ≤ A.card := by exact_mod_cast h1
    have hb : (A.card : ℝ) < m := by exact_mod_cast (show A.card < m by omega)
    have : 0 < (A.card : ℝ) * ((m : ℝ) - A.card) := mul_pos (by linarith) (by linarith)
    linarith
  rcases traj_relint hm hd hx0 hx1 hk t with ⟨-, hq0⟩ | ⟨-, hqr⟩
  · rw [hq0]
    simp only [Pi.zero_apply, Finset.sum_const_zero, abs_zero]
    exact mul_pos hr hD
  · have h := abs_sum_lt_of_mem_relintPm hqr h1 h2
    rw [scale_beta (by omega)] at h
    exact lt_of_lt_of_le h (mul_le_mul_of_nonneg_left (Dmax_mono d htn) hr.le)

/-- **Corollary 6.1, sup norm, `m ≥ 3`.** `disc(y) < (m-1)/2 · D`. -/
theorem offline_disc_lt (hm : 3 ≤ m) {n : ℕ} {d : ℕ → ℝ} {x : ℕ → Fin m → ℝ}
    {k : ℕ → Fin m} (hd : ∀ t, 0 ≤ d (t + 1)) (hD : 0 < Dmax d n)
    (hx0 : ∀ t i, 0 ≤ x t i) (hx1 : ∀ t, (∑ i, x t i) = 1) (hk : IsGreedyRun d x k)
    {t : ℕ} (htn : t ≤ n) (i : Fin m) :
    |prefixDisc d x k t i| < ((m : ℝ) - 1) / 2 * Dmax d n := by
  have h := offline_subset_disc_lt hm hd hD hx0 hx1 hk htn (A := {i}) (by simp)
    (by simp; omega)
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at h
  exact h

/-- **Corollary 6.1, `m = 2`.** `disc(y) ≤ D/2`. -/
theorem offline_disc_le_two {n : ℕ} {d : ℕ → ℝ} {x : ℕ → Fin 2 → ℝ} {k : ℕ → Fin 2}
    (hd : ∀ t, 0 ≤ d (t + 1)) (hx0 : ∀ t i, 0 ≤ x t i) (hx1 : ∀ t, (∑ i, x t i) = 1)
    (hk : IsGreedyRun d x k) {t : ℕ} (htn : t ≤ n) (i : Fin 2) :
    |prefixDisc d x k t i| ≤ Dmax d n / 2 := by
  rw [← traj_eq_prefixDisc]
  have h := online_abs_le_two hd hx0 hx1 hk t i
  linarith [Dmax_mono d htn]

/-- **Corollary 6.2 (weighted carpooling conjecture for `m = 2`).**
    `disc(y) ≤ max_j d_j`. -/
theorem carpooling_conjecture_two {n : ℕ} {d : ℕ → ℝ} {x : ℕ → Fin 2 → ℝ}
    {k : ℕ → Fin 2} (hd : ∀ t, 0 ≤ d (t + 1)) (hx0 : ∀ t i, 0 ≤ x t i)
    (hx1 : ∀ t, (∑ i, x t i) = 1) (hk : IsGreedyRun d x k) {t : ℕ} (htn : t ≤ n)
    (i : Fin 2) : |prefixDisc d x k t i| ≤ Dmax d n := by
  have h := offline_disc_le_two hd hx0 hx1 hk htn i
  linarith [Dmax_nonneg d n]

/-- **Corollary 6.2 (weighted carpooling conjecture for `m = 3`).**
    `disc(y) < max_j d_j`. -/
theorem carpooling_conjecture_three {n : ℕ} {d : ℕ → ℝ} {x : ℕ → Fin 3 → ℝ}
    {k : ℕ → Fin 3} (hd : ∀ t, 0 ≤ d (t + 1)) (hD : 0 < Dmax d n)
    (hx0 : ∀ t i, 0 ≤ x t i) (hx1 : ∀ t, (∑ i, x t i) = 1) (hk : IsGreedyRun d x k)
    {t : ℕ} (htn : t ≤ n) (i : Fin 3) : |prefixDisc d x k t i| < Dmax d n := by
  have h := offline_disc_lt le_rfl hd hD hx0 hx1 hk htn i
  norm_num at h
  exact h

/-- **Corollary 6.2, tightness for `m = 2`.** A single job split `(½, ½)` forces
    discrepancy exactly `d₁/2` for every agent, whichever agent receives it. -/
theorem two_tight (d₁ : ℝ) (k : Fin 2) (i : Fin 2) (hd : 0 ≤ d₁) :
    |step d₁ ![1 / 2, 1 / 2] k 0 i| = d₁ / 2 := by
  fin_cases k <;> fin_cases i <;> simp [step, abs_of_nonneg, hd] <;>
    norm_num [abs_of_nonneg, hd] <;> ring

/-- Zero-share padding of a share vector along an embedding `e : Fin m ↪ Fin m'`:
    agents outside the image of `e` get share `0` (proof of Proposition 6.3). -/
noncomputable def padShare {m' : ℕ} (e : Fin m ↪ Fin m') (x : Fin m → ℝ) : Fin m' → ℝ :=
  Function.extend e x 0

/-- Padding keeps the original shares. -/
lemma padShare_apply {m' : ℕ} (e : Fin m ↪ Fin m') (x : Fin m → ℝ) (i : Fin m) :
    padShare e x (e i) = x i :=
  e.injective.extend_apply _ _ _

/-- Padded agents have share `0`. -/
lemma padShare_of_not_mem {m' : ℕ} (e : Fin m ↪ Fin m') (x : Fin m → ℝ) {i' : Fin m'}
    (h : ∀ i, e i ≠ i') : padShare e x i' = 0 := by
  unfold padShare
  rw [Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => h i hi)]
  rfl

/-- Padding preserves nonnegativity. -/
lemma padShare_nonneg {m' : ℕ} (e : Fin m ↪ Fin m') {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (i' : Fin m') : 0 ≤ padShare e x i' := by
  by_cases h : ∃ i, e i = i'
  · obtain ⟨i, rfl⟩ := h
    rw [padShare_apply]
    exact hx0 i
  · push Not at h
    rw [padShare_of_not_mem e x h]

/-- Padding preserves the total share. -/
lemma padShare_sum {m' : ℕ} (e : Fin m ↪ Fin m') (x : Fin m → ℝ) :
    (∑ i', padShare e x i') = ∑ i, x i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun i' _ hi' => by
    apply padShare_of_not_mem
    intro i hi
    exact hi' (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩)), Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => padShare_apply e x i

/-- A supported padded agent comes from a supported original agent. -/
lemma exists_of_mem_supp_padShare {m' : ℕ} (e : Fin m ↪ Fin m') {x : Fin m → ℝ}
    {i' : Fin m'} (h : i' ∈ supp (padShare e x)) : ∃ i, e i = i' ∧ i ∈ supp x := by
  by_contra hne
  have hz : padShare e x i' = 0 := by
    by_cases hr : ∃ i, e i = i'
    · obtain ⟨i, hi⟩ := hr
      have hxi : x i = 0 := by
        by_contra hxi
        exact hne ⟨i, hi, by simp [supp, hxi]⟩
      rw [← hi, padShare_apply, hxi]
    · push Not at hr
      exact padShare_of_not_mem e x hr
  simp [supp, hz] at h

/-- **Padding argument of Proposition 6.3.** Appending zero-share agents does
    not change the admissible integral assignments or their discrepancies: every
    support-respecting assignment `k'` of the padded instance factors as `e ∘ k`
    through a support-respecting assignment `k` of the original instance, the
    original agents keep their prefix discrepancies, and padded agents have
    prefix discrepancy `0`. -/
theorem padded_prefixDisc {m' : ℕ} (hm : 0 < m) (e : Fin m ↪ Fin m') (d : ℕ → ℝ)
    (x : ℕ → Fin m → ℝ) (k' : ℕ → Fin m')
    (hk' : ∀ t, k' (t + 1) ∈ supp (padShare e (x (t + 1)))) :
    ∃ k : ℕ → Fin m, (∀ t, k (t + 1) ∈ supp (x (t + 1)) ∧ e (k (t + 1)) = k' (t + 1)) ∧
      (∀ t i, prefixDisc d (fun j => padShare e (x j)) k' t (e i) = prefixDisc d x k t i) ∧
      (∀ t i', (∀ i, e i ≠ i') → prefixDisc d (fun j => padShare e (x j)) k' t i' = 0) := by
  classical
  have hex : ∀ t, ∃ i, e i = k' (t + 1) ∧ i ∈ supp (x (t + 1)) :=
    fun t => exists_of_mem_supp_padShare e (hk' t)
  choose g hg using hex
  let k : ℕ → Fin m := fun t => match t with
    | 0 => ⟨0, hm⟩
    | s + 1 => g s
  have hk : ∀ j, 1 ≤ j → k' j = e (k j) := by
    intro j hj
    obtain ⟨s, rfl⟩ : ∃ s, j = s + 1 := ⟨j - 1, by omega⟩
    exact (hg s).1.symm
  refine ⟨k, fun t => ⟨(hg t).2, (hg t).1⟩, fun t i => ?_, fun t i' hi' => ?_⟩
  · unfold prefixDisc
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [hk j hj.1]
    beta_reduce
    rw [padShare_apply]
    simp only [e.injective.eq_iff]
  · unfold prefixDisc
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [hk j hj.1]
    beta_reduce
    rw [padShare_of_not_mem e _ hi', if_neg (fun h => hi' _ h.symm)]
    ring

end Carpooling

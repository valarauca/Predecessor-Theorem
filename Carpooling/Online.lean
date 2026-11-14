import Carpooling.Greedy

/-!
  Scale-free weighted online carpooling (carpooling paper Theorem 5.1(a)).
  Demands are allowed to be zero here so that the offline corollary needs no
  job deletion.
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- Online imbalance trajectory from `q^0 = 0`: round `t + 1` assigns demand
    `d (t + 1)` with share vector `x (t + 1)` to agent `k (t + 1)` (paper §1). -/
noncomputable def traj (d : ℕ → ℝ) (x : ℕ → Fin m → ℝ) (k : ℕ → Fin m) :
    ℕ → Fin m → ℝ
  | 0 => 0
  | t + 1 => step (d (t + 1)) (x (t + 1)) (k (t + 1)) (traj d x k t)

/-- Running peak demand `D_t = max_{1 ≤ j ≤ t} d_j`, with `D_0 = 0`
    (paper Theorem 5.1). -/
noncomputable def Dmax (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => max (Dmax d t) (d (t + 1))

/-- The controller follows the post-drift greedy rule in every round
    (paper Theorem 5.1(a)). -/
def IsGreedyRun (d : ℕ → ℝ) (x : ℕ → Fin m → ℝ) (k : ℕ → Fin m) : Prop :=
  ∀ t, IsGreedy (d (t + 1)) (x (t + 1)) (traj d x k t) (k (t + 1))

/-- The greedy rule can always be followed. -/
lemma exists_greedyRun (d : ℕ → ℝ) (x : ℕ → Fin m → ℝ) (hx1 : ∀ t, (∑ i, x t i) = 1) :
    ∃ k : ℕ → Fin m, IsGreedyRun d x k := by
  classical
  have hex : ∀ t (q : Fin m → ℝ), ∃ j, IsGreedy (d (t + 1)) (x (t + 1)) q j :=
    fun t q => exists_isGreedy _ (hx1 (t + 1)) q
  choose g hg using hex
  let qs : ℕ → Fin m → ℝ := fun t =>
    Nat.rec (motive := fun _ => Fin m → ℝ) 0
      (fun s q => step (d (s + 1)) (x (s + 1)) (g s q) q) t
  let k : ℕ → Fin m := fun t => match t with
    | 0 => g 0 0
    | s + 1 => g s (qs s)
  have hq : ∀ t, traj d x k t = qs t := by
    intro t
    induction t with
    | zero => rfl
    | succ s ih => simp only [traj, ih]; rfl
  refine ⟨k, fun t => ?_⟩
  rw [hq]
  exact hg t (qs t)

/-- A zero demand leaves the state unchanged. -/
lemma step_zero_demand (x : Fin m → ℝ) (k : Fin m) (q : Fin m → ℝ) : step 0 x k q = q := by
  funext i
  simp [step]

/-- `D_t ≥ 0`. -/
lemma Dmax_nonneg (d : ℕ → ℝ) (t : ℕ) : 0 ≤ Dmax d t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact le_trans ih (le_max_left _ _)

/-- `D_t` is nondecreasing. -/
lemma Dmax_mono (d : ℕ → ℝ) : Monotone (Dmax d) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

/-- `d_j ≤ D_t` for `1 ≤ j ≤ t`. -/
lemma le_Dmax (d : ℕ → ℝ) {j t : ℕ} (hj : 1 ≤ j) (hjt : j ≤ t) : d j ≤ Dmax d t := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact le_trans (le_max_right _ _) (Dmax_mono d hjt)

/-- With positive demands, `D_t > 0` for `t ≥ 1`. -/
lemma Dmax_pos {d : ℕ → ℝ} (hd : ∀ t, 0 < d (t + 1)) {t : ℕ} (ht : 1 ≤ t) :
    0 < Dmax d t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  exact lt_of_lt_of_le (hd s) (le_max_right _ _)

/-- `2/(m-1) · ((m-1)/2 · D) = D`. -/
lemma scale_cancel (hm : 2 ≤ m) (D : ℝ) :
    2 / ((m : ℝ) - 1) * (((m : ℝ) - 1) / 2 * D) = D := by
  have := (cast_sub_one_pos hm).ne'
  field_simp

/-- `(m-1)/2 · D ≥ 0` for `D ≥ 0`. -/
lemma scale_nonneg (hm : 2 ≤ m) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ ((m : ℝ) - 1) / 2 * D :=
  mul_nonneg (div_nonneg (cast_sub_one_pos hm).le zero_le_two) hD

/-- **Theorem 5.1(a), polytope form.** Under the greedy rule with demands
    `d_t ≥ 0`, every state satisfies `q^t ∈ P_m((m-1)/2 · D_t)`. -/
theorem traj_mem_Pm (hm : 2 ≤ m) {d : ℕ → ℝ} {x : ℕ → Fin m → ℝ} {k : ℕ → Fin m}
    (hd : ∀ t, 0 ≤ d (t + 1)) (hx0 : ∀ t i, 0 ≤ x t i) (hx1 : ∀ t, (∑ i, x t i) = 1)
    (hk : IsGreedyRun d x k) (t : ℕ) :
    traj d x k t ∈ Pm m (((m : ℝ) - 1) / 2 * Dmax d t) := by
  induction t with
  | zero => exact zero_mem_Pm hm (by simp [Dmax])
  | succ t ih =>
    have hmono : ((m : ℝ) - 1) / 2 * Dmax d t ≤ ((m : ℝ) - 1) / 2 * Dmax d (t + 1) :=
      mul_le_mul_of_nonneg_left (Dmax_mono d (Nat.le_succ t))
        (div_nonneg (cast_sub_one_pos hm).le zero_le_two)
    have hdB : d (t + 1) ≤ 2 / ((m : ℝ) - 1) * (((m : ℝ) - 1) / 2 * Dmax d (t + 1)) := by
      rw [scale_cancel hm]
      exact le_max_right _ _
    exact greedy_mem_Pm hm (scale_nonneg hm (Dmax_nonneg d _)) (hd t) hdB (hx0 _) (hx1 _)
      (Pm_mono hm hmono ih) (hk t)

/-- **Theorem 5.1(a), strict form for `m ≥ 3`.** Either nothing has been
    demanded yet and `q^t = 0`, or `D_t > 0` and `q^t ∈ relint P_m((m-1)/2 · D_t)`. -/
theorem traj_relint (hm : 3 ≤ m) {d : ℕ → ℝ} {x : ℕ → Fin m → ℝ} {k : ℕ → Fin m}
    (hd : ∀ t, 0 ≤ d (t + 1)) (hx0 : ∀ t i, 0 ≤ x t i) (hx1 : ∀ t, (∑ i, x t i) = 1)
    (hk : IsGreedyRun d x k) (t : ℕ) :
    (Dmax d t = 0 ∧ traj d x k t = 0) ∨
      (0 < Dmax d t ∧ traj d x k t ∈ relintPm m (((m : ℝ) - 1) / 2 * Dmax d t)) := by
  have hm2 : 2 ≤ m := by omega
  have hc : 0 < ((m : ℝ) - 1) / 2 := div_pos (cast_sub_one_pos hm2) two_pos
  induction t with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ t ih =>
    have hdB : d (t + 1) ≤ 2 / ((m : ℝ) - 1) * (((m : ℝ) - 1) / 2 * Dmax d (t + 1)) := by
      rw [scale_cancel hm2]
      exact le_max_right _ _
    rcases ih with ⟨hD0, hq0⟩ | ⟨hDpos, hqr⟩
    · rcases (hd t).eq_or_lt with hdt | hdt
      · left
        refine ⟨?_, ?_⟩
        · show max (Dmax d t) (d (t + 1)) = 0
          rw [hD0, ← hdt, max_self]
        · show step (d (t + 1)) (x (t + 1)) (k (t + 1)) (traj d x k t) = 0
          rw [hq0, ← hdt, step_zero_demand]
      · have hDp : 0 < Dmax d (t + 1) := lt_of_lt_of_le hdt (le_max_right _ _)
        right
        refine ⟨hDp, ?_⟩
        change step (d (t + 1)) (x (t + 1)) (k (t + 1)) (traj d x k t) ∈ _
        have hkt := hk t
        rw [hq0] at hkt ⊢
        exact greedy_mem_relintPm hm (mul_pos hc hDp) (hd t) hdB (hx0 _) (hx1 _)
          (zero_mem_relintPm hm2 (mul_pos hc hDp)) hkt
    · have hDp : 0 < Dmax d (t + 1) := lt_of_lt_of_le hDpos (Dmax_mono d (Nat.le_succ t))
      right
      refine ⟨hDp, ?_⟩
      have hmono : ((m : ℝ) - 1) / 2 * Dmax d t ≤ ((m : ℝ) - 1) / 2 * Dmax d (t + 1) :=
        mul_le_mul_of_nonneg_left (Dmax_mono d (Nat.le_succ t)) hc.le
      exact greedy_mem_relintPm hm (mul_pos hc hDp) (hd t) hdB (hx0 _) (hx1 _)
        (relintPm_mono hm2 hmono hqr) (hk t)

/-- `(m-1)/2 · D · β_r = r (m - r)/2 · D`. -/
lemma scale_beta (hm : 2 ≤ m) (D r : ℝ) :
    ((m : ℝ) - 1) / 2 * D * beta m r = r * ((m : ℝ) - r) / 2 * D := by
  have := (cast_sub_one_pos hm).ne'
  unfold beta
  field_simp

/-- **Theorem 5.1(a), `m = 2`.** `|q^t_i| ≤ D_t / 2`. -/
theorem online_abs_le_two {d : ℕ → ℝ} {x : ℕ → Fin 2 → ℝ} {k : ℕ → Fin 2}
    (hd : ∀ t, 0 ≤ d (t + 1)) (hx0 : ∀ t i, 0 ≤ x t i) (hx1 : ∀ t, (∑ i, x t i) = 1)
    (hk : IsGreedyRun d x k) (t : ℕ) (i : Fin 2) :
    |traj d x k t i| ≤ Dmax d t / 2 := by
  have h := abs_le_of_mem_Pm le_rfl (traj_mem_Pm le_rfl hd hx0 hx1 hk t) i
  norm_num at h
  linarith

/-- **Theorem 5.1(a), subset sums for `m ≥ 3`.** With positive demands, for
    every `t ≥ 1` and proper nonempty `A`, `|q^t(A)| < |A| (m - |A|)/2 · D_t`. -/
theorem online_subset_sum_lt (hm : 3 ≤ m) {d : ℕ → ℝ} {x : ℕ → Fin m → ℝ}
    {k : ℕ → Fin m} (hd : ∀ t, 0 < d (t + 1)) (hx0 : ∀ t i, 0 ≤ x t i)
    (hx1 : ∀ t, (∑ i, x t i) = 1) (hk : IsGreedyRun d x k) {t : ℕ} (ht : 1 ≤ t)
    {A : Finset (Fin m)} (h1 : 1 ≤ A.card) (h2 : A.card ≤ m - 1) :
    |∑ i ∈ A, traj d x k t i| < (A.card : ℝ) * ((m : ℝ) - A.card) / 2 * Dmax d t := by
  rcases traj_relint hm (fun s => (hd s).le) hx0 hx1 hk t with ⟨hD0, -⟩ | ⟨-, hqr⟩
  · exact absurd hD0 (Dmax_pos hd ht).ne'
  · have h := abs_sum_lt_of_mem_relintPm hqr h1 h2
    rwa [scale_beta (by omega)] at h

/-- **Theorem 5.1(a), sup norm for `m ≥ 3`.** With positive demands,
    `|q^t_i| < (m-1)/2 · D_t` for every `t ≥ 1`. -/
theorem online_abs_lt (hm : 3 ≤ m) {d : ℕ → ℝ} {x : ℕ → Fin m → ℝ}
    {k : ℕ → Fin m} (hd : ∀ t, 0 < d (t + 1)) (hx0 : ∀ t i, 0 ≤ x t i)
    (hx1 : ∀ t, (∑ i, x t i) = 1) (hk : IsGreedyRun d x k) {t : ℕ} (ht : 1 ≤ t)
    (i : Fin m) : |traj d x k t i| < ((m : ℝ) - 1) / 2 * Dmax d t := by
  rcases traj_relint hm (fun s => (hd s).le) hx0 hx1 hk t with ⟨hD0, -⟩ | ⟨-, hqr⟩
  · exact absurd hD0 (Dmax_pos hd ht).ne'
  · exact abs_lt_of_mem_relintPm (by omega) hqr i

end Carpooling

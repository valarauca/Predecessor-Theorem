import FGPT.Scaling

/-!
  Uniform invariance radius (FGPT paper Corollaries 4.2 and 4.3, §8.1).
-/

open Finset

namespace FGPT

variable {m : ℕ}

/-- A nontrivial probability vector: nonnegative, summing to one, with
    support size at least two (paper Definition 3.1). -/
def IsNontrivialProb (x : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧ 2 ≤ suppCard x

/-- Demands `d ∈ (0, 2]` at which every nontrivial generator fixes `Q_m`
    (paper Corollary 4.2). -/
def safeDemands (m : ℕ) : Set ℝ :=
  { d | d ∈ Set.Ioc 0 2 ∧ ∀ x : Fin m → ℝ, IsNontrivialProb x →
      ∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m }

/-- The uniform invariance radius `ρ(m)`, with `sSup ∅ = 0` (paper Corollary 4.2). -/
noncomputable def rho (m : ℕ) : ℝ := sSup (safeDemands m)

/-- The equal split between two distinct coordinates `i ≠ j`. -/
noncomputable def xPair (i j : Fin m) : Fin m → ℝ :=
  fun r => (if r = i then (1 / 2 : ℝ) else 0) + (if r = j then (1 / 2 : ℝ) else 0)

/-- `xPair i j` is a nontrivial probability vector with `σ₂ = 1`. -/
lemma xPair_spec {i j : Fin m} (hij : i ≠ j) :
    IsNontrivialProb (xPair i j) ∧ sigma2 (xPair i j) = 1 := by
  have hx0 : ∀ r, 0 ≤ xPair i j r := by
    intro r
    simp only [xPair]
    split_ifs <;> norm_num
  have hx1 : (∑ r, xPair i j r) = 1 := by
    simp only [xPair]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [mem_univ, if_true]
    norm_num
  have hxi : xPair i j i = 1 / 2 := by simp [xPair, hij]
  have hxj : xPair i j j = 1 / 2 := by simp [xPair, hij.symm]
  have hs : 2 ≤ suppCard (xPair i j) := by
    have hi : i ∈ supp (xPair i j) := by
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, hxi]
      norm_num
    have hj : j ∈ supp (xPair i j) := by
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, hxj]
      norm_num
    exact Finset.one_lt_card.mpr ⟨i, hi, j, hj, hij⟩
  refine ⟨⟨hx0, hx1, hs⟩, le_antisymm (sigma2_le_one hx0 hx1) ?_⟩
  have h := add_le_sigma2 (xPair i j) hij
  rw [hxi, hxj] at h
  linarith

/-- The support size of `x : Fin m → ℝ` is at most `m`. -/
lemma suppCard_le (x : Fin m → ℝ) : suppCard x ≤ m := by
  have h := Finset.card_le_univ (supp x)
  rwa [Fintype.card_fin] at h

/-- For `m = 2` every `d ∈ (0, 2]` is safe (paper Corollary 4.2). -/
lemma safeDemands_two : safeDemands 2 = Set.Ioc 0 2 := by
  ext d
  constructor
  · exact fun h => h.1
  · intro hd
    refine ⟨hd, fun x ⟨hx0, hx1, hs⟩ => ?_⟩
    rw [fgpt hd.1 hd.2 le_rfl hx0 hx1 hs]
    have hs2 : suppCard x = 2 := le_antisymm (suppCard_le x) hs
    have hσ := sigma2_le_one hx0 hx1
    rw [hs2]
    push_cast
    constructor <;> nlinarith [hd.1, hd.2]

/-- For `m = 3` the safe demands are exactly `(0, 1]` (paper Corollary 4.2). -/
lemma safeDemands_three : safeDemands 3 = Set.Ioc 0 1 := by
  ext d
  constructor
  · rintro ⟨hd, hall⟩
    refine ⟨hd.1, ?_⟩
    have hij : (0 : Fin 3) ≠ 1 := by decide
    obtain ⟨⟨hx0, hx1, hs⟩, hσ⟩ := xPair_spec hij
    have h := hall _ ⟨hx0, hx1, hs⟩
    rw [fgpt hd.1 hd.2 (by norm_num) hx0 hx1 hs, hσ] at h
    have h1 := h.1
    push_cast at h1
    linarith
  · intro hd
    refine ⟨⟨hd.1, by linarith [hd.2]⟩, fun x ⟨hx0, hx1, hs⟩ => ?_⟩
    rw [fgpt hd.1 (by linarith [hd.2]) (by norm_num) hx0 hx1 hs]
    have hσ := sigma2_le_one hx0 hx1
    have hσ0 := sigma2_pos x hx0 hs
    have hsR : (2 : ℝ) ≤ (suppCard x : ℝ) := by exact_mod_cast hs
    push_cast
    constructor <;> nlinarith [hd.1, hd.2]

/-- For `m ≥ 4` no demand is safe (paper Corollary 4.2). -/
lemma safeDemands_of_four_le (hm : 4 ≤ m) : safeDemands m = ∅ := by
  ext d
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hd, hall⟩
  have hij : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  obtain ⟨⟨hx0, hx1, hs⟩, -⟩ := xPair_spec hij
  exact no_invariance_of_four_le hd.1 hd.2 hm hx0 hx1 hs (hall _ ⟨hx0, hx1, hs⟩)

/-- **Uniform invariance radius**, `m = 2` (paper Corollary 4.2). -/
theorem rho_two : rho 2 = 2 := by
  rw [rho, safeDemands_two, csSup_Ioc (by norm_num)]

/-- **Uniform invariance radius**, `m = 3` (paper Corollary 4.2). -/
theorem rho_three : rho 3 = 1 := by
  rw [rho, safeDemands_three, csSup_Ioc (by norm_num)]

/-- The radius `ρ(3) = 1` is attained: equality is safe (paper Corollary 4.2). -/
theorem rho_three_mem : rho 3 ∈ safeDemands 3 := by
  rw [rho_three, safeDemands_three]
  norm_num

/-- **Uniform invariance radius**, `m ≥ 4` (paper Corollary 4.2). -/
theorem rho_of_four_le (hm : 4 ≤ m) : rho m = 0 := by
  rw [rho, safeDemands_of_four_le hm, Real.sSup_empty]

/-- **Rank-four obstruction** (paper Corollary 4.3): for `m ≥ 4` every
    nontrivial generator with `0 < d ≤ 2` has a double-floor trap in `Q_m`. -/
theorem double_floor_trap_of_four_le {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2)
    {x : Fin m → ℝ} (hm : 4 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    ∃ q ∈ Qbox m, (∃ i j, i ≠ j ∧ q i - d * x i < -1 ∧ q j - d * x j < -1) ∧
      ¬ ∃ k ∈ supp x, step d x k q ∈ Qbox m := by
  have hm2 : 2 ≤ m := by omega
  have hlt : (4 : ℝ) - (m : ℝ) < d * sigma2 x := by
    have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hpos := mul_pos hd0 (sigma2_pos x hx0 hs)
    linarith
  obtain ⟨q, hq, hD⟩ := (modeD_iff hd0 hd2 hm2 hx0 hx1 hs).2 hlt
  exact ⟨q, hq, hD, (trap_iff hq hd0 hd2 hx0 hx1 hs).2 (Or.inl hD)⟩

/-- **Memoryless three-machine balancing** (paper §8.1): for `d ∈ (0, 1]`
    and every nontrivial `x`, a state-feedback policy keeps `Q_3` invariant. -/
theorem memoryless_three {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    {x : Fin 3 → ℝ} (hx : IsNontrivialProb x) :
    ∃ policy : (Fin 3 → ℝ) → Fin 3, ∀ q ∈ Qbox 3,
      policy q ∈ supp x ∧ step d x (policy q) q ∈ Qbox 3 := by
  have hsafe : d ∈ safeDemands 3 := by
    rw [safeDemands_three]
    exact ⟨hd0, hd1⟩
  have h := hsafe.2 x hx
  classical
  refine ⟨fun q => if hq : q ∈ Qbox 3 then (h q hq).choose else 0, ?_⟩
  intro q hq
  simp only [dif_pos hq]
  exact (h q hq).choose_spec

/-- Memoryless three-machine balancing on the radius-`B` box: a demand
    `d ≤ B` is safe (paper §8.1 with Remark 3.3). -/
theorem memoryless_three_scaled {B d : ℝ} (hB : 0 < B) (hd0 : 0 < d) (hdB : d ≤ B)
    {x : Fin 3 → ℝ} (hx : IsNontrivialProb x) :
    ∀ q ∈ QboxR 3 B, ∃ k ∈ supp x, step d x k q ∈ QboxR 3 B := by
  rw [invariant_QboxR_iff hB]
  have hsafe : d / B ∈ safeDemands 3 := by
    rw [safeDemands_three]
    exact ⟨div_pos hd0 hB, (div_le_one hB).2 hdB⟩
  exact hsafe.2 x hx

end FGPT

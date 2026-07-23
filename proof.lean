/-
  Fixed-Generator Predecessor Theorem — Lean 4 / mathlib formalization skeleton.
 
  Maps to the paper's Section 4 (the trap classification), which is the only
  part needed for Theorem 3.1. Farkas / support-function sections are optional.
 
  STATUS: complete. Every lemma and theorem is proved (no `sorry`), checked
  against mathlib v4.32.0.
 
  Setup:  lake new fgpt math   →  lake exe cache get   →  drop this file in.
-/
import Mathlib
 
open Finset
 
namespace FGPT
 
variable {m : ℕ}
 
/-! ## Definitions (paper §2) -/
 
/-- The zero-sum cube section `Q_m`. -/
def Qbox (m : ℕ) : Set (Fin m → ℝ) :=
  { q | (∑ i, q i) = 0 ∧ ∀ i, |q i| ≤ 1 }
 
/-- One supported-balancing step `T_k(q) = q + d (e_k - x)`. -/
def step (d : ℝ) (x : Fin m → ℝ) (k : Fin m) (q : Fin m → ℝ) : Fin m → ℝ :=
  fun i => q i + d * ((if i = k then (1 : ℝ) else 0) - x i)
 
open Classical in
/-- Support of `x` as a `Finset`. -/
noncomputable def supp (x : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => x i ≠ 0
 
/-- `s = |supp x|`. -/
noncomputable def suppCard (x : Fin m → ℝ) : ℕ := (supp x).card
 
/-- `σ₂ x` as the max of `x i + x j` over ordered pairs `i ≠ j`.
    For `m ≥ 2` this equals the sum of the two largest coordinates,
    but the pair form is what every proof step actually uses. -/
noncomputable def sigma2 (x : Fin m → ℝ) : ℝ :=
  if h : ((univ : Finset (Fin m)).offDiag).Nonempty then
    (univ : Finset (Fin m)).offDiag.sup' h (fun p => x p.1 + x p.2)
  else 0
 
/-! ## Basic facts about `σ₂` and `supp` -/
 
/-- Every pair is dominated by `σ₂`.  (Unfold `sigma2`; `Finset.le_sup'`.) -/
lemma add_le_sigma2 (x : Fin m → ℝ) {i j : Fin m} (hij : i ≠ j) :
    x i + x j ≤ sigma2 x := by
  have hp : (i, j) ∈ (univ : Finset (Fin m)).offDiag := by
    rw [Finset.mem_offDiag]
    exact ⟨mem_univ i, mem_univ j, hij⟩
  have hne : ((univ : Finset (Fin m)).offDiag).Nonempty := ⟨(i, j), hp⟩
  unfold sigma2
  rw [dif_pos hne]
  exact Finset.le_sup' (fun p => x p.1 + x p.2) hp
 
/-- Some pair attains `σ₂`, and with `s ≥ 2` both members can be taken
    strictly positive (needed for Mode D's `ε < d·xᵢ`).
    Take `i` maximizing `x`, then `j` maximizing over `univ \ {i}`;
    positivity of both follows from the existence of two positive coords. -/
lemma exists_sigma2_pair_pos (x : Fin m → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hs : 2 ≤ suppCard x) :
    ∃ i j, i ≠ j ∧ 0 < x i ∧ 0 < x j ∧ sigma2 x = x i + x j := by
  have h1 : 1 < (supp x).card := hs
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hxa : 0 < x a := (hx0 a).lt_of_ne (Ne.symm ha)
  have hxb : 0 < x b := (hx0 b).lt_of_ne (Ne.symm hb)
  have hne : ((univ : Finset (Fin m)).offDiag).Nonempty := by
    refine ⟨(a, b), ?_⟩
    rw [Finset.mem_offDiag]; exact ⟨mem_univ a, mem_univ b, hab⟩
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup' hne (fun p => x p.1 + x p.2)
  rw [Finset.mem_offDiag] at hp
  obtain ⟨-, -, hpij⟩ := hp
  have hsig : sigma2 x = x p.1 + x p.2 := by
    unfold sigma2; rw [dif_pos hne]; exact hpe
  have hpos_ne : ∀ t : Fin m, ∃ c, c ≠ t ∧ 0 < x c := by
    intro t
    rcases eq_or_ne a t with rfl | hat
    · exact ⟨b, hab.symm, hxb⟩
    · exact ⟨a, hat, hxa⟩
  refine ⟨p.1, p.2, hpij, ?_, ?_, hsig⟩
  · obtain ⟨c, hc, hxc⟩ := hpos_ne p.2
    have hle := add_le_sigma2 x hc
    rw [hsig] at hle; linarith
  · obtain ⟨c, hc, hxc⟩ := hpos_ne p.1
    have hle := add_le_sigma2 x (Ne.symm hc)
    rw [hsig] at hle; linarith
 
/-- `σ₂ x > 0` when `s ≥ 2` — needed for the ratio-form corollary and the
    `m ≥ 4` obstruction. -/
lemma sigma2_pos (x : Fin m → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hs : 2 ≤ suppCard x) :
    0 < sigma2 x := by
  have h1 : 1 < (supp x).card := hs
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h1
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hxi : 0 < x i := (hx0 i).lt_of_ne (Ne.symm hi)
  have hxj : 0 < x j := (hx0 j).lt_of_ne (Ne.symm hj)
  have hle := add_le_sigma2 x hij
  linarith
 
/-! ## Safe-choice criterion (paper Lemma 4.1)
 
The recentered state is `y i = q i - d * x i`; we inline it below rather than
naming it, so `linarith` sees the raw atoms. -/
 
/-- For `q ∈ Q_m`, choosing `k` is safe iff no coordinate other than `k` is
    lower-dangerous and `k` is not upper-blocked.
    Forward: evaluate `step` coordinatewise, split on `i = k`.
    Backward: the "automatic" sides use `0 ≤ x i`, `x k ≤ 1` (from `hx1`),
    and `0 < d`; then `linarith`. -/
lemma step_mem_iff {q : Fin m → ℝ} (hq : q ∈ Qbox m)
    {d : ℝ} (hd0 : 0 < d) {x : Fin m → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1) (k : Fin m) :
    step d x k q ∈ Qbox m ↔
      (∀ i, i ≠ k → -1 ≤ q i - d * x i) ∧ q k - d * x k ≤ 1 - d := by
  simp only [Qbox, Set.mem_setOf_eq] at hq ⊢
  obtain ⟨hqsum, hqabs⟩ := hq
  have hxk1 : x k ≤ 1 := by
    have h := Finset.single_le_sum (f := x) (fun i _ => hx0 i) (mem_univ k)
    rwa [hx1] at h
  have hstepsum : (∑ i, step d x k q i) = 0 := by
    unfold step
    rw [Finset.sum_add_distrib, hqsum, ← Finset.mul_sum]
    have hz : (∑ i, ((if i = k then (1:ℝ) else 0) - x i)) = 0 := by
      rw [Finset.sum_sub_distrib, hx1]; simp
    rw [hz]; ring
  constructor
  · rintro ⟨_, habs⟩
    simp only [step] at habs
    refine ⟨fun i hik => ?_, ?_⟩
    · have h := habs i
      rw [if_neg hik, show (0:ℝ) - x i = -x i from by ring, mul_neg,
          ← sub_eq_add_neg, abs_le] at h
      exact h.1
    · have h := habs k
      rw [if_pos rfl, mul_sub, mul_one, abs_le] at h
      linarith [h.2]
  · rintro ⟨hlow, hup⟩
    refine ⟨hstepsum, fun i => ?_⟩
    simp only [step]
    by_cases hik : i = k
    · rw [hik, if_pos rfl, mul_sub, mul_one, abs_le]
      have hqk := abs_le.mp (hqabs k)
      have hdxk : d * x k ≤ d := by nlinarith [hx0 k, hxk1]
      exact ⟨by linarith [hqk.1], by linarith [hup]⟩
    · rw [if_neg hik, show (0:ℝ) - x i = -x i from by ring, mul_neg,
          ← sub_eq_add_neg, abs_le]
      have hqi := abs_le.mp (hqabs i)
      have hdxi : 0 ≤ d * x i := mul_nonneg (le_of_lt hd0) (hx0 i)
      exact ⟨hlow i hik, by linarith [hqi.2]⟩
 
/-- Automatic rescue of a unique lower danger (paper §4.1, fact 3):
    a lower-dangerous `ℓ` is supported (`q ℓ < -1 + d·x ℓ` forces `x ℓ > 0`),
    and choosing it is safe when `d ≤ 2` (`y ℓ + d < -1 + d ≤ 1`). -/
lemma unique_danger_rescue {q : Fin m → ℝ} (hq : q ∈ Qbox m)
    {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    {ℓ : Fin m} (hℓ : q ℓ - d * x ℓ < -1)
    (hother : ∀ i, i ≠ ℓ → -1 ≤ q i - d * x i) :
    ℓ ∈ supp x ∧ step d x ℓ q ∈ Qbox m := by
  have hqp := hq
  simp only [Qbox, Set.mem_setOf_eq] at hqp
  obtain ⟨hqsum, hqabs⟩ := hqp
  have hqℓ := abs_le.mp (hqabs ℓ)
  have hxℓpos : 0 < x ℓ := by
    by_contra h
    push_neg at h
    have hz : x ℓ = 0 := le_antisymm h (hx0 ℓ)
    rw [hz] at hℓ; simp at hℓ; linarith [hqℓ.1]
  have hmem : ℓ ∈ supp x := by
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hxℓpos.ne'
  refine ⟨hmem, ?_⟩
  rw [step_mem_iff hq hd0 hx0 hx1 ℓ]
  exact ⟨hother, by linarith⟩
 
/-! ## Certificate completeness (paper §4.1) -/
 
/-- A state is a trap iff Mode D or Mode B holds at it. Case-split on the
    number of lower-dangerous coordinates: `≥ 2` is Mode D; exactly one is
    rescued by `unique_danger_rescue`; zero forces Mode B. -/
lemma trap_iff {q : Fin m → ℝ} (hq : q ∈ Qbox m)
    {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1) (hs : 2 ≤ suppCard x) :
    (¬ ∃ k ∈ supp x, step d x k q ∈ Qbox m) ↔
      ((∃ i j, i ≠ j ∧ q i - d * x i < -1 ∧ q j - d * x j < -1) ∨
       ((∀ i, -1 ≤ q i - d * x i) ∧
        ∀ k ∈ supp x, 1 - d < q k - d * x k)) := by
  have hsafe : ∀ k, (step d x k q ∈ Qbox m) ↔
      ((∀ i, i ≠ k → -1 ≤ q i - d * x i) ∧ q k - d * x k ≤ 1 - d) :=
    fun k => step_mem_iff hq hd0 hx0 hx1 k
  constructor
  · intro hnos
    have hk : ∀ k ∈ supp x,
        (∃ i, i ≠ k ∧ q i - d * x i < -1) ∨ 1 - d < q k - d * x k := by
      intro k hkm
      have hns : ¬ (step d x k q ∈ Qbox m) := fun h => hnos ⟨k, hkm, h⟩
      rw [hsafe k, not_and_or] at hns
      rcases hns with hA | hB
      · left; push_neg at hA; exact hA
      · right; push_neg at hB; exact hB
    by_cases htwo : ∃ i j, i ≠ j ∧ q i - d * x i < -1 ∧ q j - d * x j < -1
    · exact Or.inl htwo
    · right
      push_neg at htwo
      by_cases hone : ∃ ℓ, q ℓ - d * x ℓ < -1
      · exfalso
        obtain ⟨ℓ, hℓ⟩ := hone
        have hother : ∀ i, i ≠ ℓ → -1 ≤ q i - d * x i :=
          fun i hiℓ => htwo ℓ i (Ne.symm hiℓ) hℓ
        obtain ⟨hℓsupp, hℓstep⟩ := unique_danger_rescue hq hd0 hd2 hx0 hx1 hℓ hother
        exact hnos ⟨ℓ, hℓsupp, hℓstep⟩
      · push_neg at hone
        refine ⟨hone, ?_⟩
        intro k hkm
        rcases hk k hkm with hd' | hb
        · obtain ⟨i, _, hyi⟩ := hd'
          exact absurd (hone i) (not_le.mpr hyi)
        · exact hb
  · intro hdisj
    rintro ⟨k, hksupp, hkstep⟩
    rw [hsafe k] at hkstep
    obtain ⟨hallge, hkle⟩ := hkstep
    rcases hdisj with ⟨i, j, hij, hyi, hyj⟩ | ⟨hge, hub⟩
    · by_cases hik : i = k
      · have hjk : j ≠ k := by rw [← hik]; exact Ne.symm hij
        exact absurd (hallge j hjk) (not_le.mpr hyj)
      · exact absurd (hallge i hik) (not_le.mpr hyi)
    · exact absurd (hub k hksupp) (not_lt.mpr hkle)
 
/-! ## Mode D (paper Lemma 4.2) -/
 
/-- A state with two lower-dangerous coordinates exists iff `d σ₂(x) > 4 - m`.
    Necessity: sum over `univ`, splitting off `{i, j}`; bound the rest by
    `Finset.sum_le_card_nsmul` and `card_sdiff`; finish with `linarith`.
    Sufficiency: the strict inequality plus `d ≤ 2`, `σ₂ ≤ 1` forces `3 ≤ m`;
    take the positive attaining pair, set
    `ε := min (d*x i) (min (d*x j) (d*σ₂ - (4 - m))) / 2`, and use the
    explicit witness from the paper (an `if`-defined function). Membership
    checks are `Fin.sum_univ`-style bookkeeping plus `field_simp; ring_nf`
    and `linarith`/`positivity`. -/
lemma modeD_iff {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hm : 2 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    (∃ q ∈ Qbox m, ∃ i j, i ≠ j ∧
        q i - d * x i < -1 ∧ q j - d * x j < -1) ↔
      (4 : ℝ) - (m : ℝ) < d * sigma2 x := by
  have hσpos : 0 < sigma2 x := sigma2_pos x hx0 hs
  have hσ1 : sigma2 x ≤ 1 := by
    unfold sigma2
    split_ifs with hne
    · apply Finset.sup'_le
      intro p hp
      rw [Finset.mem_offDiag] at hp
      obtain ⟨_, _, hpne⟩ := hp
      calc x p.1 + x p.2
          = ∑ k ∈ ({p.1, p.2} : Finset (Fin m)), x k := (Finset.sum_pair hpne).symm
        _ ≤ ∑ k, x k :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hx0 k)
        _ = 1 := hx1
    · exact zero_le_one
  have hdσ2 : d * sigma2 x ≤ 2 := by nlinarith [hσ1, hσpos, hd0, hd2]
  constructor
  · rintro ⟨q, hq, i, j, hij, hqi, hqj⟩
    simp only [Qbox, Set.mem_setOf_eq] at hq
    obtain ⟨hqsum, hqabs⟩ := hq
    have hcompl : (∑ k ∈ ({i, j} : Finset (Fin m))ᶜ, q k) ≤ ((m : ℝ) - 2) := by
      have hb : (∑ k ∈ ({i, j} : Finset (Fin m))ᶜ, q k)
          ≤ (({i, j} : Finset (Fin m))ᶜ.card : ℝ) := by
        have h := Finset.sum_le_card_nsmul (({i, j} : Finset (Fin m))ᶜ) q 1
          (fun k _ => (abs_le.mp (hqabs k)).2)
        simpa using h
      have hcard : (({i, j} : Finset (Fin m))ᶜ.card : ℝ) = (m : ℝ) - 2 := by
        rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hij,
            Nat.cast_sub (by omega : 2 ≤ m)]
        norm_num
      rwa [hcard] at hb
    have hpair : (∑ k ∈ ({i, j} : Finset (Fin m)), q k) +
        (∑ k ∈ ({i, j} : Finset (Fin m))ᶜ, q k) = 0 := by
      rw [Finset.sum_add_sum_compl]; exact hqsum
    rw [Finset.sum_pair hij] at hpair
    have hqij : q i + q j = -(∑ k ∈ ({i, j} : Finset (Fin m))ᶜ, q k) := by linarith
    have hdax : d * (x i + x j) ≤ d * sigma2 x :=
      mul_le_mul_of_nonneg_left (add_le_sigma2 x hij) (le_of_lt hd0)
    have hexp : d * (x i + x j) = d * x i + d * x j := by ring
    linarith [hqi, hqj, hcompl, hqij, hdax, hexp]
  · intro hlt
    have hmR : (2 : ℝ) < (m : ℝ) := by linarith
    have hm2R : (0 : ℝ) < (m : ℝ) - 2 := by linarith
    have hm2ne : (m : ℝ) - 2 ≠ 0 := ne_of_gt hm2R
    obtain ⟨i, j, hij, hxi, hxj, hσeq⟩ := exists_sigma2_pair_pos x hx0 hs
    have h1 : 0 < d * x i := mul_pos hd0 hxi
    have h2 : 0 < d * x j := mul_pos hd0 hxj
    have h3 : 0 < d * sigma2 x - (4 - (m : ℝ)) := by linarith
    have hmin : 0 < min (d * x i) (min (d * x j) (d * sigma2 x - (4 - (m : ℝ)))) :=
      lt_min h1 (lt_min h2 h3)
    have mle1 : min (d * x i) (min (d * x j) (d * sigma2 x - (4 - (m : ℝ)))) ≤ d * x i :=
      min_le_left _ _
    have mle2 : min (d * x i) (min (d * x j) (d * sigma2 x - (4 - (m : ℝ)))) ≤ d * x j :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have mle3 : min (d * x i) (min (d * x j) (d * sigma2 x - (4 - (m : ℝ))))
        ≤ d * sigma2 x - (4 - (m : ℝ)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    set ε : ℝ := (min (d * x i) (min (d * x j) (d * sigma2 x - (4 - (m : ℝ))))) / 2 with hε
    have hε_pos : 0 < ε := by rw [hε]; linarith [hmin]
    have hεi : ε ≤ d * x i := by rw [hε]; linarith [mle1, hmin]
    have hεj : ε ≤ d * x j := by rw [hε]; linarith [mle2, hmin]
    have hScond : 2 * ε ≤ d * sigma2 x - (4 - (m : ℝ)) := by rw [hε]; linarith [mle3]
    set S : ℝ := 2 - d * (x i + x j) + 2 * ε with hS
    set c : ℝ := S / ((m : ℝ) - 2) with hc
    have hSmulEq : d * (x i + x j) = d * sigma2 x := by rw [hσeq]
    have hSpos : 0 < S := by rw [hS, hSmulEq]; linarith [hdσ2, hε_pos]
    have hSle : S ≤ (m : ℝ) - 2 := by rw [hS, hSmulEq]; linarith [hScond]
    have hc_pos : 0 < c := by rw [hc]; exact div_pos hSpos hm2R
    have hc_le : c ≤ 1 := by rw [hc, div_le_one hm2R]; exact hSle
    set q : Fin m → ℝ := fun k => if k = i then (-1 + d * x i - ε)
        else if k = j then (-1 + d * x j - ε) else c with hqdef
    have hqi_val : q i = -1 + d * x i - ε := by simp only [hqdef, if_true]
    have hqj_val : q j = -1 + d * x j - ε := by
      simp only [hqdef, if_true]; rw [if_neg (Ne.symm hij)]
    have hcompl_sum : (∑ k ∈ ({i, j} : Finset (Fin m))ᶜ, q k) = ((m : ℝ) - 2) * c := by
      have hcong : (∑ k ∈ ({i, j} : Finset (Fin m))ᶜ, q k)
          = ∑ _k ∈ ({i, j} : Finset (Fin m))ᶜ, c := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at hk
        push_neg at hk
        simp only [hqdef]; rw [if_neg hk.1, if_neg hk.2]
      rw [hcong, Finset.sum_const, Finset.card_compl, Fintype.card_fin,
          Finset.card_pair hij, nsmul_eq_mul]
      congr 1
      rw [Nat.cast_sub (by omega : 2 ≤ m)]
      norm_num
    refine ⟨q, ?_, i, j, hij, ?_, ?_⟩
    · simp only [Qbox, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩
      · rw [← Finset.sum_add_sum_compl ({i, j} : Finset (Fin m)) q, Finset.sum_pair hij,
            hqi_val, hqj_val, hcompl_sum, hc, hS]
        field_simp
        ring
      · intro k
        by_cases hki : k = i
        · rw [hki, hqi_val, abs_le]
          have hxi1 : x i ≤ 1 := by
            have h := Finset.single_le_sum (f := x) (fun t _ => hx0 t) (mem_univ i)
            rwa [hx1] at h
          have hdxi : d * x i ≤ 2 := by nlinarith [hxi1, hd2, hd0]
          exact ⟨by linarith [hεi], by linarith [hε_pos, hdxi]⟩
        · by_cases hkj : k = j
          · rw [hkj, hqj_val, abs_le]
            have hxj1 : x j ≤ 1 := by
              have h := Finset.single_le_sum (f := x) (fun t _ => hx0 t) (mem_univ j)
              rwa [hx1] at h
            have hdxj : d * x j ≤ 2 := by nlinarith [hxj1, hd2, hd0]
            exact ⟨by linarith [hεj], by linarith [hε_pos, hdxj]⟩
          · have hqk : q k = c := by simp only [hqdef]; rw [if_neg hki, if_neg hkj]
            rw [hqk, abs_le]
            exact ⟨by linarith [hc_pos], hc_le⟩
    · rw [hqi_val]; linarith [hε_pos]
    · rw [hqj_val]; linarith [hε_pos]
 
/-! ## Mode B (paper Lemma 4.3) -/
 
/-- A state with no lower danger and every supported coordinate upper-blocked
    exists iff `d (s - 1) > 2s - m`.
    Necessity: `-d = ∑ y > s(1-d) - (m-s)`; sum-splitting over `supp x`.
    Sufficiency: define `b i := if i ∈ supp x then 1 - d*(1 - x i) else -1`,
    show `∑ b = 2s - m - d(s-1) < 0` and `b i ∈ [-1, 1)`, then take the
    closed-form witness `q := b + t • (fun _ => 1 - b ·)` with
    `t := -(∑ b) / (m - ∑ b)`; the denominator is positive since `∑ b < 0`. -/
lemma modeB_iff {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hm : 2 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    (∃ q ∈ Qbox m, (∀ i, -1 ≤ q i - d * x i) ∧
        ∀ k ∈ supp x, 1 - d < q k - d * x k) ↔
      2 * (suppCard x : ℝ) - (m : ℝ) < d * ((suppCard x : ℝ) - 1) := by
  simp only [suppCard] at hs ⊢
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hsm : (supp x).card ≤ m := by
    have h := Finset.card_le_univ (supp x); rwa [Fintype.card_fin] at h
  have hcard_compl : (((supp x)ᶜ).card : ℝ) = (m : ℝ) - ((supp x).card : ℝ) := by
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub hsm]
  constructor
  · rintro ⟨q, hq, hlb, hub⟩
    simp only [Qbox, Set.mem_setOf_eq] at hq
    obtain ⟨hqsum, hqabs⟩ := hq
    have hne_supp : (supp x).Nonempty := Finset.card_pos.mp (by omega)
    have hlow : (∑ k ∈ supp x, (1 - d)) < ∑ k ∈ supp x, (q k - d * x k) :=
      Finset.sum_lt_sum_of_nonempty hne_supp (fun k hk => hub k hk)
    rw [Finset.sum_const, nsmul_eq_mul, mul_sub, mul_one,
        mul_comm ((supp x).card : ℝ) d] at hlow
    have hhigh : (∑ k ∈ (supp x)ᶜ, (-1 : ℝ)) ≤ ∑ k ∈ (supp x)ᶜ, (q k - d * x k) :=
      Finset.sum_le_sum (fun k _ => hlb k)
    rw [Finset.sum_const, nsmul_eq_mul, hcard_compl, mul_neg_one] at hhigh
    have hsplit : (∑ k ∈ supp x, (q k - d * x k)) +
        (∑ k ∈ (supp x)ᶜ, (q k - d * x k)) = -d := by
      rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, ← Finset.mul_sum, hqsum, hx1]; ring
    rw [mul_sub, mul_one]
    linarith [hlow, hhigh, hsplit]
  · intro hlt
    have hsx1 : (∑ i ∈ supp x, x i) = 1 := by
      rw [← hx1]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      exact hi
    have hxk_lt : ∀ k ∈ supp x, x k < 1 := by
      intro k hk
      obtain ⟨a, ha, b1, hb1, hab⟩ := Finset.one_lt_card.mp (show 1 < (supp x).card from hs)
      have hj : ∃ j, j ≠ k ∧ 0 < x j := by
        rcases eq_or_ne a k with rfl | hak
        · refine ⟨b1, hab.symm, ?_⟩
          simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hb1
          exact (hx0 b1).lt_of_ne (Ne.symm hb1)
        · refine ⟨a, hak, ?_⟩
          simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact (hx0 a).lt_of_ne (Ne.symm ha)
      obtain ⟨j, hjk, hxj⟩ := hj
      have hpair_le : x k + x j ≤ ∑ i, x i := by
        rw [← Finset.sum_pair (Ne.symm hjk)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hx0 i)
      rw [hx1] at hpair_le
      linarith
    set b : Fin m → ℝ := fun i => if i ∈ supp x then 1 - d * (1 - x i) else -1 with hbdef
    have hb_supp : ∀ i ∈ supp x, b i = 1 - d + d * x i := by
      intro i hi; simp only [hbdef]; rw [if_pos hi]; ring
    have hb_nsupp : ∀ i, i ∉ supp x → b i = -1 := by
      intro i hi; simp only [hbdef]; rw [if_neg hi]
    have hb_le1 : ∀ i, b i ≤ 1 := by
      intro i
      by_cases hi : i ∈ supp x
      · rw [hb_supp i hi]
        have hxi1 : x i ≤ 1 := by
          have h := Finset.single_le_sum (f := x) (fun a _ => hx0 a) (mem_univ i); rwa [hx1] at h
        nlinarith [hd0, hxi1]
      · rw [hb_nsupp i hi]; linarith
    have hb_ge : ∀ i, -1 ≤ b i := by
      intro i
      by_cases hi : i ∈ supp x
      · rw [hb_supp i hi]
        have hdxi : 0 ≤ d * x i := mul_nonneg hd0.le (hx0 i)
        linarith [hd2]
      · exact (hb_nsupp i hi).ge
    set P : ℝ := ∑ i, b i with hPdef
    have hPval : P = 2 * ((supp x).card : ℝ) - (m : ℝ) - d * (((supp x).card : ℝ) - 1) := by
      rw [hPdef, ← Finset.sum_add_sum_compl (supp x) b]
      have e1 : (∑ i ∈ supp x, b i) = ((supp x).card : ℝ) * (1 - d) + d := by
        rw [Finset.sum_congr rfl (fun i hi => hb_supp i hi), Finset.sum_add_distrib,
            Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hsx1, mul_one]
      have e2 : (∑ i ∈ (supp x)ᶜ, b i) = -((m : ℝ) - ((supp x).card : ℝ)) := by
        rw [Finset.sum_congr rfl (fun i hi => hb_nsupp i (Finset.mem_compl.mp hi)),
            Finset.sum_const, nsmul_eq_mul, hcard_compl, mul_neg_one]
      rw [e1, e2]; ring
    have hP_neg : P < 0 := by rw [hPval]; linarith [hlt]
    have hmP : (0 : ℝ) < (m : ℝ) - P := by linarith [hP_neg, hmpos]
    have hmPne : (m : ℝ) - P ≠ 0 := ne_of_gt hmP
    set t : ℝ := -P / ((m : ℝ) - P) with htdef
    have ht_pos : 0 < t := by rw [htdef]; exact div_pos (by linarith) hmP
    have ht_le1 : t ≤ 1 := by rw [htdef, div_le_one hmP]; linarith [hmpos]
    have ht_id : t * ((m : ℝ) - P) = -P := by rw [htdef]; field_simp
    set q : Fin m → ℝ := fun i => b i + t * (1 - b i) with hqdef
    have hq_val : ∀ i, q i = b i + t * (1 - b i) := fun i => by simp only [hqdef]
    have hy_supp : ∀ i ∈ supp x, q i - d * x i = 1 - d + t * (d * (1 - x i)) := by
      intro i hi; rw [hq_val i, hb_supp i hi]; ring
    have hy_nsupp : ∀ i, i ∉ supp x → q i - d * x i = -1 + 2 * t := by
      intro i hi
      have hx0i : x i = 0 := by
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi; exact hi
      rw [hq_val i, hb_nsupp i hi, hx0i]; ring
    refine ⟨q, ?_, ?_, ?_⟩
    · simp only [Qbox, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩
      · have hsumq : (∑ i, q i) = P + t * ((m : ℝ) - P) := by
          have hstep : (∑ i, q i) = (∑ i, b i) + ∑ i, t * (1 - b i) := by
            simp only [hq_val]; rw [Finset.sum_add_distrib]
          rw [hstep, ← hPdef, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← hPdef]
        rw [hsumq, ht_id]; ring
      · intro i
        rw [abs_le, hq_val i]
        constructor
        · nlinarith [hb_ge i, ht_pos, ht_le1]
        · nlinarith [hb_le1 i, ht_pos, ht_le1]
    · intro i
      by_cases hi : i ∈ supp x
      · rw [hy_supp i hi]
        have hxi1 : x i ≤ 1 := by
          have h := Finset.single_le_sum (f := x) (fun a _ => hx0 a) (mem_univ i); rwa [hx1] at h
        have hnn : 0 ≤ t * (d * (1 - x i)) :=
          mul_nonneg ht_pos.le (mul_nonneg hd0.le (by linarith))
        linarith [hd2]
      · rw [hy_nsupp i hi]; linarith [ht_pos]
    · intro k hk
      rw [hy_supp k hk]
      have hxk1 : x k < 1 := hxk_lt k hk
      have hpp : 0 < t * (d * (1 - x k)) :=
        mul_pos ht_pos (mul_pos hd0 (by linarith))
      linarith
 
/-! ## Main theorem (paper Theorem 3.1) -/
 
/-- **Fixed-Generator Predecessor Theorem**, multiplicative form.
    Assemble `trap_iff`, `modeD_iff`, `modeB_iff`; equality-is-safe is
    automatic because both trap conditions are strict. -/
theorem fgpt {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hm : 2 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    (∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m) ↔
      (d * sigma2 x ≤ (4 : ℝ) - (m : ℝ) ∧
       d * ((suppCard x : ℝ) - 1) ≤ 2 * (suppCard x : ℝ) - (m : ℝ)) := by
  have key : (∃ q ∈ Qbox m, ¬ ∃ k ∈ supp x, step d x k q ∈ Qbox m) ↔
      ((4:ℝ) - m < d * sigma2 x) ∨
      (2 * (suppCard x : ℝ) - m < d * ((suppCard x : ℝ) - 1)) := by
    constructor
    · rintro ⟨q, hq, htrap⟩
      rw [trap_iff hq hd0 hd2 hx0 hx1 hs] at htrap
      rcases htrap with hD | hB
      · left; rw [← modeD_iff hd0 hd2 hm hx0 hx1 hs]; exact ⟨q, hq, hD⟩
      · right; rw [← modeB_iff hd0 hd2 hm hx0 hx1 hs]; exact ⟨q, hq, hB⟩
    · rintro (hD | hB)
      · rw [← modeD_iff hd0 hd2 hm hx0 hx1 hs] at hD
        obtain ⟨q, hq, i, j, hij, hqi, hqj⟩ := hD
        exact ⟨q, hq, by
          rw [trap_iff hq hd0 hd2 hx0 hx1 hs]; exact Or.inl ⟨i, j, hij, hqi, hqj⟩⟩
      · rw [← modeB_iff hd0 hd2 hm hx0 hx1 hs] at hB
        obtain ⟨q, hq, hb1, hb2⟩ := hB
        exact ⟨q, hq, by
          rw [trap_iff hq hd0 hd2 hx0 hx1 hs]; exact Or.inr ⟨hb1, hb2⟩⟩
  constructor
  · intro hall
    constructor
    · by_contra hc; push_neg at hc
      obtain ⟨q, hq, hnk⟩ := key.mpr (Or.inl hc)
      exact hnk (hall q hq)
    · by_contra hc; push_neg at hc
      obtain ⟨q, hq, hnk⟩ := key.mpr (Or.inr hc)
      exact hnk (hall q hq)
  · rintro ⟨hle1, hle2⟩ q hq
    by_contra hnk
    rcases key.mp ⟨q, hq, hnk⟩ with h | h
    · linarith
    · linarith
 
/-- Ratio form of the threshold. Since `σ₂ x > 0` and `(s : ℝ) - 1 ≥ 1`,
    each cut divides cleanly: `div_le_iff` / `le_div_iff` with
    `sigma2_pos` and `hs`. Keep this thin — all content is in `fgpt`. -/
theorem fgpt_ratio {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hm : 2 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    (∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m) ↔
      d ≤ min ((2 * (suppCard x : ℝ) - m) / ((suppCard x : ℝ) - 1))
              (((4 : ℝ) - m) / sigma2 x) := by
  rw [fgpt hd0 hd2 hm hx0 hx1 hs, le_min_iff]
  have hσ : 0 < sigma2 x := sigma2_pos x hx0 hs
  have hs1 : 0 < (suppCard x : ℝ) - 1 := by
    have : (2:ℝ) ≤ (suppCard x : ℝ) := by exact_mod_cast hs
    linarith
  rw [le_div_iff₀ hs1, le_div_iff₀ hσ]
  tauto
 
/-- Rank-four obstruction (paper §10.2): for `m ≥ 4` no positive demand
    gives full one-step invariance. From `fgpt`: `d * σ₂ ≤ 4 - m ≤ 0`
    contradicts `d > 0` and `sigma2_pos`. -/
theorem no_invariance_of_four_le {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2)
    {x : Fin m → ℝ} (hm : 4 ≤ m) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : (∑ i, x i) = 1) (hs : 2 ≤ suppCard x) :
    ¬ (∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m) := by
  intro hall
  have hm2 : 2 ≤ m := le_trans (by norm_num) hm
  rw [fgpt hd0 hd2 hm2 hx0 hx1 hs] at hall
  obtain ⟨h1, _⟩ := hall
  have hpos : 0 < d * sigma2 x := mul_pos hd0 (sigma2_pos x hx0 hs)
  have hmle : (4:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  linarith
 
end FGPT
 

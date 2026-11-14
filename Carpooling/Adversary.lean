import Carpooling.Basic

/-!
  Adaptive unit-demand adversary and the subset-sum dichotomy
  (carpooling paper Theorem 5.1(b)).
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-! ## Arithmetic on index sequences -/

/-- Gauss sum over the reals: `∑_{i < n} i = n (n - 1) / 2`. -/
lemma sum_range_cast_id (n : ℕ) : (∑ i ∈ range n, (i : ℝ)) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- `∑_{j < n} |j + 1 - (n + 1)/2| ≤ n² / 4`, the total centred weight used to
    bound the potential `W` (paper §5, proof of (b)). -/
lemma sum_abs_centred_le (n : ℕ) :
    (∑ j ∈ range n, |(j : ℝ) + 1 - ((n : ℝ) + 1) / 2|) ≤ (n : ℝ) ^ 2 / 4 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num
  | more n ih _ =>
    rw [sum_range_succ, sum_range_succ']
    have hshift : ∀ j ∈ range n,
        |((j + 1 : ℕ) : ℝ) + 1 - (((n + 2 : ℕ) : ℝ) + 1) / 2| =
          |(j : ℝ) + 1 - ((n : ℝ) + 1) / 2| := by
      intro j _
      push_cast
      ring_nf
    rw [sum_congr rfl hshift]
    have h0 : |((0 : ℕ) : ℝ) + 1 - (((n + 2 : ℕ) : ℝ) + 1) / 2| = ((n : ℝ) + 1) / 2 := by
      push_cast
      rw [show (0 : ℝ) + 1 - ((n : ℝ) + 2 + 1) / 2 = -(((n : ℝ) + 1) / 2) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    have h1 : |((n + 1 : ℕ) : ℝ) + 1 - (((n + 2 : ℕ) : ℝ) + 1) / 2| = ((n : ℝ) + 1) / 2 := by
      push_cast
      rw [show (n : ℝ) + 1 + 1 - ((n : ℝ) + 2 + 1) / 2 = ((n : ℝ) + 1) / 2 by ring,
        abs_of_nonneg (by positivity)]
    rw [h0, h1]
    push_cast
    nlinarith [ih]

/-- Top-`k` sums of a zero-sum sequence with sorted gaps at least `γ`:
    `∑_{m-k ≤ n < m} s_n ≥ γ k (m - k) / 2` (paper §5, proof of (b)). -/
lemma top_sum_ge {s : ℕ → ℝ} {k : ℕ} {γ : ℝ} (hk : k ≤ m)
    (hgap : ∀ r, r + 1 < m → s r + γ ≤ s (r + 1))
    (hsum : (∑ n ∈ range m, s n) = 0) :
    γ * k * ((m : ℝ) - k) / 2 ≤ ∑ n ∈ Ico (m - k) m, s n := by
  set t : ℕ → ℝ := fun n => s n - γ * ((n : ℝ) - ((m : ℝ) - 1) / 2) with htdef
  have hmono : ∀ i j, i ≤ j → j < m → t i ≤ t j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j _ ih =>
      intro hj
      have h1 := hgap j hj
      have h2 := ih (by omega)
      simp only [htdef] at h2 ⊢
      push_cast
      linarith
  have htsum : (∑ n ∈ range m, t n) = 0 := by
    simp only [htdef]
    rw [sum_sub_distrib, hsum, ← mul_sum, sum_sub_distrib, sum_range_cast_id, sum_const,
      card_range, nsmul_eq_mul]
    ring
  have hsplit := sum_range_add_sum_Ico t (show m - k ≤ m by omega)
  have htop : 0 ≤ ∑ n ∈ Ico (m - k) m, t n := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · by_cases h0 : 0 ≤ t (m - k)
      · apply sum_nonneg
        intro n hn
        rw [mem_Ico] at hn
        exact h0.trans (hmono _ _ hn.1 hn.2)
      · have hneg : (∑ n ∈ range (m - k), t n) ≤ 0 := by
          apply sum_nonpos
          intro n hn
          rw [mem_range] at hn
          exact (hmono n (m - k) hn.le (by omega)).trans (not_le.mp h0).le
        linarith
  have hshift : (∑ n ∈ Ico (m - k) m, s n) =
      (∑ n ∈ Ico (m - k) m, t n) +
        γ * ∑ n ∈ Ico (m - k) m, ((n : ℝ) - ((m : ℝ) - 1) / 2) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    simp only [htdef]
    ring
  have hgauss : (∑ n ∈ Ico (m - k) m, ((n : ℝ) - ((m : ℝ) - 1) / 2)) =
      (k : ℝ) * ((m : ℝ) - k) / 2 := by
    rw [sum_Ico_eq_sub _ (show m - k ≤ m by omega)]
    simp only [sum_sub_distrib, sum_range_cast_id, sum_const, card_range, nsmul_eq_mul]
    rw [Nat.cast_sub hk]
    ring
  rw [hshift, hgauss]
  linarith

/-- Bottom-`k` sums of a zero-sum sequence with sorted gaps at least `γ`:
    `∑_{n < k} s_n ≤ -γ k (m - k) / 2` (paper §5, proof of (b)). -/
lemma bottom_sum_le {s : ℕ → ℝ} {k : ℕ} {γ : ℝ} (hk : k ≤ m)
    (hgap : ∀ r, r + 1 < m → s r + γ ≤ s (r + 1))
    (hsum : (∑ n ∈ range m, s n) = 0) :
    (∑ n ∈ range k, s n) ≤ -(γ * k * ((m : ℝ) - k) / 2) := by
  have htop := top_sum_ge (m := m) (k := m - k) (by omega) hgap hsum
  rw [show m - (m - k) = k by omega, Nat.cast_sub hk] at htop
  have hsplit := sum_range_add_sum_Ico s hk
  rw [hsum] at hsplit
  nlinarith

/-- Sums over `{j : Fin m | p j}` equal sums over `{n < m | p n}`. -/
lemma sum_fin_filter {M : Type*} [AddCommMonoid M] (p : ℕ → Prop) [DecidablePred p]
    (f : ℕ → M) :
    (∑ j ∈ univ.filter (fun j : Fin m => p j), f j) = ∑ n ∈ (range m).filter p, f n := by
  rw [sum_filter, sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun n => if p n then f n else 0) m

/-- Cardinality of `{j : Fin m | p j}` equals that of `{n < m | p n}`. -/
lemma card_fin_filter (p : ℕ → Prop) [DecidablePred p] :
    (univ.filter (fun j : Fin m => p j)).card = ((range m).filter p).card := by
  rw [card_eq_sum_ones, card_eq_sum_ones]
  exact sum_fin_filter p (fun _ => 1)

/-! ## The potential `W` -/

/-- Rank weight `c_j = j + 1` of sorted position `j`. -/
def rankWeight (j : Fin m) : ℝ := (j : ℕ) + 1

/-- Potential `W(q) = ∑_j (j + 1) q_{(j)}` over the sorted coordinates of `q`
    (paper §5, proof of (b)). -/
noncomputable def potential (q : Fin m → ℝ) : ℝ :=
  ∑ j, rankWeight j * q (Tuple.sort q j)

/-- Rearrangement bound: pairing ranks with any reordering of `q` gives at most
    `W(q)`. -/
lemma sum_rank_le_potential (q : Fin m → ℝ) (τ : Equiv.Perm (Fin m)) :
    (∑ j, rankWeight j * q (τ j)) ≤ potential q := by
  have hc : Monotone (rankWeight (m := m)) := by
    intro i j hij
    simp only [rankWeight]
    have : (i : ℕ) ≤ j := hij
    exact_mod_cast Nat.add_le_add_right this 1
  have hmv := hc.monovary (Tuple.monotone_sort q)
  have h := hmv.sum_mul_comp_perm_le_sum_mul (σ := (Tuple.sort q)⁻¹ * τ)
  simpa [potential] using h

/-- The potential vanishes at the origin. -/
@[simp] lemma potential_zero : potential (0 : Fin m → ℝ) = 0 := by
  simp [potential]

/-- On the zero-sum hyperplane, `‖q‖∞ ≤ (m-1)/2` forces `W(q) ≤ m²(m-1)/8`
    (paper §5, proof of (b)). -/
lemma potential_le {q : Fin m → ℝ} (hsum : (∑ i, q i) = 0)
    (hL : ∀ i, |q i| ≤ ((m : ℝ) - 1) / 2) (hm : 1 ≤ m) :
    potential q ≤ (m : ℝ) ^ 2 * ((m : ℝ) - 1) / 8 := by
  have hL0 : 0 ≤ ((m : ℝ) - 1) / 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set π := Tuple.sort q
  have hsumπ : (∑ j, q (π j)) = 0 := by rw [Equiv.sum_comp π q, hsum]
  have hcentre : potential q = ∑ j, (rankWeight j - ((m : ℝ) + 1) / 2) * q (π j) := by
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, hsumπ, mul_zero, sub_zero]
    rfl
  have hterm : ∀ j, (rankWeight j - ((m : ℝ) + 1) / 2) * q (π j) ≤
      |rankWeight j - ((m : ℝ) + 1) / 2| * (((m : ℝ) - 1) / 2) := by
    intro j
    calc (rankWeight j - ((m : ℝ) + 1) / 2) * q (π j)
        ≤ |(rankWeight j - ((m : ℝ) + 1) / 2) * q (π j)| := le_abs_self _
      _ = |rankWeight j - ((m : ℝ) + 1) / 2| * |q (π j)| := abs_mul _ _
      _ ≤ |rankWeight j - ((m : ℝ) + 1) / 2| * (((m : ℝ) - 1) / 2) :=
          mul_le_mul_of_nonneg_left (hL _) (abs_nonneg _)
  have hweights : (∑ j : Fin m, |rankWeight j - ((m : ℝ) + 1) / 2|) ≤ (m : ℝ) ^ 2 / 4 := by
    have h := sum_abs_centred_le m
    rw [← Fin.sum_univ_eq_sum_range
      (fun j : ℕ => |(j : ℝ) + 1 - ((m : ℝ) + 1) / 2|) m] at h
    exact h
  rw [hcentre]
  calc (∑ j, (rankWeight j - ((m : ℝ) + 1) / 2) * q (π j))
      ≤ ∑ j, |rankWeight j - ((m : ℝ) + 1) / 2| * (((m : ℝ) - 1) / 2) :=
        sum_le_sum fun j _ => hterm j
    _ = (∑ j, |rankWeight j - ((m : ℝ) + 1) / 2|) * (((m : ℝ) - 1) / 2) := by
        rw [sum_mul]
    _ ≤ (m : ℝ) ^ 2 / 4 * (((m : ℝ) - 1) / 2) :=
        mul_le_mul_of_nonneg_right hweights hL0
    _ = (m : ℝ) ^ 2 * ((m : ℝ) - 1) / 8 := by ring

/-! ## The adversary -/

/-- The adversary's generator `x = η e_a + (1 - η) e_b` (paper §5, proof of (b)). -/
noncomputable def pairX (η : ℝ) (a b : Fin m) : Fin m → ℝ :=
  fun i => (if i = a then η else 0) + (if i = b then 1 - η else 0)

/-- `p = (π r, π (r + 1))` is an adjacent pair in the sorted order `π` of `q`
    with gap `q_{π(r+1)} - q_{π(r)} ≤ 1 - 2η` (paper §5, proof of (b)). -/
def IsSmallGap (η : ℝ) (q : Fin m → ℝ) (p : Fin m × Fin m) : Prop :=
  ∃ r : ℕ, ∃ h : r + 1 < m, p.1 = Tuple.sort q ⟨r, by omega⟩ ∧
    p.2 = Tuple.sort q ⟨r + 1, h⟩ ∧ q p.2 - q p.1 ≤ 1 - 2 * η

open Classical in
/-- The adversary's sorted pair at state `q`, or `none` when every sorted gap
    exceeds `1 - 2η` (paper §5, proof of (b)). -/
noncomputable def advPair (η : ℝ) (q : Fin m → ℝ) : Option (Fin m × Fin m) :=
  if h : ∃ p, IsSmallGap η q p then some (Classical.choose h) else none

/-- One round against the adversary: it presents `d = 1` and `x = pairX η a b`,
    and the online algorithm takes `b` (`true`) or `a` (`false`). These are the
    only support-respecting choices (`supp_pairX`). -/
noncomputable def advStep (η : ℝ) (b : Bool) (q : Fin m → ℝ) : Fin m → ℝ :=
  match advPair η q with
  | none => q
  | some p => step 1 (pairX η p.1 p.2) (if b then p.2 else p.1) q

/-- The trajectory `q^t` from `q^0 = 0` produced by the adversary against the
    choice sequence `choice` (paper §5, proof of (b)). -/
noncomputable def advTraj (η : ℝ) (choice : ℕ → Bool) : ℕ → Fin m → ℝ
  | 0 => 0
  | t + 1 => advStep η (choice t) (advTraj η choice t)

/-- The adversary's generator is a probability vector. -/
lemma sum_pairX (η : ℝ) (a b : Fin m) : (∑ i, pairX η a b i) = 1 := by
  simp [pairX, sum_add_distrib]

/-- The adversary's generator is nonnegative for `0 ≤ η ≤ 1`. -/
lemma pairX_nonneg {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (a b : Fin m) (i : Fin m) :
    0 ≤ pairX η a b i := by
  simp only [pairX]
  split_ifs <;> linarith

/-- For `0 < η < 1` and `a ≠ b`, the support of the adversary's generator is
    exactly `{a, b}`, so a support-respecting algorithm picks `a` or `b`. -/
lemma supp_pairX {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {a b : Fin m} (hab : a ≠ b) :
    supp (pairX η a b) = {a, b} := by
  ext i
  simp only [supp, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, pairX]
  rcases eq_or_ne i a with rfl | hia
  · simp only [if_true, if_neg hab, true_or, iff_true]
    linarith
  · rcases eq_or_ne i b with rfl | hib
    · simp only [if_neg hia, if_true, or_true, iff_true]
      linarith
    · simp [hia, hib]

/-- A small-gap pair consists of two distinct indices. -/
lemma IsSmallGap.ne {η : ℝ} {q : Fin m → ℝ} {p : Fin m × Fin m} (h : IsSmallGap η q p) :
    p.1 ≠ p.2 := by
  obtain ⟨r, hr, h1, h2, _⟩ := h
  rw [h1, h2]
  intro heq
  have := congrArg Fin.val ((Tuple.sort q).injective heq)
  simp at this

/-- `advPair` returns a small-gap pair when it returns one. -/
lemma isSmallGap_of_advPair {η : ℝ} {q : Fin m → ℝ} {p : Fin m × Fin m}
    (h : advPair η q = some p) : IsSmallGap η q p := by
  unfold advPair at h
  split_ifs at h with hex
  rw [← Option.some_inj.mp h]
  exact Classical.choose_spec hex

/-- `advPair` is `none` exactly when no sorted gap is small. -/
lemma advPair_eq_none_iff {η : ℝ} {q : Fin m → ℝ} :
    advPair η q = none ↔ ¬ ∃ p, IsSmallGap η q p := by
  unfold advPair
  split_ifs with hex <;> simp [hex]

/-- Rounds against the adversary preserve the zero-sum hyperplane. -/
lemma sum_advStep (η : ℝ) (b : Bool) (q : Fin m → ℝ) :
    (∑ i, advStep η b q i) = ∑ i, q i := by
  unfold advStep
  cases advPair η q with
  | none => rfl
  | some p => exact sum_step_univ (sum_pairX η _ _) 1 _ q

/-- The adversary trajectory stays on the zero-sum hyperplane. -/
lemma sum_advTraj (η : ℝ) (choice : ℕ → Bool) (t : ℕ) :
    (∑ i, advTraj (m := m) η choice t i) = 0 := by
  induction t with
  | zero => simp [advTraj]
  | succ t ih => simp only [advTraj]; rw [sum_advStep, ih]

/-- Effect of a swap of adjacent ranks on the rank weights. -/
lemma rankWeight_swap {s0 s1 : Fin m} (hs : (s1 : ℕ) = s0 + 1) (j : Fin m) :
    rankWeight (Equiv.swap s0 s1 j) =
      rankWeight j + (if j = s0 then 1 else 0) - (if j = s1 then 1 else 0) := by
  have hne : s0 ≠ s1 := fun h => by rw [h] at hs; omega
  rw [Equiv.swap_apply_def]
  rcases eq_or_ne j s0 with rfl | h0
  · simp only [if_true, if_neg hne, rankWeight, hs]
    push_cast
    ring
  · rcases eq_or_ne j s1 with rfl | h1
    · simp only [if_neg h0, if_true, rankWeight, hs]
      push_cast
      ring
    · simp [h0, h1]

/-- Each adversary round raises the potential by at least `η`, whichever
    endpoint the algorithm picks (paper §5, proof of (b)). -/
lemma potential_step {η : ℝ} {q : Fin m → ℝ} {a b : Fin m}
    (hgap : IsSmallGap η q (a, b)) {k : Fin m} (hk : k = a ∨ k = b) :
    potential q + η ≤ potential (step 1 (pairX η a b) k q) := by
  obtain ⟨r, hr, ha, hb, hg⟩ := hgap
  simp only at ha hb hg
  set π := Tuple.sort q with hπ
  set s0 : Fin m := ⟨r, by omega⟩ with hs0
  set s1 : Fin m := ⟨r + 1, hr⟩ with hs1
  have hs : (s1 : ℕ) = s0 + 1 := rfl
  have hne : s0 ≠ s1 := fun h => by rw [h] at hs; omega
  have hc : rankWeight s1 = rankWeight s0 + 1 := by
    simp only [rankWeight, hs]
    push_cast
    ring
  set q' := step 1 (pairX η a b) k q with hq'
  have hW : potential q = ∑ j, rankWeight j * q (π j) := rfl
  rcases hk with rfl | rfl
  · have hD : ∀ j, q' (π j) = q (π j) +
        (1 - η) * ((if j = s0 then 1 else 0) - (if j = s1 then 1 else 0)) := by
      intro j
      simp only [hq', step, pairX, ha, hb, Equiv.apply_eq_iff_eq]
      rcases eq_or_ne j s0 with rfl | h0
      · simp [hne]
      · rcases eq_or_ne j s1 with rfl | h1
        · simp [h0]
        · simp [h0, h1]
    have hreidx : (∑ j, rankWeight j * q' (π (Equiv.swap s0 s1 j))) =
        ∑ j, rankWeight (Equiv.swap s0 s1 j) * q' (π j) := by
      rw [← Equiv.sum_comp (Equiv.swap s0 s1)
        (fun j => rankWeight (Equiv.swap s0 s1 j) * q' (π j))]
      simp only [Equiv.swap_apply_self]
    have hsum : (∑ j, rankWeight (Equiv.swap s0 s1 j) * q' (π j)) =
        potential q - (1 - η) + q' (π s0) - q' (π s1) := by
      simp only [rankWeight_swap hs, hD, hW]
      simp only [add_mul, sub_mul, mul_add, mul_sub, ite_mul, one_mul, zero_mul,
        mul_ite, mul_one, mul_zero, sum_add_distrib, sum_sub_distrib, sum_ite_eq',
        mem_univ, if_true, if_neg hne, if_neg hne.symm, hc]
      ring
    have hτ := sum_rank_le_potential q' (π * Equiv.swap s0 s1)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hτ
    rw [hreidx, hsum, hD s0, hD s1] at hτ
    simp only [if_true, if_neg hne, if_neg hne.symm] at hτ
    rw [← ha, ← hb] at hτ
    linarith
  · have hD : ∀ j, q' (π j) = q (π j) +
        η * ((if j = s1 then 1 else 0) - (if j = s0 then 1 else 0)) := by
      intro j
      simp only [hq', step, pairX, ha, hb, Equiv.apply_eq_iff_eq]
      rcases eq_or_ne j s0 with rfl | h0
      · simp [hne]
      · rcases eq_or_ne j s1 with rfl | h1
        · simp [h0]
        · simp [h0, h1]
    have hτ := sum_rank_le_potential q' π
    simp only [hD] at hτ
    simp only [mul_add, mul_sub, mul_ite, mul_one, mul_zero, sum_add_distrib,
      sum_sub_distrib, sum_ite_eq', mem_univ, if_true, ← hW, hc] at hτ
    linarith

/-- Against the adversary, a round with a small gap raises the potential by at
    least `η` (paper §5, proof of (b)). -/
lemma potential_advStep {η : ℝ} {q : Fin m → ℝ} {p : Fin m × Fin m}
    (hp : advPair η q = some p) (b : Bool) :
    potential q + η ≤ potential (advStep η b q) := by
  have hgap := isSmallGap_of_advPair hp
  unfold advStep
  rw [hp]
  exact potential_step (a := p.1) (b := p.2) hgap (by cases b <;> simp)

/-- At the origin every sorted gap is `0 ≤ 1 - 2η`. -/
lemma exists_smallGap_zero (hm : 2 ≤ m) {η : ℝ} (hη : η ≤ 1 / 2) :
    ∃ p, IsSmallGap η (0 : Fin m → ℝ) p :=
  ⟨(Tuple.sort (0 : Fin m → ℝ) ⟨0, by omega⟩, Tuple.sort (0 : Fin m → ℝ) ⟨0 + 1, by omega⟩),
    0, by omega, rfl, rfl, by simp only [Pi.zero_apply, sub_zero]; linarith⟩

/-- With no small gap, every sorted gap exceeds `1 - 2η`. -/
lemma sorted_gap_gt {η : ℝ} {q : Fin m → ℝ} (h : ¬ ∃ p, IsSmallGap η q p) (r : ℕ)
    (hr : r + 1 < m) :
    q (Tuple.sort q ⟨r, by omega⟩) + (1 - 2 * η) < q (Tuple.sort q ⟨r + 1, hr⟩) := by
  by_contra hle
  push Not at hle
  exact h ⟨(Tuple.sort q ⟨r, by omega⟩, Tuple.sort q ⟨r + 1, hr⟩), r, hr, rfl, rfl,
    by simp only; linarith⟩

/-- With all sorted gaps at least `γ` on the zero-sum hyperplane, the `k`
    largest coordinates sum to at least `γ k (m - k)/2` and the `k` smallest to
    at most `-γ k (m - k)/2` (paper §5, proof of (b)). -/
lemma exists_extreme_subsets {q : Fin m → ℝ} {γ : ℝ} (hsum : (∑ i, q i) = 0)
    (hgap : ∀ r (h : r + 1 < m),
      q (Tuple.sort q ⟨r, by omega⟩) + γ ≤ q (Tuple.sort q ⟨r + 1, h⟩))
    {k : ℕ} (hk : k ≤ m) :
    ∃ Aplus Aminus : Finset (Fin m), Aplus.card = k ∧ Aminus.card = k ∧
      γ * k * ((m : ℝ) - k) / 2 ≤ ∑ i ∈ Aplus, q i ∧
      ∑ i ∈ Aminus, q i ≤ -(γ * k * ((m : ℝ) - k) / 2) := by
  set π := Tuple.sort q with hπ
  set s : ℕ → ℝ := fun n => if h : n < m then q (π ⟨n, h⟩) else 0 with hsdef
  have hs : ∀ j : Fin m, s j = q (π j) := fun j => by simp [hsdef, j.isLt]
  have hsgap : ∀ r, r + 1 < m → s r + γ ≤ s (r + 1) := by
    intro r hr
    simp only [hsdef, dif_pos hr, dif_pos (show r < m by omega)]
    exact hgap r hr
  have hssum : (∑ n ∈ range m, s n) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range s m]
    simp only [hs]
    rw [Equiv.sum_comp π q, hsum]
  have hIco : (range m).filter (fun n => m - k ≤ n) = Ico (m - k) m := by
    ext n
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  have hrange : (range m).filter (fun n => n < k) = range k := by
    ext n
    simp only [mem_filter, mem_range]
    omega
  refine ⟨(univ.filter (fun j : Fin m => m - k ≤ (j : ℕ))).map π.toEmbedding,
    (univ.filter (fun j : Fin m => (j : ℕ) < k)).map π.toEmbedding, ?_, ?_, ?_, ?_⟩
  · rw [card_map]
    refine (card_fin_filter (m := m) (fun n => m - k ≤ n)).trans ?_
    rw [hIco, Nat.card_Ico]
    omega
  · rw [card_map]
    refine (card_fin_filter (m := m) (fun n => n < k)).trans ?_
    rw [hrange, card_range]
  · rw [sum_map]
    have h1 : (∑ j ∈ univ.filter (fun j : Fin m => m - k ≤ (j : ℕ)), q (π.toEmbedding j)) =
        ∑ j ∈ univ.filter (fun j : Fin m => m - k ≤ (j : ℕ)), s j :=
      sum_congr rfl fun j _ => (hs j).symm
    rw [h1]
    refine le_of_le_of_eq ?_ (sum_fin_filter (m := m) (fun n => m - k ≤ n) s).symm
    rw [hIco]
    exact top_sum_ge hk hsgap hssum
  · rw [sum_map]
    have h1 : (∑ j ∈ univ.filter (fun j : Fin m => (j : ℕ) < k), q (π.toEmbedding j)) =
        ∑ j ∈ univ.filter (fun j : Fin m => (j : ℕ) < k), s j :=
      sum_congr rfl fun j _ => (hs j).symm
    rw [h1]
    refine le_of_eq_of_le (sum_fin_filter (m := m) (fun n => n < k) s) ?_
    rw [hrange]
    exact bottom_sum_le hk hsgap hssum

/-! ## Theorem 5.1(b) -/

/-- The adversary's share parameter `η = 2δ / m²`. -/
noncomputable def advEta (m : ℕ) (δ : ℝ) : ℝ := 2 * δ / (m : ℝ) ^ 2

/-- The adversary's horizon `T = ⌊m⁴ (m - 1) / (16 δ)⌋ + 1`. -/
noncomputable def advHorizon (m : ℕ) (δ : ℝ) : ℕ :=
  ⌊(m : ℝ) ^ 4 * ((m : ℝ) - 1) / (16 * δ)⌋₊ + 1

/-- The play `q^t` of the paper's adversary with parameter `δ` against the
    choice sequence `choice`. -/
noncomputable def advPlay (m : ℕ) (δ : ℝ) (choice : ℕ → Bool) : ℕ → Fin m → ℝ :=
  advTraj (advEta m δ) choice

/-- Halting rule: the adversary stops once `‖q‖∞ > (m-1)/2` or every sorted
    gap exceeds `1 - 2η`. -/
def AdvHalts (η : ℝ) (q : Fin m → ℝ) : Prop :=
  (∃ i, ((m : ℝ) - 1) / 2 < |q i|) ∨ ¬ ∃ p, IsSmallGap η q p

/-- **Theorem 5.1(b)** (adaptive subset-sum dichotomy). Fix `m ≥ 2` and
    `0 < δ ≤ (m-1)/2`. Against every online support-respecting algorithm
    (encoded by `choice`, since each presented support is `{a, b}`), the
    unit-demand adversary first halts at some `1 ≤ t* ≤ T`, and either
    (i) `‖q^{t*}‖∞ > (m-1)/2`, or (ii) `‖q^t‖∞ ≤ (m-1)/2` for all
    `1 ≤ t ≤ t*` and, for every `1 ≤ k ≤ m-1`, some `k`-sets `A₊`, `A₋` have
    `q^{t*}(A₊) > k(m-k)/2 - δ` and `q^{t*}(A₋) < -k(m-k)/2 + δ`. -/
theorem adversary_dichotomy (hm : 2 ≤ m) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ ((m : ℝ) - 1) / 2) (choice : ℕ → Bool) :
    ∃ tstar, 1 ≤ tstar ∧ tstar ≤ advHorizon m δ ∧
      AdvHalts (advEta m δ) (advPlay m δ choice tstar) ∧
      (∀ t, 1 ≤ t → t < tstar → ¬ AdvHalts (advEta m δ) (advPlay m δ choice t)) ∧
      ((∃ i, ((m : ℝ) - 1) / 2 < |advPlay m δ choice tstar i|) ∨
       ((∀ t, 1 ≤ t → t ≤ tstar → ∀ i, |advPlay m δ choice t i| ≤ ((m : ℝ) - 1) / 2) ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ m - 1 → ∃ Aplus Aminus : Finset (Fin m),
          Aplus.card = k ∧ Aminus.card = k ∧
          (k : ℝ) * ((m : ℝ) - k) / 2 - δ < ∑ i ∈ Aplus, advPlay m δ choice tstar i ∧
          ∑ i ∈ Aminus, advPlay m δ choice tstar i < -((k : ℝ) * ((m : ℝ) - k) / 2) + δ)) := by
  classical
  set η := advEta m δ with hηdef
  set q := advPlay m δ choice with hqdef
  set T := advHorizon m δ with hTdef
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hηm : η * (m : ℝ) ^ 2 = 2 * δ := by
    rw [hηdef, advEta]
    field_simp
  have hη0 : 0 < η := by rw [hηdef, advEta]; positivity
  have hηhalf : η ≤ 1 / 2 := by
    have h4 : 4 * η * (m : ℝ) ^ 2 ≤ 2 * (m : ℝ) ^ 2 := by nlinarith [sq_nonneg ((m : ℝ) - 2)]
    nlinarith
  have hq0 : q 0 = 0 := rfl
  have hsumq : ∀ t, (∑ i, q t i) = 0 := fun t => sum_advTraj η choice t
  have hqsucc : ∀ t, q (t + 1) = advStep η (choice t) (q t) := fun _ => rfl
  have hT1 : 1 ≤ T := by rw [hTdef, advHorizon]; omega
  have hTη : (m : ℝ) ^ 2 * ((m : ℝ) - 1) / 8 < T * η := by
    have hT : (m : ℝ) ^ 4 * ((m : ℝ) - 1) / (16 * δ) < T := by
      rw [hTdef, advHorizon]
      push_cast
      exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ (by positivity)] at hT
    have h8 : (m : ℝ) ^ 2 * ((m : ℝ) - 1) / 8 * (m : ℝ) ^ 2 < T * η * (m : ℝ) ^ 2 := by
      rw [mul_assoc (T : ℝ), hηm]
      nlinarith
    exact lt_of_mul_lt_mul_right h8 hm2.le
  have hex : ∃ t, 1 ≤ t ∧ t ≤ T ∧ AdvHalts η (q t) := by
    by_contra hno
    push Not at hno
    have hgrow : ∀ t, t ≤ T → (t : ℝ) * η ≤ potential (q t) := by
      intro t
      induction t with
      | zero => intro _; simp [hq0]
      | succ t ih =>
        intro ht
        have hgap : ∃ p, IsSmallGap η (q t) p := by
          rcases Nat.eq_zero_or_pos t with rfl | htpos
          · rw [hq0]
            exact exists_smallGap_zero hm hηhalf
          · have hnh := hno t htpos (by omega)
            simp only [AdvHalts, not_or, not_not] at hnh
            exact hnh.2
        obtain ⟨p, hp⟩ : ∃ p, advPair η (q t) = some p := by
          cases h : advPair η (q t) with
          | none => exact absurd hgap (advPair_eq_none_iff.mp h)
          | some p => exact ⟨p, rfl⟩
        have hstep := potential_advStep hp (choice t)
        rw [← hqsucc] at hstep
        have := ih (by omega)
        push_cast
        linarith
    have hnT := hno T hT1 le_rfl
    simp only [AdvHalts, not_or, not_exists, not_lt] at hnT
    have hup := potential_le (hsumq T) hnT.1 (by omega)
    have hlo := hgrow T le_rfl
    linarith
  set tstar := Nat.find hex with htstar
  obtain ⟨ht1, htT, hthalt⟩ := Nat.find_spec hex
  have hbefore : ∀ t, 1 ≤ t → t < tstar → ¬ AdvHalts η (q t) := by
    intro t ht1' htlt hh
    exact Nat.find_min hex htlt ⟨ht1', by omega, hh⟩
  refine ⟨tstar, ht1, htT, hthalt, hbefore, ?_⟩
  by_cases hbig : ∃ i, ((m : ℝ) - 1) / 2 < |q tstar i|
  · exact Or.inl hbig
  · right
    have hnogap : ¬ ∃ p, IsSmallGap η (q tstar) p := by
      rcases hthalt with h | h
      · exact absurd h hbig
      · exact h
    refine ⟨?_, ?_⟩
    · intro t ht1' htle i
      rcases lt_or_eq_of_le htle with hlt | rfl
      · have hnh := hbefore t ht1' hlt
        simp only [AdvHalts, not_or, not_exists, not_lt] at hnh
        exact hnh.1 i
      · push Not at hbig
        exact hbig i
    · intro k hk1 hkm
      have hgap : ∀ r (h : r + 1 < m), q tstar (Tuple.sort (q tstar) ⟨r, by omega⟩) +
          (1 - 2 * η) ≤ q tstar (Tuple.sort (q tstar) ⟨r + 1, h⟩) :=
        fun r h => (sorted_gap_gt hnogap r h).le
      obtain ⟨Aplus, Aminus, hcp, hcm, hp, hmn⟩ :=
        exists_extreme_subsets (hsumq tstar) hgap (k := k) (by omega)
      refine ⟨Aplus, Aminus, hcp, hcm, ?_, ?_⟩
      · have hkR : (k : ℝ) * ((m : ℝ) - k) ≤ (m : ℝ) ^ 2 / 4 := by
          nlinarith [sq_nonneg ((m : ℝ) - 2 * k)]
        have hk0 : 0 ≤ (k : ℝ) * ((m : ℝ) - k) := by
          have : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
        have hsmall : η * ((k : ℝ) * ((m : ℝ) - k)) ≤ δ / 2 := by
          have := mul_le_mul_of_nonneg_left hkR hη0.le
          nlinarith
        nlinarith
      · have hkR : (k : ℝ) * ((m : ℝ) - k) ≤ (m : ℝ) ^ 2 / 4 := by
          nlinarith [sq_nonneg ((m : ℝ) - 2 * k)]
        have hsmall : η * ((k : ℝ) * ((m : ℝ) - k)) ≤ δ / 2 := by
          have := mul_le_mul_of_nonneg_left hkR hη0.le
          nlinarith
        nlinarith

/-- **Theorem 5.1(b)**, sup-norm form: every online support-respecting
    algorithm reaches `‖q^t‖∞ > (m-1)/2 - δ` at some round `1 ≤ t ≤ T`, so
    the constant `(m-1)/2` of Theorem 5.1(a) cannot be improved. -/
theorem adversary_sup_norm (hm : 2 ≤ m) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ ((m : ℝ) - 1) / 2) (choice : ℕ → Bool) :
    ∃ t, 1 ≤ t ∧ t ≤ advHorizon m δ ∧
      ∃ i, ((m : ℝ) - 1) / 2 - δ < |advPlay m δ choice t i| := by
  obtain ⟨tstar, ht1, htT, -, -, hcase⟩ := adversary_dichotomy hm hδ0 hδ choice
  refine ⟨tstar, ht1, htT, ?_⟩
  rcases hcase with ⟨i, hi⟩ | ⟨-, hsets⟩
  · exact ⟨i, by linarith⟩
  · obtain ⟨Aplus, -, hcp, -, hp, -⟩ := hsets 1 le_rfl (by omega)
    obtain ⟨i, rfl⟩ := card_eq_one.mp hcp
    refine ⟨i, ?_⟩
    rw [sum_singleton] at hp
    push_cast at hp
    have := le_abs_self (advPlay m δ choice tstar i)
    linarith

end Carpooling

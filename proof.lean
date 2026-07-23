/-
  Fixed-Generator Predecessor Theorem — Lean 4 / mathlib formalization skeleton.
 
  Maps to the paper's Section 4 (the trap classification), which is the only
  part needed for Theorem 3.1. Farkas / support-function sections are optional.
 
  STATUS: untested scaffold. Statements only; every proof is `sorry`.
  Lemma names in mathlib drift — use `exact?`, loogle, or LeanSearch to
  resolve any that have moved.
 
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
  sorry
 
/-- Some pair attains `σ₂`, and with `s ≥ 2` both members can be taken
    strictly positive (needed for Mode D's `ε < d·xᵢ`).
    Take `i` maximizing `x`, then `j` maximizing over `univ \ {i}`;
    positivity of both follows from the existence of two positive coords. -/
lemma exists_sigma2_pair_pos (x : Fin m → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hs : 2 ≤ suppCard x) :
    ∃ i j, i ≠ j ∧ 0 < x i ∧ 0 < x j ∧ sigma2 x = x i + x j := by
  sorry
 
/-- `σ₂ x > 0` when `s ≥ 2` — needed for the ratio-form corollary and the
    `m ≥ 4` obstruction. -/
lemma sigma2_pos (x : Fin m → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hs : 2 ≤ suppCard x) :
    0 < sigma2 x := by
  sorry
 
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
  sorry
 
/-- Automatic rescue of a unique lower danger (paper §4.1, fact 3):
    a lower-dangerous `ℓ` is supported (`q ℓ < -1 + d·x ℓ` forces `x ℓ > 0`),
    and choosing it is safe when `d ≤ 2` (`y ℓ + d < -1 + d ≤ 1`). -/
lemma unique_danger_rescue {q : Fin m → ℝ} (hq : q ∈ Qbox m)
    {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    {ℓ : Fin m} (hℓ : q ℓ - d * x ℓ < -1)
    (hother : ∀ i, i ≠ ℓ → -1 ≤ q i - d * x i) :
    ℓ ∈ supp x ∧ step d x ℓ q ∈ Qbox m := by
  sorry
 
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
  sorry
 
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
  sorry
 
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
  sorry
 
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
  sorry
 
/-- Ratio form of the threshold. Since `σ₂ x > 0` and `(s : ℝ) - 1 ≥ 1`,
    each cut divides cleanly: `div_le_iff` / `le_div_iff` with
    `sigma2_pos` and `hs`. Keep this thin — all content is in `fgpt`. -/
theorem fgpt_ratio {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hm : 2 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    (∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m) ↔
      d ≤ min ((2 * (suppCard x : ℝ) - m) / ((suppCard x : ℝ) - 1))
              (((4 : ℝ) - m) / sigma2 x) := by
  sorry
 
/-- Rank-four obstruction (paper §10.2): for `m ≥ 4` no positive demand
    gives full one-step invariance. From `fgpt`: `d * σ₂ ≤ 4 - m ≤ 0`
    contradicts `d > 0` and `sigma2_pos`. -/
theorem no_invariance_of_four_le {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2)
    {x : Fin m → ℝ} (hm : 4 ≤ m) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : (∑ i, x i) = 1) (hs : 2 ≤ suppCard x) :
    ¬ (∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m) := by
  sorry
 
end FGPT
 

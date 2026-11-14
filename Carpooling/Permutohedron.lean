import Carpooling.SubsetSum

/-!
  The quadratic zero-sum permutohedron `P_m(B)` (carpooling paper §3) and the
  quadratic exchange identity (Lemma 4.1).
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- Quadratic profile `β^{(m)}(z) = z (m - z) / (m - 1)` (paper §3), taken at a
    real argument so that Lemma 4.1 holds for all integers. -/
noncomputable def beta (m : ℕ) (z : ℝ) : ℝ := z * ((m : ℝ) - z) / ((m : ℝ) - 1)

/-- `m - 1 > 0` over the reals when `m ≥ 2`. -/
lemma cast_sub_one_pos (hm : 2 ≤ m) : (0 : ℝ) < (m : ℝ) - 1 := by
  have h : (2 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-- Lemma 4.1 (quadratic exchange identity):
    `(p + 1) β_r - p β_{r+1} - β_{r-p} = p (p + 1) / (m - 1)`. -/
lemma beta_exchange (hm : 2 ≤ m) (r p : ℝ) :
    (p + 1) * beta m r - p * beta m (r + 1) - beta m (r - p) =
      p * (p + 1) / ((m : ℝ) - 1) := by
  have hm1 := (cast_sub_one_pos hm).ne'
  unfold beta
  field_simp
  ring

/-- `β_0 = 0`. -/
@[simp] lemma beta_zero : beta m 0 = 0 := by simp [beta]

/-- `β_m = 0`. -/
@[simp] lemma beta_self : beta m m = 0 := by simp [beta]

/-- `β_1 = 1`. -/
lemma beta_one (hm : 2 ≤ m) : beta m 1 = 1 := by
  have hm1 := (cast_sub_one_pos hm).ne'
  unfold beta
  field_simp

/-- The profile is symmetric: `β_{m-z} = β_z`. -/
lemma beta_symm (z : ℝ) : beta m ((m : ℝ) - z) = beta m z := by
  unfold beta
  ring_nf

/-- `β_{m-1} = 1`. -/
lemma beta_pred (hm : 2 ≤ m) : beta m ((m : ℝ) - 1) = 1 := by
  rw [beta_symm, beta_one hm]

/-- `β_z ≥ 0` on `[0, m]`. -/
lemma beta_nonneg (hm : 2 ≤ m) {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ m) : 0 ≤ beta m z :=
  div_nonneg (mul_nonneg h0 (by linarith)) (cast_sub_one_pos hm).le

/-- `β_z > 0` on `(0, m)`. -/
lemma beta_pos (hm : 2 ≤ m) {z : ℝ} (h0 : 0 < z) (h1 : z < m) : 0 < beta m z :=
  div_pos (mul_pos h0 (by linarith)) (cast_sub_one_pos hm)

/-- `β_{|A|} ≥ 0` for every subset. -/
lemma beta_card_nonneg (hm : 2 ≤ m) (A : Finset (Fin m)) : 0 ≤ beta m A.card := by
  apply beta_nonneg hm (Nat.cast_nonneg _)
  have h := Finset.card_le_univ A
  rw [Fintype.card_fin] at h
  exact_mod_cast h

/-- `β_{|A|} > 0` for every proper nonempty subset. -/
lemma beta_card_pos (hm : 2 ≤ m) {A : Finset (Fin m)} (h1 : 1 ≤ A.card)
    (h2 : A.card ≤ m - 1) : 0 < beta m A.card := by
  apply beta_pos hm
  · exact_mod_cast h1
  · have : A.card < m := by omega
    exact_mod_cast this

/-- Scaled quadratic zero-sum permutohedron `P_m(B) = B · P_m` (paper §3). -/
def Pm (m : ℕ) (B : ℝ) : Set (Fin m → ℝ) := Psub (fun r => B * beta m r)

/-- Relative interior of `P_m(B)`: strict constraints on every proper nonempty
    subset (paper Remark 4.3). -/
def relintPm (m : ℕ) (B : ℝ) : Set (Fin m → ℝ) :=
  { q | (∑ i, q i) = 0 ∧ ∀ A : Finset (Fin m), 1 ≤ A.card → A.card ≤ m - 1 →
      -(B * beta m A.card) < ∑ i ∈ A, q i }

/-- Unfolded membership in `P_m(B)`. -/
lemma mem_Pm {B : ℝ} {q : Fin m → ℝ} :
    q ∈ Pm m B ↔ (∑ i, q i) = 0 ∧ ∀ A : Finset (Fin m),
      -(B * beta m A.card) ≤ ∑ i ∈ A, q i := Iff.rfl

/-- Constraints at `A = ∅` and `A = [m]` hold on the zero-sum hyperplane, so
    only proper nonempty subsets matter. -/
lemma mem_Pm_of_proper (hm : 2 ≤ m) {B : ℝ} {q : Fin m → ℝ} (hsum : (∑ i, q i) = 0)
    (h : ∀ A : Finset (Fin m), 1 ≤ A.card → A.card ≤ m - 1 →
      -(B * beta m A.card) ≤ ∑ i ∈ A, q i) : q ∈ Pm m B := by
  refine ⟨hsum, fun A => ?_⟩
  by_cases hA0 : A.card = 0
  · rw [Finset.card_eq_zero.mp hA0]
    simp
  · by_cases hAm : A.card = m
    · have hAu : A = univ := Finset.eq_univ_of_card A (by rw [Fintype.card_fin]; exact hAm)
      rw [hAu, hsum, Finset.card_univ, Fintype.card_fin]
      simp
    · have hle := Finset.card_le_univ A
      rw [Fintype.card_fin] at hle
      exact h A (by omega) (by omega)

/-- `relint P_m(B) ⊆ P_m(B)`. -/
lemma relintPm_subset (hm : 2 ≤ m) {B : ℝ} : relintPm m B ⊆ Pm m B :=
  fun _ hq => mem_Pm_of_proper hm hq.1 fun A h1 h2 => (hq.2 A h1 h2).le

/-- `P_m(B)` is nondecreasing in `B`. -/
lemma Pm_mono (hm : 2 ≤ m) {B B' : ℝ} (hBB : B ≤ B') : Pm m B ⊆ Pm m B' := by
  intro q hq
  refine ⟨hq.1, fun A => ?_⟩
  have h1 := hq.2 A
  have h2 := mul_le_mul_of_nonneg_right hBB (beta_card_nonneg hm A)
  simp only at h1 ⊢
  linarith

/-- `relint P_m(B)` is nondecreasing in `B`. -/
lemma relintPm_mono (hm : 2 ≤ m) {B B' : ℝ} (hBB : B ≤ B') :
    relintPm m B ⊆ relintPm m B' := by
  intro q hq
  refine ⟨hq.1, fun A h1 h2 => ?_⟩
  have h3 := hq.2 A h1 h2
  have h4 := mul_le_mul_of_nonneg_right hBB (beta_card_nonneg hm A)
  linarith

/-- `0 ∈ P_m(B)` for `B ≥ 0`. -/
lemma zero_mem_Pm (hm : 2 ≤ m) {B : ℝ} (hB : 0 ≤ B) : (0 : Fin m → ℝ) ∈ Pm m B := by
  refine ⟨by simp, fun A => ?_⟩
  have := mul_nonneg hB (beta_card_nonneg hm A)
  simp only [Pi.zero_apply, Finset.sum_const_zero]
  linarith

/-- `0 ∈ relint P_m(B)` for `B > 0`. -/
lemma zero_mem_relintPm (hm : 2 ≤ m) {B : ℝ} (hB : 0 < B) :
    (0 : Fin m → ℝ) ∈ relintPm m B := by
  refine ⟨by simp, fun A h1 h2 => ?_⟩
  have := mul_pos hB (beta_card_pos hm h1 h2)
  simp only [Pi.zero_apply, Finset.sum_const_zero]
  linarith

/-- On the zero-sum hyperplane, `q(Aᶜ) = -q(A)`. -/
lemma sum_compl_eq_neg {q : Fin m → ℝ} (hsum : (∑ i, q i) = 0) (A : Finset (Fin m)) :
    (∑ i ∈ Aᶜ, q i) = -∑ i ∈ A, q i := by
  have h := Finset.sum_add_sum_compl A q
  linarith

/-- `|Aᶜ| = m - |A|` as reals. -/
lemma card_compl_cast (A : Finset (Fin m)) :
    ((Aᶜ.card : ℕ) : ℝ) = (m : ℝ) - A.card := by
  have hle := Finset.card_le_univ A
  rw [Fintype.card_fin] at hle
  rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub hle]

/-- Upper bounds in `P_m(B)`: `q(A) ≤ B β_{|A|}`. -/
lemma sum_le_of_mem_Pm {B : ℝ} {q : Fin m → ℝ} (hq : q ∈ Pm m B)
    (A : Finset (Fin m)) : (∑ i ∈ A, q i) ≤ B * beta m A.card := by
  have h := hq.2 Aᶜ
  simp only at h
  rw [sum_compl_eq_neg hq.1, card_compl_cast, beta_symm] at h
  linarith

/-- Strict two-sided subset-sum bounds in `relint P_m(B)`:
    `|q(A)| < B β_{|A|}` for proper nonempty `A`. -/
lemma abs_sum_lt_of_mem_relintPm {B : ℝ} {q : Fin m → ℝ} (hq : q ∈ relintPm m B)
    {A : Finset (Fin m)} (h1 : 1 ≤ A.card) (h2 : A.card ≤ m - 1) :
    |∑ i ∈ A, q i| < B * beta m A.card := by
  have hle := Finset.card_le_univ A
  rw [Fintype.card_fin] at hle
  have hc : Aᶜ.card = m - A.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hlo := hq.2 A h1 h2
  have hhi := hq.2 Aᶜ (by omega) (by omega)
  rw [sum_compl_eq_neg hq.1, card_compl_cast, beta_symm] at hhi
  rw [abs_lt]
  constructor <;> linarith

/-- Coordinates of `P_m(B)` lie in `[-B, B]`. -/
lemma abs_le_of_mem_Pm (hm : 2 ≤ m) {B : ℝ} {q : Fin m → ℝ} (hq : q ∈ Pm m B)
    (i : Fin m) : |q i| ≤ B := by
  have hlo := hq.2 {i}
  have hhi := sum_le_of_mem_Pm hq {i}
  simp only [Finset.card_singleton, Finset.sum_singleton, Nat.cast_one,
    beta_one hm, mul_one] at hlo hhi
  rw [abs_le]
  exact ⟨hlo, hhi⟩

/-- Coordinates of `relint P_m(B)` lie in `(-B, B)`. -/
lemma abs_lt_of_mem_relintPm (hm : 2 ≤ m) {B : ℝ} {q : Fin m → ℝ}
    (hq : q ∈ relintPm m B) (i : Fin m) : |q i| < B := by
  have h := abs_sum_lt_of_mem_relintPm hq (A := {i}) (by simp) (by simp; omega)
  simpa [beta_one hm] using h

/-- `P_m ⊆ Q_m` (paper §3). -/
lemma Pm_subset_Qbox (hm : 2 ≤ m) : Pm m 1 ⊆ Qbox m :=
  fun _ hq => ⟨hq.1, abs_le_of_mem_Pm hm hq⟩

/-- For `m ≤ 3` every proper nonempty subset is a singleton or a co-singleton,
    so `Q_m ⊆ P_m`. -/
lemma Qbox_subset_Pm (hm : 2 ≤ m) (hm3 : m ≤ 3) : Qbox m ⊆ Pm m 1 := by
  intro q hq
  refine mem_Pm_of_proper hm hq.1 fun A h1 h2 => ?_
  have hle := Finset.card_le_univ A
  rw [Fintype.card_fin] at hle
  by_cases hA1 : A.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA1
    simp only [Finset.card_singleton, Nat.cast_one, beta_one hm, Finset.sum_singleton]
    linarith [(abs_le.mp (hq.2 a)).1]
  · have hc1 : Aᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
    have hsA := sum_compl_eq_neg hq.1 A
    rw [ha, Finset.sum_singleton] at hsA
    have hcard : (A.card : ℝ) = (m : ℝ) - 1 := by
      have : A.card = m - 1 := by omega
      rw [this, Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcard, beta_pred hm]
    linarith [(abs_le.mp (hq.2 a)).2]

/-- `P_2 = Q_2` and `P_3 = Q_3` (paper §3). -/
theorem Pm_eq_Qbox (hm : 2 ≤ m) (hm3 : m ≤ 3) : Pm m 1 = Qbox m :=
  Set.Subset.antisymm (Pm_subset_Qbox hm) (Qbox_subset_Pm hm hm3)

/-- `P_m ⊊ Q_m` for `m ≥ 4`: two coordinates at `-1` violate the pair
    constraint `β_2 = 2(m-2)/(m-1) < 2` (paper §3). -/
theorem Pm_ssubset_Qbox (hm : 4 ≤ m) : Pm m 1 ⊂ Qbox m := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Pm_subset_Qbox (by omega), fun heq => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  set q : Fin (n + 2) → ℝ := fun i => if (i : ℕ) < 2 then -1 else 2 / n with hqdef
  have hqQ : q ∈ Qbox (n + 2) := by
    refine ⟨?_, fun i => ?_⟩
    · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [hqdef, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one]
      simp only [show (0 : ℕ) < 2 from by norm_num, show (0 + 1 : ℕ) < 2 from by norm_num,
        if_true, show ∀ j : ℕ, ¬ (j + 1 + 1 < 2) from fun j => by omega, if_false,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    · simp only [hqdef]
      split_ifs
      · norm_num
      · rw [abs_le]
        constructor
        · have : 0 ≤ 2 / (n : ℝ) := by positivity
          linarith
        · rw [div_le_one (by linarith)]
          exact hn
  rw [← heq] at hqQ
  have h := hqQ.2 {0, 1}
  rw [Finset.sum_pair zero_ne_one] at h
  simp only [hqdef, Fin.val_zero, Fin.val_one, show (0 : ℕ) < 2 from by norm_num,
    show (1 : ℕ) < 2 from by norm_num, if_true] at h
  rw [Finset.card_pair zero_ne_one] at h
  unfold beta at h
  push_cast at h
  rw [show ((n : ℝ) + 2 - 1) = n + 1 by ring] at h
  have hpos : (0 : ℝ) < n + 1 := by linarith
  rw [show ((n : ℝ) + 2 - 2) = n by ring, one_mul] at h
  have hlt : 2 * (n : ℝ) / (n + 1) < 2 := by
    rw [div_lt_iff₀ hpos]
    linarith
  linarith

/-- Vertex `v*_r = (2r - m - 1)/(m - 1)` of the permutohedron (paper §3). -/
noncomputable def vstar (m : ℕ) (r : ℕ) : ℝ := (2 * (r : ℝ) - m - 1) / ((m : ℝ) - 1)

/-- Partial sums of `v*` trace the profile: `∑_{r ≤ k} v*_r = -β_k` (paper §3). -/
lemma sum_vstar (hm : 2 ≤ m) (k : ℕ) :
    (∑ r ∈ Finset.Icc 1 k, vstar m r) = -beta m k := by
  have hm1 := (cast_sub_one_pos hm).ne'
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    unfold vstar beta
    push_cast
    field_simp
    ring

end Carpooling

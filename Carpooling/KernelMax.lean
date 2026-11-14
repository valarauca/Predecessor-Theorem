import Carpooling.Permutohedron

/-!
  Maximal-kernel uniqueness for universal controlled invariance
  (carpooling paper Theorem 4.4(b), (c)).

  The proof maximizes the rearrangement potential
  `F_w(q) = max_σ ∑_j w_j q_{σ(j)}` over the closure of an invariant set.
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- Rearrangement potential `F_w(q) = max_σ ∑_j w_j q_{σ(j)}` (paper Theorem 4.4 proof). -/
noncomputable def Fw (w q : Fin m → ℝ) : ℝ :=
  (univ : Finset (Equiv.Perm (Fin m))).sup' univ_nonempty fun σ => ∑ j, w j * q (σ j)

/-- Every rearranged pairing is bounded by `F_w`. -/
lemma le_Fw (w q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : (∑ j, w j * q (σ j)) ≤ Fw w q :=
  Finset.le_sup' (fun σ : Equiv.Perm (Fin m) => ∑ j, w j * q (σ j)) (mem_univ σ)

/-- Some permutation attains `F_w`. -/
lemma exists_Fw_eq (w q : Fin m → ℝ) :
    ∃ π : Equiv.Perm (Fin m), Fw w q = ∑ j, w j * q (π j) := by
  obtain ⟨π, -, hπ⟩ := Finset.exists_mem_eq_sup' univ_nonempty
    (fun σ : Equiv.Perm (Fin m) => ∑ j, w j * q (σ j))
  exact ⟨π, hπ⟩

/-- `F_w` is continuous. -/
lemma continuous_Fw (w : Fin m → ℝ) : Continuous (Fw w) :=
  Continuous.finset_sup'_apply univ_nonempty fun σ _ =>
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply (σ j))

/-- Two sums over `Fin m` that agree off `{a, b}` differ by the two boundary terms. -/
lemma sum_sub_sum_two {f g : Fin m → ℝ} {a b : Fin m} (hab : a ≠ b)
    (h : ∀ j, j ≠ a → j ≠ b → f j = g j) :
    (∑ j, f j) - ∑ j, g j = (f a - g a) + (f b - g b) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_eq_add a b hab (fun c _ hc => by rw [h c hc.1 hc.2, sub_self])
    (by simp) (by simp)

/-- For strictly increasing `w`, a permutation attaining `F_w(q)` lists `q` in
    nondecreasing order. -/
lemma argmax_sorted {w q : Fin m → ℝ} (hw : StrictMono w) {π : Equiv.Perm (Fin m)}
    (hπ : Fw w q = ∑ j, w j * q (π j)) {a b : Fin m} (hab : a < b) :
    q (π a) ≤ q (π b) := by
  by_contra h
  push Not at h
  have h1 := le_Fw w q ((Equiv.swap a b).trans π)
  have h2 := sum_sub_sum_two (f := fun j => w j * q (((Equiv.swap a b).trans π) j))
    (g := fun j => w j * q (π j)) hab.ne (fun j hja hjb => by
      simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hja hjb])
  simp only [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1 h2
  have hpos : 0 < (w b - w a) * (q (π a) - q (π b)) :=
    mul_pos (sub_pos.mpr (hw hab)) (sub_pos.mpr h)
  linarith

/-- `Q_m` is closed. -/
lemma isClosed_Qbox : IsClosed (Qbox m) := by
  have h : Qbox m = {q : Fin m → ℝ | (∑ i, q i) = 0} ∩ ⋂ i, {q | |q i| ≤ 1} := by
    ext q
    simp [Qbox]
  rw [h]
  exact (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i)
    continuous_const).inter
    (isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const)

/-- `Q_m` lies in the closed unit ball of the sup norm. -/
lemma Qbox_subset_closedBall : Qbox m ⊆ Metric.closedBall (0 : Fin m → ℝ) 1 := by
  intro q hq
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  exact hq.2 i

/-- A step is a continuous map of the state. -/
lemma continuous_step (d : ℝ) (x : Fin m → ℝ) (k : Fin m) : Continuous (step d x k) :=
  continuous_pi fun i => (continuous_apply i).add continuous_const

/-- The closure of a one-step controlled invariant set is one-step controlled
    invariant (paper Theorem 4.4 proof). -/
lemma closure_invariant {d : ℝ} {x : Fin m → ℝ} {K : Set (Fin m → ℝ)}
    (h : ∀ q ∈ K, ∃ k ∈ supp x, step d x k q ∈ K) :
    ∀ q ∈ closure K, ∃ k ∈ supp x, step d x k q ∈ closure K := by
  intro q hq
  by_contra hno
  push Not at hno
  have hVo : IsOpen (⋂ k ∈ supp x, step d x k ⁻¹' (closure K)ᶜ) :=
    isOpen_biInter_finset fun k _ =>
      isClosed_closure.isOpen_compl.preimage (continuous_step d x k)
  have hqV : q ∈ ⋂ k ∈ supp x, step d x k ⁻¹' (closure K)ᶜ := by
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
    exact hno
  obtain ⟨q', hq'V, hq'K⟩ := mem_closure_iff.mp hq _ hVo hqV
  obtain ⟨k, hk, hkK⟩ := h q' hq'K
  exact (Set.mem_iInter₂.mp hq'V k hk) (subset_closure hkK)

/-- At a maximizer of `F_w` over an invariant set, positions `a < b` along the
    attaining permutation are separated by at least `d (1 - η)`, tested with
    the generator `η e_{π a} + (1 - η) e_{π b}` (paper Theorem 4.4 proof). -/
lemma gap_ge_aux {d : ℝ} (hd : 0 < d) {L : Set (Fin m → ℝ)}
    (hinvL : ∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 → 2 ≤ suppCard x →
      ∀ q ∈ L, ∃ k ∈ supp x, step d x k q ∈ L)
    {w : Fin m → ℝ} (hw : StrictMono w) {q : Fin m → ℝ} (hqL : q ∈ L)
    (hmax : IsMaxOn (Fw w) L q) {π : Equiv.Perm (Fin m)}
    (hπ : Fw w q = ∑ j, w j * q (π j)) {a b : Fin m} (hab : a < b)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    d * (1 - η) ≤ q (π b) - q (π a) := by
  have hi : π a ≠ π b := π.injective.ne hab.ne
  have hwab : 0 < w b - w a := sub_pos.mpr (hw hab)
  set x : Fin m → ℝ := fun i => if i = π a then η else if i = π b then 1 - η else 0
    with hxdef
  have hxa : x (π a) = η := by simp [hxdef]
  have hxb : x (π b) = 1 - η := by simp [hxdef, hi.symm]
  have hxo : ∀ i, i ≠ π a → i ≠ π b → x i = 0 := fun i h1 h2 => by simp [hxdef, h1, h2]
  have hx0 : ∀ i, 0 ≤ x i := by
    intro i
    by_cases h1 : i = π a
    · rw [h1, hxa]
      exact hη0.le
    · by_cases h2 : i = π b
      · rw [h2, hxb]
        linarith
      · rw [hxo i h1 h2]
  have hx1 : (∑ i, x i) = 1 := by
    rw [Finset.sum_eq_add (π a) (π b) hi (fun c _ hc => hxo c hc.1 hc.2) (by simp) (by simp),
      hxa, hxb]
    ring
  have hsupp : supp x = {π a, π b} := by
    ext i
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases h1 : i = π a
    · rw [h1, hxa]
      simp [hη0.ne']
    · by_cases h2 : i = π b
      · rw [h2, hxb]
        simp [sub_ne_zero.mpr hη1.ne']
      · rw [hxo i h1 h2]
        simp [h1, h2]
  have hs : 2 ≤ suppCard x := by
    unfold suppCard
    rw [hsupp, Finset.card_pair hi]
  obtain ⟨k, hk, hkL⟩ := hinvL x hx0 hx1 hs q hqL
  have hle : Fw w (step d x k q) ≤ Fw w q := isMaxOn_iff.mp hmax _ hkL
  rw [hsupp, Finset.mem_insert, Finset.mem_singleton] at hk
  have hoff : ∀ j, j ≠ a → j ≠ b → step d x k q (π j) = q (π j) := by
    intro j hja hjb
    have h1 : π j ≠ π a := π.injective.ne hja
    have h2 : π j ≠ π b := π.injective.ne hjb
    have h3 : π j ≠ k := by
      rcases hk with rfl | rfl <;> assumption
    simp only [step]
    rw [if_neg h3, hxo _ h1 h2]
    ring
  rcases hk with rfl | rfl
  · have hsa : step d x (π a) q (π a) = q (π a) + d * (1 - η) := by
      simp only [step, ↓reduceIte, hxa]
    have hsb : step d x (π a) q (π b) = q (π b) - d * (1 - η) := by
      simp only [step]
      rw [if_neg hi.symm, hxb]
      ring
    have h1 := le_Fw w (step d x (π a) q) ((Equiv.swap a b).trans π)
    have h2 := sum_sub_sum_two
      (f := fun j => w j * step d x (π a) q (((Equiv.swap a b).trans π) j))
      (g := fun j => w j * q (π j)) hab.ne (fun j hja hjb => by
        simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hja hjb, hoff j hja hjb])
    simp only [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1 h2
    rw [hsa, hsb] at h2
    by_contra hcon
    push Not at hcon
    have hpos : 0 < (w b - w a) * (d * (1 - η) - (q (π b) - q (π a))) :=
      mul_pos hwab (by linarith)
    linarith
  · have hsa : step d x (π b) q (π a) = q (π a) - d * η := by
      simp only [step]
      rw [if_neg hi, hxa]
      ring
    have hsb : step d x (π b) q (π b) = q (π b) + d * η := by
      simp only [step, ↓reduceIte, hxb]
      ring
    have h1 := le_Fw w (step d x (π b) q) π
    have h2 := sum_sub_sum_two (f := fun j => w j * step d x (π b) q (π j))
      (g := fun j => w j * q (π j)) hab.ne (fun j hja hjb => by
        simp only [hoff j hja hjb])
    rw [hsa, hsb] at h2
    exfalso
    have hpos : 0 < (w b - w a) * (d * η) := mul_pos hwab (mul_pos hd hη0)
    linarith

/-- At a maximizer of `F_w` over an invariant set, positions `a < b` along the
    attaining permutation are separated by at least `d` (paper Theorem 4.4 proof). -/
lemma gap_ge {d : ℝ} (hd : 0 < d) {L : Set (Fin m → ℝ)}
    (hinvL : ∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 → 2 ≤ suppCard x →
      ∀ q ∈ L, ∃ k ∈ supp x, step d x k q ∈ L)
    {w : Fin m → ℝ} (hw : StrictMono w) {q : Fin m → ℝ} (hqL : q ∈ L)
    (hmax : IsMaxOn (Fw w) L q) {π : Equiv.Perm (Fin m)}
    (hπ : Fw w q = ∑ j, w j * q (π j)) {a b : Fin m} (hab : a < b) :
    d ≤ q (π b) - q (π a) := by
  by_contra hlt
  push Not at hlt
  have hg0 : 0 ≤ q (π b) - q (π a) := sub_nonneg.mpr (argmax_sorted hw hπ hab)
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (d - (q (π b) - q (π a))) / (2 * d) := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := hd.ne'
  have hη0 : 0 < η := by
    rw [hηdef]
    exact div_pos (by linarith) (by linarith)
  have hη1 : η < 1 := by
    rw [hηdef, div_lt_one (by linarith)]
    linarith
  have hdη : d * η = (d - (q (π b) - q (π a))) / 2 := by
    rw [hηdef]
    field_simp
  have h := gap_ge_aux hd hinvL hw hqL hmax hπ hab hη0 hη1
  linarith

/-- Coordinates of `q` read along a permutation, padded by `0` past `m`. -/
noncomputable def along (q : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (n : ℕ) : ℝ :=
  if h : n < m then q (π ⟨n, h⟩) else 0

/-- `along` agrees with `q ∘ π` on `Fin m`. -/
lemma along_val (q : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (j : Fin m) :
    along q π j = q (π j) := by
  simp [along, j.isLt]

/-- Consecutive gaps of at least `d` accumulate: `a_{r+n} - a_r ≥ n d`. -/
lemma chain_ge {a : ℕ → ℝ} {d : ℝ} (h : ∀ n, n + 1 < m → d ≤ a (n + 1) - a n) :
    ∀ n r, r + n < m → (n : ℝ) * d ≤ a (r + n) - a r := by
  intro n
  induction n with
  | zero =>
    intro r _
    simp
  | succ n ih =>
    intro r hr
    have h1 := ih r (by omega)
    have h2 := h (r + n) (by omega)
    rw [show r + (n + 1) = r + n + 1 by omega]
    push_cast
    linarith

/-- An invariant subset of `Q_m` has a maximizer of `F_w` on its closure whose
    sorted coordinates have consecutive gaps at least `d` (paper Theorem 4.4 proof). -/
lemma exists_sorted_maximizer {d : ℝ} (hd : 0 < d) {K : Set (Fin m → ℝ)}
    (hKQ : K ⊆ Qbox m)
    (hinv : ∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 → 2 ≤ suppCard x →
      pred d x K = K)
    (hne : K.Nonempty) {w : Fin m → ℝ} (hw : StrictMono w) :
    ∃ q ∈ closure K, IsMaxOn (Fw w) (closure K) q ∧ ∃ π : Equiv.Perm (Fin m),
      Fw w q = ∑ j, w j * q (π j) ∧
      ∀ n, n + 1 < m → d ≤ along q π (n + 1) - along q π n := by
  have hLQ : closure K ⊆ Qbox m := closure_minimal hKQ isClosed_Qbox
  have hLc : IsCompact (closure K) :=
    (isCompact_closedBall (0 : Fin m → ℝ) 1).of_isClosed_subset isClosed_closure
      (hLQ.trans Qbox_subset_closedBall)
  have hinvL : ∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 → 2 ≤ suppCard x →
      ∀ q ∈ closure K, ∃ k ∈ supp x, step d x k q ∈ closure K :=
    fun x h0 h1 hs => closure_invariant (pred_eq_self_iff.mp (hinv x h0 h1 hs))
  obtain ⟨q, hqL, hmax⟩ := hLc.exists_isMaxOn hne.closure (continuous_Fw w).continuousOn
  obtain ⟨π, hπ⟩ := exists_Fw_eq w q
  refine ⟨q, hqL, hmax, π, hπ, fun n hn => ?_⟩
  have h := gap_ge hd hinvL hw hqL hmax hπ (a := ⟨n, by omega⟩) (b := ⟨n + 1, hn⟩)
    (by simp [Fin.lt_def])
  have e1 : along q π (n + 1) = q (π ⟨n + 1, hn⟩) := by simp [along, hn]
  have e0 : along q π n = q (π ⟨n, by omega⟩) := by
    simp [along, show n < m by omega]
  rw [e1, e0]
  exact h

/-- `along` stays in `[-1, 1]` for states of `Q_m`. -/
lemma abs_along_le {q : Fin m → ℝ} (hq : q ∈ Qbox m) (π : Equiv.Perm (Fin m)) (n : ℕ) :
    |along q π n| ≤ 1 := by
  unfold along
  split_ifs
  · exact hq.2 _
  · simp

/-- **Theorem 4.4(b)**: if a nonempty `K ⊆ Q_m` is one-step controlled invariant
    for every nontrivial generator of demand `d > 0`, then `d ≤ 2 / (m - 1)`. -/
theorem kernel_demand_le (hm : 2 ≤ m) {d : ℝ} (hd : 0 < d) {K : Set (Fin m → ℝ)}
    (hKQ : K ⊆ Qbox m)
    (hinv : ∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 → 2 ≤ suppCard x →
      pred d x K = K)
    (hne : K.Nonempty) : d ≤ 2 / ((m : ℝ) - 1) := by
  have hw : StrictMono (fun j : Fin m => (j : ℝ)) := fun i j hij => by
    have h : (i : ℕ) < j := hij
    dsimp only
    exact_mod_cast h
  obtain ⟨q, hqL, -, π, -, hgap⟩ := exists_sorted_maximizer hd hKQ hinv hne hw
  have hqQ : q ∈ Qbox m := closure_minimal hKQ isClosed_Qbox hqL
  have hc := chain_ge hgap (m - 1) 0 (by omega)
  rw [zero_add] at hc
  have h1 := abs_le.mp (abs_along_le hqQ π (m - 1))
  have h0 := abs_le.mp (abs_along_le hqQ π 0)
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast] at hc
  rw [le_div_iff₀ (cast_sub_one_pos hm)]
  linarith

/-- Gauss sum over the reals: `∑_{n < k} n = k (k - 1) / 2`. -/
lemma sum_range_cast_id (k : ℕ) : (∑ n ∈ Finset.range k, (n : ℝ)) = k * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- At `d = 2 / (m - 1)` the sorted maximizer of `F_w` is the vertex
    `-1 + j d`, so `F_w(q) ≤ ∑_j w_j (-1 + j d)` on `K` (paper Theorem 4.4(c) proof). -/
lemma kernel_Fw_le (hm : 2 ≤ m) {d : ℝ} (hd : d = 2 / ((m : ℝ) - 1))
    {K : Set (Fin m → ℝ)} (hKQ : K ⊆ Qbox m)
    (hinv : ∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 → 2 ≤ suppCard x →
      pred d x K = K)
    {w : Fin m → ℝ} (hw : StrictMono w) {q0 : Fin m → ℝ} (hq0 : q0 ∈ K) :
    Fw w q0 ≤ ∑ j : Fin m, w j * (-1 + (j : ℝ) * d) := by
  have hm1 := cast_sub_one_pos hm
  have hdpos : 0 < d := by
    rw [hd]
    exact div_pos two_pos hm1
  have hdm : ((m : ℝ) - 1) * d = 2 := by
    rw [hd]
    field_simp
  obtain ⟨q, hqL, hmax, π, hπ, hgap⟩ := exists_sorted_maximizer hdpos hKQ hinv ⟨q0, hq0⟩ hw
  have hqQ : q ∈ Qbox m := closure_minimal hKQ isClosed_Qbox hqL
  have hc := chain_ge hgap
  have hval : ∀ n, n < m → along q π n = along q π 0 + n * d := by
    intro n hn
    have h1 := hc n 0 (by omega)
    have h2 := hc (m - 1 - n) n (by omega)
    rw [zero_add] at h1
    rw [show n + (m - 1 - n) = m - 1 by omega] at h2
    have hcast : ((m - 1 - n : ℕ) : ℝ) = (m : ℝ) - 1 - n := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast] at h2
    have hb1 := abs_le.mp (abs_along_le hqQ π (m - 1))
    have hb0 := abs_le.mp (abs_along_le hqQ π 0)
    apply le_antisymm
    · linarith
    · linarith
  have hsum0 : (∑ n ∈ Finset.range m, along q π n) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [along_val]
    rw [Equiv.sum_comp π q]
    exact hqQ.1
  have hsum1 : (∑ n ∈ Finset.range m, along q π n) = m * along q π 0 + m := by
    rw [Finset.sum_congr rfl fun n hn => hval n (Finset.mem_range.mp hn),
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_mul, sum_range_cast_id]
    have : (m : ℝ) * ((m : ℝ) - 1) / 2 * d = m * (((m : ℝ) - 1) * d) / 2 := by ring
    rw [this, hdm]
    ring
  have ha0 : along q π 0 = -1 := by
    have hm0 : (0 : ℝ) < m := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hprod : (m : ℝ) * (along q π 0 + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  calc Fw w q0 ≤ Fw w q := isMaxOn_iff.mp hmax _ (subset_closure hq0)
    _ = ∑ j, w j * q (π j) := hπ
    _ = ∑ j : Fin m, w j * (-1 + (j : ℝ) * d) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show q (π j) = along q π j from (along_val q π j).symm, hval j j.isLt, ha0]

/-- Some permutation sends exactly the first `|A|` positions into `A`. -/
lemma exists_perm_prefix (A : Finset (Fin m)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ j, σ j ∈ A ↔ (j : ℕ) < A.card := by
  have hle := Finset.card_le_univ A
  rw [Fintype.card_fin] at hle
  have hcard : Fintype.card {j : Fin m // (j : ℕ) < A.card} =
      Fintype.card {i : Fin m // i ∈ A} := by
    rw [Fintype.card_subtype, Fin.card_filter_val_lt, Fintype.card_coe]
    exact min_eq_right hle
  let e := Fintype.equivOfCardEq hcard
  refine ⟨Equiv.extendSubtype e, fun j => ?_⟩
  by_cases hj : (j : ℕ) < A.card
  · exact ⟨fun _ => hj, fun _ => Equiv.extendSubtype_mem e j hj⟩
  · exact ⟨fun h => absurd h (Equiv.extendSubtype_not_mem e j hj), fun h => absurd h hj⟩

/-- If `t ≤ δ c` for every `δ > 0`, then `t ≤ 0`. -/
lemma nonpos_of_forall_pos_le_mul {t c : ℝ} (h : ∀ δ : ℝ, 0 < δ → t ≤ δ * c) : t ≤ 0 := by
  by_contra ht
  push Not at ht
  rcases le_or_gt c 0 with hc | hc
  · have := h 1 one_pos
    linarith
  · have h1 := h (t / (2 * c)) (by positivity)
    have h2 : t / (2 * c) * c = t / 2 := by
      field_simp
    linarith

/-- **Theorem 4.4(c)**: at `d = 2 / (m - 1)`, every `K ⊆ Q_m` that is one-step
    controlled invariant for all nontrivial generators satisfies `K ⊆ P_m`;
    with Theorem 4.4(a), `P_m` is the unique maximal such set. -/
theorem kernel_subset_Pm (hm : 2 ≤ m) {d : ℝ} (hd : d = 2 / ((m : ℝ) - 1))
    {K : Set (Fin m → ℝ)} (hKQ : K ⊆ Qbox m)
    (hinv : ∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 → 2 ≤ suppCard x →
      pred d x K = K) : K ⊆ Pm m 1 := by
  intro q0 hq0
  have hm1 := cast_sub_one_pos hm
  refine ⟨(hKQ hq0).1, fun A => ?_⟩
  simp only [one_mul]
  obtain ⟨σ, hσ⟩ := exists_perm_prefix A
  have hum : A.card ≤ m := by
    have h := Finset.card_le_univ A
    rwa [Fintype.card_fin] at h
  have hA : (∑ j : Fin m, if (j : ℕ) < A.card then q0 (σ j) else 0) = ∑ i ∈ A, q0 i := by
    have h1 : ∀ j : Fin m, (if (j : ℕ) < A.card then q0 (σ j) else 0) =
        if σ j ∈ A then q0 (σ j) else 0 := by
      intro j
      by_cases h : (j : ℕ) < A.card
      · rw [if_pos h, if_pos ((hσ j).mpr h)]
      · rw [if_neg h, if_neg (fun h' => h ((hσ j).mp h'))]
    rw [Finset.sum_congr rfl fun j _ => h1 j,
      Equiv.sum_comp σ (fun i => if i ∈ A then q0 i else 0), Finset.sum_ite_mem,
      Finset.univ_inter]
  have hB : (∑ j : Fin m, if (j : ℕ) < A.card then -1 + (j : ℝ) * d else 0) =
      -beta m A.card := by
    rw [Fin.sum_univ_eq_sum_range (fun n => if n < A.card then -1 + (n : ℝ) * d else 0) m,
      Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfil : (Finset.range m).filter (fun n => n < A.card) = Finset.range A.card := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfil, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_mul, sum_range_cast_id, hd]
    unfold beta
    field_simp
    ring
  have key : ∀ δ : ℝ, 0 < δ → -beta m A.card - ∑ i ∈ A, q0 i ≤
      δ * ((∑ j : Fin m, (j : ℝ) * (-1 + (j : ℝ) * d)) - ∑ j : Fin m, (j : ℝ) * q0 (σ j)) := by
    intro δ hδ
    set w : Fin m → ℝ := fun j => δ * (j : ℝ) - if (j : ℕ) < A.card then 1 else 0 with hwdef
    have hw : StrictMono w := by
      intro i j hij
      have hij' : (i : ℕ) < j := hij
      have hc : (i : ℝ) < j := by exact_mod_cast hij'
      have hδc : δ * (i : ℝ) < δ * j := mul_lt_mul_of_pos_left hc hδ
      simp only [hwdef]
      split_ifs with h1 h2 h2
      · linarith
      · linarith
      · exact absurd (lt_trans hij' h2) h1
      · linarith
    have hsplit : ∀ v : Fin m → ℝ, (∑ j, w j * v j) =
        δ * (∑ j : Fin m, (j : ℝ) * v j) - ∑ j : Fin m, if (j : ℕ) < A.card then v j else 0 := by
      intro v
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hwdef]
      split_ifs <;> ring
    have e1 := hsplit (fun j => q0 (σ j))
    have e2 := hsplit (fun j => -1 + (j : ℝ) * d)
    try simp only at e1 e2
    rw [hA] at e1
    rw [hB] at e2
    have h1 := le_Fw w q0 σ
    have h2 := kernel_Fw_le hm hd hKQ hinv hw hq0
    linarith
  have := nonpos_of_forall_pos_le_mul key
  linarith

end Carpooling

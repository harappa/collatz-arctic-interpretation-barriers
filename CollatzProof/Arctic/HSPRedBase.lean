/-
Ingredients of the reduction of the hypothesis `HSP` to the expected-value hypothesis `MinRate`. The main theorem is in `HSPRed.lean`.
Finite forms of the superadditivity of the smallest entries and of the equivalence ("the almost-sure statement for all classes" ⟺ "all finite
entries of `D_w` are at least `Λ_C t - o(t)`"); these are the facts (F1)–(F3) of Appendix B.1.

* **Smallest finite entry** `minCap c P`: the smallest finite entry of the matrix `P`, capped at `c` (it is `c` if there is no finite entry).
  Characterization `hsp_le_minCap`; **superadditivity** `hsp_minCap_mul`: `minCap c₁ P + minCap c₂ Q ≤ minCap (c₁ + c₂) (P Q)`
  (a finite entry of a product is the sum of two finite entries along a single path; (F1)).
* On words, `fmin A C w := minCap (digMax A · |w|) (ev (restrictI C A) w)` (`digMax A` is the largest finite entry of the digit letters) and
  its average `avgMinCap`. `fmin` is superadditive (`hsp_fmin_append`, (F1)), and finite values of `rowVal` are at least `fmin` (`hsp_fmin_le_rowVal`, (F2)).
* **Law of large numbers for independent blocks** ((F3)): the sum `blockSum` over the blocks of length `K` of a uniform word of length `nK + r` (the rest is discarded).
  By the concatenation bijection `hsp_sum_append`, the second moment of the block sum is at most `n 2^(nK+r) B` (`hsp_var_blockSum`; the cross terms vanish),
  and Chebyshev's inequality for counting follows (`hsp_cheb_blockSum`). Superadditivity gives `blockSum ≤ fmin` (`hsp_blockSum_le_fmin`).
* Auxiliary: decomposition of finite entries of products `hsp_mul_eq_fin`, the upper bound for digit words `hsp_fmax_le_digits` (`fmax(w) ≤ digMax · |w|`), etc.
-/
import CollatzProof.Arctic.CoreHyp
import CollatzProof.Arctic.RateUpper
import CollatzProof.Arctic.WindowLLN2
import CollatzProof.Arctic.ConfigLemmas

namespace Collatz.Arctic

open Arc

/-! ### The capped smallest entry -/

/-- An arctic value capped at `c` (`-∞` is read as `c`). -/
def capVal (c : ℕ) (a : Arc) : ℕ := min c ((Arc.val a).unbotD c)

/-- The smallest finite entry of a matrix, capped at `c` (`c` if there is no finite entry). -/
def minCap {D : ℕ} (c : ℕ) (P : AMat D) : ℕ :=
  (Finset.univ : Finset (Fin D × Fin D)).fold min c (fun ij => capVal c (P ij.1 ij.2))

lemma hsp_fin_inj {n v : ℕ} (h : fin n = fin v) : n = v := by
  have := congrArg val h
  simpa using this

lemma hsp_ne_zero_iff_fin {a : Arc} : a ≠ 0 ↔ ∃ v, a = fin v := by
  rw [Arc.ne_zero_iff_val, val_ne_bot_iff]

/-- A finite entry of a product is the sum of two finite entries along a single path. -/
lemma hsp_mul_eq_fin {D : ℕ} {P Q : AMat D} {i j : Fin D} {v : ℕ} (h : (P * Q) i j = fin v) :
    ∃ k a b, P i k = fin a ∧ Q k j = fin b ∧ a + b = v := by
  have hne : (Finset.univ : Finset (Fin D)).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨k, -, hk⟩ := exists_eq_sum hne (fun k => P i k * Q k j)
  rw [Matrix.mul_apply] at h
  rw [h] at hk
  have hfin : val (P i k * Q k j) ≠ ⊥ := by rw [hk]; simp
  obtain ⟨a, ha⟩ := (val_ne_bot_iff _).mp (ne_bot_left hfin)
  obtain ⟨b, hb⟩ := (val_ne_bot_iff _).mp (ne_bot_right hfin)
  rw [ha, hb, fin_mul_fin] at hk
  exact ⟨k, a, b, ha, hb, hsp_fin_inj hk⟩

lemma hsp_le_mul_apply {D : ℕ} (P Q : AMat D) (i k j : Fin D) : P i k * Q k j ≤ (P * Q) i j := by
  rw [Matrix.mul_apply]
  exact le_sum_of_mem (s := Finset.univ) (fun k => P i k * Q k j) (Finset.mem_univ k)

/-- The largest entry of a matrix is one of its entries (`D > 0`). -/
lemma hsp_maxEnt_eq {D : ℕ} (P : AMat D) (i : Fin D) : ∃ i₀ j₀, maxEnt P = P i₀ j₀ := by
  have hne : (Finset.univ : Finset (Fin D)).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨i₀, -, h₀⟩ := exists_eq_sum hne (fun i => ∑ j, P i j)
  obtain ⟨j₀, -, h₁⟩ := exists_eq_sum hne (fun j => P i₀ j)
  exact ⟨i₀, j₀, by rw [maxEnt, ← h₀, ← h₁]⟩

lemma hsp_le_capVal {m c : ℕ} {a : Arc} : m ≤ capVal c a ↔ m ≤ c ∧ ∀ v, a = fin v → m ≤ v := by
  unfold capVal
  rw [le_min_iff]
  by_cases hb : val a = ⊥
  · rw [hb, WithBot.unbotD_bot]
    constructor
    · rintro ⟨h, -⟩
      refine ⟨h, fun v hv => ?_⟩
      rw [hv, val_fin] at hb
      exact absurd hb (WithBot.coe_ne_bot)
    · rintro ⟨h, -⟩
      exact ⟨h, h⟩
  · obtain ⟨n, rfl⟩ := (val_ne_bot_iff a).mp hb
    change m ≤ c ∧ m ≤ n ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun v hv => hsp_fin_inj hv ▸ h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 n rfl⟩

/-- Characterization of `minCap`: `m ≤ minCap c P` iff `m ≤ c` and every finite entry of `P` is at least `m`. -/
lemma hsp_le_minCap {D : ℕ} {m c : ℕ} {P : AMat D} :
    m ≤ minCap c P ↔ m ≤ c ∧ ∀ i j v, P i j = fin v → m ≤ v := by
  unfold minCap
  rw [Finset.le_fold_min]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j v hv => (hsp_le_capVal.mp (h2 (i, j) (Finset.mem_univ _))).2 v hv⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ij _ => hsp_le_capVal.mpr ⟨h1, fun v hv => h2 ij.1 ij.2 v hv⟩⟩

lemma hsp_minCap_le_cap {D : ℕ} (c : ℕ) (P : AMat D) : minCap c P ≤ c :=
  (hsp_le_minCap.mp le_rfl).1

lemma hsp_minCap_le_of {D : ℕ} {c : ℕ} {P : AMat D} {i j : Fin D} {v : ℕ} (h : P i j = fin v) :
    minCap c P ≤ v :=
  (hsp_le_minCap.mp le_rfl).2 i j v h

/-- **Superadditivity**: since a finite entry of a product is the sum of two finite entries along a single path,
`minCap c₁ P + minCap c₂ Q ≤ minCap (c₁ + c₂) (P Q)`. -/
theorem hsp_minCap_mul {D : ℕ} (c₁ c₂ : ℕ) (P Q : AMat D) :
    minCap c₁ P + minCap c₂ Q ≤ minCap (c₁ + c₂) (P * Q) := by
  rw [hsp_le_minCap]
  refine ⟨add_le_add (hsp_minCap_le_cap _ _) (hsp_minCap_le_cap _ _), fun i j v hv => ?_⟩
  obtain ⟨k, a, b, ha, hb, hab⟩ := hsp_mul_eq_fin hv
  have h1 := hsp_minCap_le_of (c := c₁) ha
  have h2 := hsp_minCap_le_of (c := c₂) hb
  omega

/-! ### The smallest entry over a word -/

/-- The largest finite entry of the matrices of the digit letters (`f`, `t`) (`-∞` read as 0). -/
def digMax {D : ℕ} (A : Interp D) : ℕ :=
  (Finset.univ : Finset (Fin D × Fin D)).sup
    (fun ij => max (natOr0 (A Letter.f ij.1 ij.2)) (natOr0 (A Letter.t ij.1 ij.2)))

/-- The smallest finite entry of the product restricted to `C` along the word `w` (capped at `digMax A · |w|`). -/
def fmin {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (w : Word) : ℕ :=
  minCap (digMax A * w.length) (ev (restrictI C A) w)

/-- The average of `fmin` over uniform words of length `K`. -/
def avgMinCap {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (K : ℕ) : ℚ :=
  (∑ w ∈ wordsOfLen K, (fmin A C w : ℚ)) / 2 ^ K

/-- Superadditivity of `fmin`: `fmin(u) + fmin(v) ≤ fmin(uv)`. -/
theorem hsp_fmin_append {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (u v : Word) :
    fmin A C u + fmin A C v ≤ fmin A C (u ++ v) := by
  unfold fmin
  rw [ev_append, List.length_append, Nat.mul_add]
  exact hsp_minCap_mul _ _ _ _

lemma hsp_fmin_le {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (w : Word) :
    fmin A C w ≤ digMax A * w.length :=
  hsp_minCap_le_cap _ _

/-- `fmin` is at most the value of any finite entry (with arbitrary start and end indices). -/
lemma hsp_fmin_le_of {D : ℕ} {A : Interp D} {C : Finset (Fin D)} {w : Word} {i j : Fin D} {v : ℕ}
    (h : ev (restrictI C A) w i j = fin v) : fmin A C w ≤ v :=
  hsp_minCap_le_of h

/-- Finite values of `rowVal` are at least `fmin` (the entry at a starting index attaining the maximum is finite). -/
lemma hsp_fmin_le_rowVal {D : ℕ} {A : Interp D} {C S : Finset (Fin D)} {w : Word} {j : Fin D}
    {v : ℕ} (h : rowVal A C S w j = fin v) : fmin A C w ≤ v := by
  unfold rowVal at h
  have hS : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · rw [hS, Finset.sum_empty] at h
      have := congrArg val h
      simp at this
    · exact hS
  obtain ⟨i, -, hi⟩ := exists_eq_sum hS (fun i => ev (restrictI C A) w i j)
  rw [h] at hi
  exact hsp_fmin_le_of hi

/-- The average is between 0 and `digMax A · K`. -/
lemma hsp_avgMinCap_nonneg {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (K : ℕ) :
    0 ≤ avgMinCap A C K := by
  unfold avgMinCap; positivity

lemma hsp_avgMinCap_le {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (K : ℕ) :
    avgMinCap A C K ≤ (digMax A * K : ℕ) := by
  unfold avgMinCap
  rw [div_le_iff₀ (by positivity)]
  have h : ∑ w ∈ wordsOfLen K, (fmin A C w : ℚ) ≤ ∑ _w ∈ wordsOfLen K, ((digMax A * K : ℕ) : ℚ) := by
    refine Finset.sum_le_sum (fun w hw => ?_)
    have := hsp_fmin_le A C w
    rw [length_of_mem_wordsOfLen hw] at this
    exact_mod_cast this
  rw [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul] at h
  push_cast at h ⊢
  linarith

/-! ### Law of large numbers for independent blocks -/

/-- Rewrite a sum over words of length `p + q` as a sum over pairs (the first `p` letters, the rest) (concatenation is a bijection). -/
lemma hsp_sum_append {R : Type*} [AddCommMonoid R] (p q : ℕ) (φ : Word → Word → R) :
    ∑ w ∈ wordsOfLen (p + q), φ (w.take p) (w.drop p) =
      ∑ u ∈ wordsOfLen p, ∑ v ∈ wordsOfLen q, φ u v := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij' (fun x _ => x.1 ++ x.2) (fun w _ => (w.take p, w.drop p)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hx
    rw [Finset.mem_product] at hx
    exact WinLLN.append_mem hx.1 hx.2
  · intro w hw
    exact Finset.mem_product.mpr ⟨WinLLN.take_mem hw, WinLLN.drop_mem hw⟩
  · rintro ⟨u, v⟩ hx
    rw [Finset.mem_product] at hx
    have hu := length_of_mem_wordsOfLen hx.1
    simp [← hu]
  · intro w _
    simp
  · rintro ⟨u, v⟩ hx
    rw [Finset.mem_product] at hx
    have hu := length_of_mem_wordsOfLen hx.1
    simp [← hu]

/-- The sum of `g` over the first `n` blocks of length `K` of a word (the rest is discarded). -/
def blockSum (g : Word → ℚ) (K : ℕ) : ℕ → Word → ℚ
  | 0, _ => 0
  | n + 1, w => g (w.take K) + blockSum g K n (w.drop K)

/-- **Second moment of the block sum**: if `μ` is the mean of `g` over words of length `K` (`∑ (g - μ) = 0`) and
`(g - μ)² ≤ B`, then over uniform words of length `nK + r` we have `∑ (blockSum n - nμ)² ≤ n 2^(nK+r) B`
(the blocks are independent and the cross terms vanish). -/
theorem hsp_var_blockSum (g : Word → ℚ) (K r : ℕ) (μ B : ℚ)
    (hμ : ∑ u ∈ wordsOfLen K, (g u - μ) = 0)
    (hB : ∀ u ∈ wordsOfLen K, (g u - μ) ^ 2 ≤ B) :
    ∀ n : ℕ, ∑ w ∈ wordsOfLen (n * K + r), (blockSum g K n w - n * μ) ^ 2 ≤
      n * 2 ^ (n * K + r) * B := by
  intro n
  induction n with
  | zero => simp [blockSum]
  | succ n ih =>
    have hL : (n + 1) * K + r = K + (n * K + r) := by ring
    rw [hL]
    have e : ∀ w : Word, (blockSum g K (n + 1) w - ((n + 1 : ℕ) : ℚ) * μ) ^ 2 =
        (fun u v => ((g u - μ) + (blockSum g K n v - n * μ)) ^ 2) (w.take K) (w.drop K) := by
      intro w
      simp only [blockSum]
      push_cast
      ring
    simp_rw [e]
    rw [hsp_sum_append K (n * K + r) (fun u v => ((g u - μ) + (blockSum g K n v - n * μ)) ^ 2)]
    have expand : ∀ u v, ((g u - μ) + (blockSum g K n v - n * μ)) ^ 2 =
        (g u - μ) ^ 2 + 2 * (g u - μ) * (blockSum g K n v - n * μ) +
          (blockSum g K n v - n * μ) ^ 2 := fun u v => by ring
    simp_rw [expand, Finset.sum_add_distrib]
    -- the three terms
    have t1 : ∑ u ∈ wordsOfLen K, ∑ _v ∈ wordsOfLen (n * K + r), (g u - μ) ^ 2 =
        2 ^ (n * K + r) * ∑ u ∈ wordsOfLen K, (g u - μ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul]
      push_cast; ring
    have t2 : ∑ u ∈ wordsOfLen K, ∑ v ∈ wordsOfLen (n * K + r),
        2 * (g u - μ) * (blockSum g K n v - n * μ) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hμ]; ring
    have t3 : ∑ _u ∈ wordsOfLen K, ∑ v ∈ wordsOfLen (n * K + r), (blockSum g K n v - n * μ) ^ 2 =
        2 ^ K * ∑ v ∈ wordsOfLen (n * K + r), (blockSum g K n v - n * μ) ^ 2 := by
      rw [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul]
      push_cast; ring
    rw [t1, t2, t3]
    have hB' : ∑ u ∈ wordsOfLen K, (g u - μ) ^ 2 ≤ 2 ^ K * B := by
      calc ∑ u ∈ wordsOfLen K, (g u - μ) ^ 2 ≤ ∑ _u ∈ wordsOfLen K, B := Finset.sum_le_sum hB
        _ = 2 ^ K * B := by rw [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul]; push_cast; ring
    have h1 := mul_le_mul_of_nonneg_left hB' (by positivity : (0 : ℚ) ≤ 2 ^ (n * K + r))
    have h2 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℚ) ≤ 2 ^ K)
    have e2 : (2 : ℚ) ^ (K + (n * K + r)) = 2 ^ K * 2 ^ (n * K + r) := pow_add _ _ _
    rw [e2]
    push_cast
    nlinarith

/-- **Chebyshev for the block sum**: if `n ≥ 1` and `η > 0`, the number of words of length `nK + r` with `blockSum n < nμ - nη`
is at most `2^(nK+r) B / (n η²)`. -/
theorem hsp_cheb_blockSum (g : Word → ℚ) (K r : ℕ) (μ B : ℚ)
    (hμ : ∑ u ∈ wordsOfLen K, (g u - μ) = 0)
    (hB : ∀ u ∈ wordsOfLen K, (g u - μ) ^ 2 ≤ B) (n : ℕ) (hn : 1 ≤ n) (η : ℚ) (hη : 0 < η) :
    (((wordsOfLen (n * K + r)).filter (fun w => blockSum g K n w < n * μ - n * η)).card : ℚ) *
      (n * η ^ 2) ≤ 2 ^ (n * K + r) * B := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hc : (0 : ℚ) < n * η := by positivity
  have h1 := WinLLN.cheb (wordsOfLen (n * K + r)) (fun w => blockSum g K n w - n * μ) (n * η) hc
  have h2 := hsp_var_blockSum g K r μ B hμ hB n
  have hsub : (wordsOfLen (n * K + r)).filter (fun w => blockSum g K n w < n * μ - n * η) ⊆
      (wordsOfLen (n * K + r)).filter (fun w => n * η < |blockSum g K n w - n * μ|) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, ?_⟩
    rw [abs_sub_comm, lt_abs]
    left; linarith [hw.2]
  have h3 : (((wordsOfLen (n * K + r)).filter (fun w => blockSum g K n w < n * μ - n * η)).card : ℚ)
      ≤ (((wordsOfLen (n * K + r)).filter (fun w => n * η < |blockSum g K n w - n * μ|)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℚ) ≤ (n * η) ^ 2)
  have h5 := (h4.trans h1).trans h2
  -- divide by `(n η)² = n · (n η²)`
  have e : ((((wordsOfLen (n * K + r)).filter
      (fun w => blockSum g K n w < n * μ - n * η)).card : ℚ)) * (n * η) ^ 2 =
      n * (((((wordsOfLen (n * K + r)).filter
      (fun w => blockSum g K n w < n * μ - n * η)).card : ℚ)) * (n * η ^ 2)) := by ring
  rw [e, mul_assoc] at h5
  exact le_of_mul_le_mul_left h5 hnq

/-- By superadditivity, `fmin(w)` is at least the sum of `fmin` over the leading blocks of length `K`. -/
lemma hsp_blockSum_le_fmin {D : ℕ} (A : Interp D) (C : Finset (Fin D)) (K : ℕ) :
    ∀ (n : ℕ) (w : Word), blockSum (fun u => (fmin A C u : ℚ)) K n w ≤ fmin A C w := by
  intro n
  induction n with
  | zero => intro w; simp [blockSum]
  | succ n ih =>
    intro w
    simp only [blockSum]
    have h1 := ih (w.drop K)
    have h2 := hsp_fmin_append A C (w.take K) (w.drop K)
    rw [List.take_append_drop] at h2
    have h2' : ((fmin A C (w.take K) : ℕ) : ℚ) + (fmin A C (w.drop K) : ℚ) ≤ (fmin A C w : ℚ) := by
      exact_mod_cast h2
    linarith

/-! ### Upper bounds on the entries for digit words -/

lemma hsp_natOr0_le_digMax {D : ℕ} (A : Interp D) {s : Letter} (hs : s = Letter.f ∨ s = Letter.t)
    (i j : Fin D) : natOr0 (A s i j) ≤ digMax A := by
  have h : max (natOr0 (A Letter.f i j)) (natOr0 (A Letter.t i j)) ≤ digMax A :=
    Finset.le_sup (f := fun ij : Fin D × Fin D =>
      max (natOr0 (A Letter.f ij.1 ij.2)) (natOr0 (A Letter.t ij.1 ij.2))) (Finset.mem_univ (i, j))
  rcases hs with rfl | rfl
  · exact (le_max_left _ _).trans h
  · exact (le_max_right _ _).trans h

lemma hsp_fmax_singleton {D : ℕ} (A : Interp D) (C : Finset (Fin D)) {s : Letter}
    (hs : s = Letter.f ∨ s = Letter.t) : fmax A C [s] ≤ digMax A := by
  refine natOr0_maxEnt_le _ (fun i j => ?_)
  simp only [ev, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, restrictI]
  split_ifs
  · exact hsp_natOr0_le_digMax A hs i j
  · rw [natOr0_zero]; exact Nat.zero_le _

/-- For digit words, `fmax(w) ≤ digMax · |w|`. -/
lemma hsp_fmax_le_digits {D : ℕ} (A : Interp D) (C : Finset (Fin D)) :
    ∀ w : Word, IsDigits w → fmax A C w ≤ digMax A * w.length
  | [], _ => by rw [fmax_nil]; exact Nat.zero_le _
  | s :: w, hw => by
    have hs := hw s List.mem_cons_self
    have hw' : IsDigits w := fun s' hs' => hw s' (List.mem_cons_of_mem _ hs')
    have h := fmax_append_le A C [s] w
    have h1 := hsp_fmax_singleton A C hs
    have h2 := hsp_fmax_le_digits A C w hw'
    rw [List.singleton_append] at h
    rw [List.length_cons, Nat.mul_succ]
    omega

/-- A finite entry is at most `fmax`. -/
lemma hsp_le_fmax_of {D : ℕ} {A : Interp D} {C : Finset (Fin D)} {w : Word} {i j : Fin D} {v : ℕ}
    (h : ev (restrictI C A) w i j = fin v) : v ≤ fmax A C w := by
  have := natOr0_entry_le (ev (restrictI C A) w) i j
  rwa [h, natOr0_fin] at this

end Collatz.Arctic

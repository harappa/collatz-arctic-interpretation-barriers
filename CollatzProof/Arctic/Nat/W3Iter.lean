/-
# Natural-number interpretations of 𝒯 (Section 12.4): iterated sums (Lemma 12.15)

Lemma 12.15 (i) (the deterministic lemma on iterated sums, a finite form with errors of Thm 2.1 of Y. Kifer, arXiv:2501.15633) and two adaptations used
downstream (in Propositions 12.27 and 12.28).
It depends only on Mathlib (not on the Collatz definitions).

* **Iterated sums with gaps** `gsum`: for a list `[(ξ_s, g_s), …, (ξ_1, g_1)]` (outermost = the side of the largest position),
  `gsum L n = ∑ ∏_k ξ_k(p_k)` over the positions `p_s < n`, `p_{k-1} + g_k ≤ p_k` (`g_1` is not used). The gap condition `p_k + R_k ≤ p_{k+1}`
  of the decomposition (Definition 12.9) is written with `g_{k+1} := R_k`, the last condition `p_s + R_s ≤ t_1` with `n := t_1 + 1 - R_s`, and the first condition `t_0 ≤ p_1` by
  restricting the positions of `ξ_1`. With all gaps 1 this is the iterated sum `isum` of Lemma 12.15 (`I_s(n) = ∑_{p_1<⋯<p_s<n} ∏ ξ_k(p_k)`).
* **Lemma 12.15 (i)** `iterSum_approx` (upper and lower): under the hypothesis `IterHyp` ((IH) with `B`, `N`, `Q` for `c_IH`, `L`, `q`: non-negative, `Q ∈ [0, B]`, for all `n ≤ N`
  `|∑_{p<n} ξ(p) - Q n| ≤ η N`, and `∑_{p<N} ξ ≤ B N`), for all `n ≤ N`,
  `|I_s(n) - (Q_1⋯Q_s/s!) n^s| ≤ ε_s N^s`. Here `ε_s` follows the recursion of the proof of Lemma 12.15 (`epsIter`: `ε_1 = η`,
  `ε_j = B ε_{j-1} + (2η + B/N) B^{j-1}/(j-1)!`). The closed upper bound `epsIter_le`: `ε_s ≤ 3^s (B+1)^s (η + 1/N)`.
  The proof is the written one (induction, Abel summation `abel_sum`, `abel_bound`, and the bound for power sums `pow_sum_bound`).
* **Moving to restricted positions**: `restrict A ξ` (0 outside `A`). `iterHyp_restrict` (if at most `r` positions lie outside `A`, the
  hypothesis carries over with `η` replaced by `η + r B'/N`), `isum_mono` (monotone in the sequences).
* **The version with gaps `≥ M`**: `gsum_le_isum` (if the gaps are at least 1, `gsum ≤ isum`), `isum_sub_gsum_le` (if the gaps are at most `M`,
  `isum - gsum ≤ (s-1)(M-1) B'^s n^{s-1}`, `0 ≤ ξ ≤ B'`). Upper and lower bounds together: `gsum_approx`.

Only the three standard axioms (the axiom checks are in `verify/Probe.lean`). No `sorry`, `axiom` or `native_decide` is used.
-/
import Mathlib

namespace Collatz.Arctic.NatQ5.W3a

open Finset

/-! ## §1 Definitions -/

/-- **Iterated sum with gaps**: `gsum [(ξ_s, g_s), …, (ξ_1, g_1)] n = ∑ ∏_k ξ_k(p_k)` (`p_s < n`, `p_{k-1} + g_k ≤ p_k`). -/
noncomputable def gsum : List ((ℕ → ℝ) × ℕ) → ℕ → ℝ
  | [], _ => 1
  | x :: rest, n => ∑ p ∈ range n, x.1 p * gsum rest (p + 1 - x.2)

@[simp] theorem gsum_nil (n : ℕ) : gsum [] n = 1 := rfl

theorem gsum_cons (x : (ℕ → ℝ) × ℕ) (rest : List ((ℕ → ℝ) × ℕ)) (n : ℕ) :
    gsum (x :: rest) n = ∑ p ∈ range n, x.1 p * gsum rest (p + 1 - x.2) := rfl

/-- **Iterated sum** (`I_s(n)` of Lemma 12.15, gaps 1): the list `ξs = [ξ_s, …, ξ_1]`. -/
noncomputable def isum (ξs : List (ℕ → ℝ)) (n : ℕ) : ℝ := gsum (ξs.map (fun ξ => (ξ, 1))) n

@[simp] theorem isum_nil (n : ℕ) : isum [] n = 1 := rfl

theorem isum_cons (ξ : ℕ → ℝ) (ξs : List (ℕ → ℝ)) (n : ℕ) :
    isum (ξ :: ξs) n = ∑ p ∈ range n, ξ p * isum ξs p := by
  simp only [isum, List.map_cons, gsum_cons, Nat.add_sub_cancel]

/-- The hypothesis of Lemma 12.15 (i) (a sequence `ξ` and its mean `Q`). -/
def IterHyp (B η : ℝ) (N : ℕ) (ξ : ℕ → ℝ) (Q : ℝ) : Prop :=
  (∀ p, 0 ≤ ξ p) ∧ 0 ≤ Q ∧ Q ≤ B ∧ (∀ n ≤ N, |∑ p ∈ range n, ξ p - Q * n| ≤ η * N) ∧
    ∑ p ∈ range N, ξ p ≤ B * N

/-- The error `ε_j` of Lemma 12.15 (i) (the recursion of its proof; `ε_0 := 0`). -/
noncomputable def epsIter (B η : ℝ) (N : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => η
  | j + 2 => B * epsIter B η N (j + 1) + (2 * η + B / N) * B ^ (j + 1) / ((j + 1).factorial : ℝ)

/-! ## §2 Power sums and Abel summation -/

/-- `(i+1) x^i ≤ (x+1)^{i+1} - x^{i+1} ≤ (i+1) (x+1)^i` (`x ≥ 0`). -/
theorem pow_succ_sub_bounds {x : ℝ} (hx : 0 ≤ x) (i : ℕ) :
    ((i : ℝ) + 1) * x ^ i ≤ (x + 1) ^ (i + 1) - x ^ (i + 1) ∧
      (x + 1) ^ (i + 1) - x ^ (i + 1) ≤ ((i : ℝ) + 1) * (x + 1) ^ i := by
  have hg := geom_sum₂_mul (x + 1) x (i + 1)
  rw [show x + 1 - x = (1 : ℝ) by ring, mul_one] at hg
  rw [← hg]
  have hcard : ((range (i + 1)).card : ℝ) = (i : ℝ) + 1 := by rw [card_range]; push_cast; ring
  constructor
  · calc ((i : ℝ) + 1) * x ^ i = ∑ _j ∈ range (i + 1), x ^ i := by rw [sum_const, nsmul_eq_mul, hcard]
      _ ≤ ∑ j ∈ range (i + 1), (x + 1) ^ j * x ^ (i + 1 - 1 - j) := by
        refine sum_le_sum (fun j hj => ?_)
        have hji : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have e : x ^ i = x ^ j * x ^ (i + 1 - 1 - j) := by
          rw [← pow_add]; congr 1; omega
        rw [e]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx (by linarith) j) (by positivity)
  · calc ∑ j ∈ range (i + 1), (x + 1) ^ j * x ^ (i + 1 - 1 - j) ≤ ∑ _j ∈ range (i + 1), (x + 1) ^ i := by
          refine sum_le_sum (fun j hj => ?_)
          have hji : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
          have e : (x + 1) ^ i = (x + 1) ^ j * (x + 1) ^ (i + 1 - 1 - j) := by
            rw [← pow_add]; congr 1; omega
          rw [e]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx (by linarith) _) (by positivity)
      _ = ((i : ℝ) + 1) * (x + 1) ^ i := by rw [sum_const, nsmul_eq_mul, hcard]

/-- `(i+1) ∑_{p<n} p^i ≤ n^{i+1}`. -/
theorem pow_sum_le (i n : ℕ) : ((i : ℝ) + 1) * ∑ p ∈ range n, (p : ℝ) ^ i ≤ (n : ℝ) ^ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add]
    have := (pow_succ_sub_bounds (Nat.cast_nonneg n) i).1
    push_cast
    linarith

/-- `n^{i+1} ≤ (i+1) (∑_{p<n} p^i + n^i)`. -/
theorem le_pow_sum (i n : ℕ) : (n : ℝ) ^ (i + 1) ≤ ((i : ℝ) + 1) * (∑ p ∈ range n, (p : ℝ) ^ i + (n : ℝ) ^ i) := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, range_zero, sum_empty, zero_add]
    rw [zero_pow (Nat.succ_ne_zero i)]
    positivity
  | succ n ih =>
    rw [sum_range_succ]
    have := (pow_succ_sub_bounds (Nat.cast_nonneg n) i).2
    push_cast
    have hi : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
    nlinarith

/-- **Bound for power sums**: `|∑_{p<n} p^i - n^{i+1}/(i+1)| ≤ n^i`. -/
theorem pow_sum_bound (i n : ℕ) :
    |∑ p ∈ range n, (p : ℝ) ^ i - (n : ℝ) ^ (i + 1) / ((i : ℝ) + 1)| ≤ (n : ℝ) ^ i := by
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have h1 := pow_sum_le i n
  have h2 := le_pow_sum i n
  rw [abs_le]
  constructor
  · rw [neg_le, neg_sub, sub_le_iff_le_add, div_le_iff₀ hi]
    linarith
  · rw [sub_le_iff_le_add]
    have : ∑ p ∈ range n, (p : ℝ) ^ i ≤ (n : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
      rw [le_div_iff₀ hi]; linarith
    have : (0 : ℝ) ≤ (n : ℝ) ^ i := by positivity
    linarith

/-- **Abel summation**: `∑_{p<n} (D(p+1) - D(p)) a_p = D(n) a_n - D(0) a_0 - ∑_{p<n} D(p+1)(a_{p+1} - a_p)`. -/
theorem abel_sum (D a : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ range n, (D (p + 1) - D p) * a p =
      D n * a n - D 0 * a 0 - ∑ p ∈ range n, D (p + 1) * (a (p + 1) - a p) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- A bound for Abel summation: if `D 0 = 0`, `|D k| ≤ M` (`k ≤ n`), and `a` is monotone with `a 0 ≥ 0`, then `|∑| ≤ 2 M a_n`. -/
theorem abel_bound {D a : ℕ → ℝ} {n : ℕ} {M : ℝ} (hD0 : D 0 = 0) (hD : ∀ k ≤ n, |D k| ≤ M)
    (ha : Monotone a) (ha0 : 0 ≤ a 0) :
    |∑ p ∈ range n, (D (p + 1) - D p) * a p| ≤ 2 * M * a n := by
  rw [abel_sum, hD0, zero_mul, sub_zero]
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hD 0 (Nat.zero_le _))
  have htel : ∑ p ∈ range n, (a (p + 1) - a p) = a n - a 0 := sum_range_sub a n
  have hs : |∑ p ∈ range n, D (p + 1) * (a (p + 1) - a p)| ≤ M * (a n - a 0) := by
    rw [← htel, mul_sum]
    refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum (fun p hp => ?_))
    have hdp : 0 ≤ a (p + 1) - a p := sub_nonneg.mpr (ha (Nat.le_succ p))
    rw [abs_mul, abs_of_nonneg hdp]
    exact mul_le_mul_of_nonneg_right (hD (p + 1) (mem_range.mp hp)) hdp
  have h1 : |D n * a n| ≤ M * a n := by
    rw [abs_mul, abs_of_nonneg (le_trans ha0 (ha (Nat.zero_le n)))]
    exact mul_le_mul_of_nonneg_right (hD n le_rfl) (le_trans ha0 (ha (Nat.zero_le n)))
  calc |D n * a n - ∑ p ∈ range n, D (p + 1) * (a (p + 1) - a p)|
      ≤ |D n * a n| + |∑ p ∈ range n, D (p + 1) * (a (p + 1) - a p)| := abs_sub _ _
    _ ≤ M * a n + M * (a n - a 0) := add_le_add h1 hs
    _ ≤ 2 * M * a n := by nlinarith

/-! ## §3 Lemma 12.15 (i) -/

/-- **One step**: if `f` is within `e N^i` of `c p^i`, then `∑_{p<n} ξ(p) f(p)` is within `(B e + (2η + B/N) c) N^{i+1}` of
`c Q n^{i+1}/(i+1)` (`n ≤ N`). -/
theorem iter_step {B η e c Q : ℝ} {N i : ℕ} (hN : 1 ≤ N) (hc : 0 ≤ c) {ξ f : ℕ → ℝ}
    (hξ : ∀ p, 0 ≤ ξ p) (hQ0 : 0 ≤ Q) (hQB : Q ≤ B)
    (hpre : ∀ n ≤ N, |∑ p ∈ range n, ξ p - Q * n| ≤ η * N) (htot : ∑ p ∈ range N, ξ p ≤ B * N)
    (hf : ∀ p ≤ N, |f p - c * (p : ℝ) ^ i| ≤ e * (N : ℝ) ^ i) :
    ∀ n ≤ N, |∑ p ∈ range n, ξ p * f p - c * Q / ((i : ℝ) + 1) * (n : ℝ) ^ (i + 1)| ≤
      (B * e + (2 * η + B / N) * c) * (N : ℝ) ^ (i + 1) := by
  intro n hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  -- the first term
  have hT1 : |∑ p ∈ range n, ξ p * (f p - c * (p : ℝ) ^ i)| ≤ B * e * (N : ℝ) ^ (i + 1) := by
    have hsn : ∑ p ∈ range n, ξ p ≤ ∑ p ∈ range N, ξ p :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hn) (fun p _ _ => hξ p)
    have he : 0 ≤ e * (N : ℝ) ^ i := le_trans (abs_nonneg _) (hf 0 (Nat.zero_le _))
    calc |∑ p ∈ range n, ξ p * (f p - c * (p : ℝ) ^ i)|
        ≤ ∑ p ∈ range n, ξ p * (e * (N : ℝ) ^ i) := by
          refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum (fun p hp => ?_))
          rw [abs_mul, abs_of_nonneg (hξ p)]
          exact mul_le_mul_of_nonneg_left (hf p (by have := mem_range.mp hp; omega)) (hξ p)
      _ = (∑ p ∈ range n, ξ p) * (e * (N : ℝ) ^ i) := by rw [sum_mul]
      _ ≤ (B * N) * (e * (N : ℝ) ^ i) := mul_le_mul_of_nonneg_right (hsn.trans htot) he
      _ = B * e * (N : ℝ) ^ (i + 1) := by ring
  -- the second term (Abel summation)
  have hT2 : |∑ p ∈ range n, (ξ p - Q) * (p : ℝ) ^ i| ≤ 2 * (η * N) * (N : ℝ) ^ i := by
    set D : ℕ → ℝ := fun k => ∑ p ∈ range k, ξ p - Q * k with hD
    have hDs : ∀ p, D (p + 1) - D p = ξ p - Q := by
      intro p; simp only [hD, sum_range_succ]; push_cast; ring
    have hab := abel_bound (D := D) (a := fun p => (p : ℝ) ^ i) (n := n) (M := η * N)
      (by simp [hD]) (fun k hk => hpre k (le_trans hk hn))
      (fun p q hpq => pow_le_pow_left₀ (Nat.cast_nonneg p) (by exact_mod_cast hpq) i) (by positivity)
    simp only [hDs] at hab
    refine hab.trans ?_
    have hηN : 0 ≤ η * N := le_trans (abs_nonneg _) (hpre 0 (Nat.zero_le _))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) hnN i) (by positivity)
  -- the third term (power sums)
  have hT3 : |Q * (∑ p ∈ range n, (p : ℝ) ^ i - (n : ℝ) ^ (i + 1) / ((i : ℝ) + 1))| ≤ B * (N : ℝ) ^ i := by
    rw [abs_mul, abs_of_nonneg hQ0]
    exact mul_le_mul hQB ((pow_sum_bound i n).trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hnN i))
      (abs_nonneg _) (le_trans hQ0 hQB)
  -- combining
  have e1 : ∑ p ∈ range n, ξ p * f p - c * Q / ((i : ℝ) + 1) * (n : ℝ) ^ (i + 1) =
      ∑ p ∈ range n, ξ p * (f p - c * (p : ℝ) ^ i) + c * ∑ p ∈ range n, (ξ p - Q) * (p : ℝ) ^ i
        + c * (Q * (∑ p ∈ range n, (p : ℝ) ^ i - (n : ℝ) ^ (i + 1) / ((i : ℝ) + 1))) := by
    simp only [mul_sub, sub_mul, sum_sub_distrib, mul_sum]
    field_simp
    ring
  rw [e1]
  have hB : B * (N : ℝ) ^ i = B / N * (N : ℝ) ^ (i + 1) := by
    field_simp; ring
  calc |∑ p ∈ range n, ξ p * (f p - c * (p : ℝ) ^ i) + c * ∑ p ∈ range n, (ξ p - Q) * (p : ℝ) ^ i
        + c * (Q * (∑ p ∈ range n, (p : ℝ) ^ i - (n : ℝ) ^ (i + 1) / ((i : ℝ) + 1)))|
      ≤ |∑ p ∈ range n, ξ p * (f p - c * (p : ℝ) ^ i)| + |c * ∑ p ∈ range n, (ξ p - Q) * (p : ℝ) ^ i|
        + |c * (Q * (∑ p ∈ range n, (p : ℝ) ^ i - (n : ℝ) ^ (i + 1) / ((i : ℝ) + 1)))| :=
        abs_add_three _ _ _
    _ ≤ B * e * (N : ℝ) ^ (i + 1) + c * (2 * (η * N) * (N : ℝ) ^ i) + c * (B * (N : ℝ) ^ i) := by
        rw [abs_mul c, abs_mul c, abs_of_nonneg hc]
        exact add_le_add (add_le_add hT1 (mul_le_mul_of_nonneg_left hT2 hc)) (mul_le_mul_of_nonneg_left hT3 hc)
    _ = (B * e + (2 * η + B / N) * c) * (N : ℝ) ^ (i + 1) := by
        rw [hB]; ring

/-- The product of the means is at most `B^s`. -/
theorem prod_le_pow {B : ℝ} : ∀ (L : List ((ℕ → ℝ) × ℝ)), (∀ x ∈ L, 0 ≤ x.2 ∧ x.2 ≤ B) →
    0 ≤ (L.map Prod.snd).prod ∧ (L.map Prod.snd).prod ≤ B ^ L.length
  | [], _ => by simp
  | x :: L, h => by
    obtain ⟨h1, h2⟩ := prod_le_pow L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact ⟨mul_nonneg hx.1 h1, mul_le_mul hx.2 h2 h1 (le_trans hx.1 hx.2)⟩

/-- **Lemma 12.15 (i) (iterated sums)**: for a list `L = [(ξ_s, Q_s), …, (ξ_1, Q_1)]` of sequences satisfying the hypothesis `IterHyp`,
for all `n ≤ N`, `|I_s(n) - (Q_1⋯Q_s/s!) n^s| ≤ ε_s N^s` (`ε_s` is the recursion `epsIter`). -/
theorem iterSum_approx {B η : ℝ} {N : ℕ} (hB : 0 ≤ B) (hN : 1 ≤ N) :
    ∀ L : List ((ℕ → ℝ) × ℝ), (∀ x ∈ L, IterHyp B η N x.1 x.2) → ∀ n ≤ N,
      |isum (L.map Prod.fst) n - (L.map Prod.snd).prod / (L.length.factorial : ℝ) * (n : ℝ) ^ L.length| ≤
        epsIter B η N L.length * (N : ℝ) ^ L.length
  | [], _ => by intro n _; simp [epsIter]
  | [x], h => by
    intro n hn
    obtain ⟨-, -, -, hpre, -⟩ := h x List.mem_cons_self
    simp only [List.map_cons, List.map_nil, isum_cons, isum_nil, mul_one, List.prod_cons,
      List.prod_nil, List.length_cons, List.length_nil, zero_add, Nat.factorial_one, Nat.cast_one,
      div_one, pow_one, epsIter]
    exact hpre n hn
  | x :: y :: L, h => by
    intro n hn
    have hrest := iterSum_approx hB hN (y :: L) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    obtain ⟨hξ, hQ0, hQB, hpre, htot⟩ := h x List.mem_cons_self
    set rest := y :: L with hrestdef
    set i := rest.length with hi
    have hP := prod_le_pow rest (fun z hz => by
      obtain ⟨-, a, b, -, -⟩ := h z (List.mem_cons_of_mem _ hz); exact ⟨a, b⟩)
    set P := (rest.map Prod.snd).prod with hPdef
    have hfact : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hc : 0 ≤ P / (i.factorial : ℝ) := div_nonneg hP.1 hfact.le
    have hstep := iter_step (ξ := x.1) (f := isum (rest.map Prod.fst)) (c := P / (i.factorial : ℝ))
      (e := epsIter B η N i) (i := i) hN hc hξ hQ0 hQB hpre htot
      (fun p hp => by
        have := hrest p hp
        rwa [show (rest.map Prod.snd).prod / (rest.length.factorial : ℝ) * (p : ℝ) ^ rest.length =
          P / (i.factorial : ℝ) * (p : ℝ) ^ i from rfl] at this) n hn
    -- the form of the main term
    have hmain : P / (i.factorial : ℝ) * x.2 / ((i : ℝ) + 1) =
        ((x :: rest).map Prod.snd).prod / ((x :: rest).length.factorial : ℝ) := by
      simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.factorial_succ, Nat.cast_mul]
      rw [← hPdef]
      push_cast
      field_simp
      rw [← hi]
      ring
    -- the form of the error
    have hcB : P / (i.factorial : ℝ) ≤ B ^ i / (i.factorial : ℝ) := div_le_div_of_nonneg_right hP.2 hfact.le
    obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨L.length, by rw [hi, hrestdef, List.length_cons]⟩
    have heps : epsIter B η N ((x :: rest).length) =
        B * epsIter B η N i + (2 * η + B / N) * B ^ i / (i.factorial : ℝ) := by
      rw [List.length_cons, ← hi, hj]; rfl
    have hηN : 0 ≤ η * N := le_trans (abs_nonneg _) (hpre 0 (Nat.zero_le _))
    have hη : 0 ≤ η := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      exact nonneg_of_mul_nonneg_left hηN hNpos
    have h2 : 0 ≤ 2 * η + B / N := by positivity
    rw [List.map_cons, isum_cons, ← hmain, heps, List.length_cons, ← hi]
    refine le_trans hstep ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_left hcB h2
    rw [mul_div_assoc]
    linarith

/-- **The closed upper bound for `ε_s`**: `ε_s ≤ 3^s (B+1)^s (η + 1/N)` (`B, η ≥ 0`, `N ≥ 1`). It tends to 0 as `η → 0` and `N → ∞`. -/
theorem epsIter_le {B η : ℝ} {N : ℕ} (hB : 0 ≤ B) (hη : 0 ≤ η) (hN : 1 ≤ N) :
    ∀ j : ℕ, epsIter B η N j ≤ 3 ^ j * (B + 1) ^ j * (η + 1 / N)
  | 0 => by simp only [epsIter, pow_zero, one_mul]; positivity
  | 1 => by
    simp only [epsIter, pow_one]
    have : (0 : ℝ) ≤ 1 / N := by positivity
    nlinarith
  | j + 2 => by
    have ih := epsIter_le hB hη hN (j + 1)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hE : (0 : ℝ) ≤ η + 1 / N := by positivity
    have hB1 : (0 : ℝ) ≤ B + 1 := by linarith
    have hfact : (1 : ℝ) ≤ ((j + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (j + 1)
    have hpow : B ^ (j + 1) ≤ (B + 1) ^ (j + 1) := pow_le_pow_left₀ hB (by linarith) _
    have hdiv : B ^ (j + 1) / ((j + 1).factorial : ℝ) ≤ (B + 1) ^ (j + 1) :=
      le_trans (div_le_self (by positivity) hfact) hpow
    have h2 : 2 * η + B / N ≤ 2 * (B + 1) * (η + 1 / N) := by
      have : B / N ≤ 2 * (B + 1) / N := div_le_div_of_nonneg_right (by linarith) hNpos.le
      have h3 : 2 * (B + 1) * (η + 1 / N) = 2 * (B + 1) * η + 2 * (B + 1) / N := by ring
      rw [h3]; nlinarith
    have hA : B * epsIter B η N (j + 1) ≤ 3 ^ (j + 1) * (B + 1) ^ (j + 2) * (η + 1 / N) := by
      have hpos : 0 ≤ 3 ^ (j + 1) * (B + 1) ^ (j + 1) * (η + 1 / N) := by positivity
      have hε0 : 0 ≤ epsIter B η N (j + 1) ∨ epsIter B η N (j + 1) < 0 := le_or_gt 0 _
      rcases hε0 with hε0 | hε0
      · calc B * epsIter B η N (j + 1) ≤ (B + 1) * epsIter B η N (j + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hε0
          _ ≤ (B + 1) * (3 ^ (j + 1) * (B + 1) ^ (j + 1) * (η + 1 / N)) :=
            mul_le_mul_of_nonneg_left ih hB1
          _ = 3 ^ (j + 1) * (B + 1) ^ (j + 2) * (η + 1 / N) := by ring
      · have : B * epsIter B η N (j + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB hε0.le
        have : 0 ≤ 3 ^ (j + 1) * (B + 1) ^ (j + 2) * (η + 1 / N) := by positivity
        linarith
    have hC : (2 * η + B / N) * B ^ (j + 1) / ((j + 1).factorial : ℝ) ≤
        2 * (B + 1) ^ (j + 2) * (η + 1 / N) := by
      rw [mul_div_assoc]
      calc (2 * η + B / N) * (B ^ (j + 1) / ((j + 1).factorial : ℝ))
          ≤ (2 * (B + 1) * (η + 1 / N)) * (B + 1) ^ (j + 1) :=
            mul_le_mul h2 hdiv (by positivity) (by positivity)
        _ = 2 * (B + 1) ^ (j + 2) * (η + 1 / N) := by ring
    have hsum : 3 ^ (j + 1) * (B + 1) ^ (j + 2) * (η + 1 / N) + 2 * (B + 1) ^ (j + 2) * (η + 1 / N) ≤
        3 ^ (j + 2) * (B + 1) ^ (j + 2) * (η + 1 / N) := by
      have h3 : (2 : ℝ) ≤ 2 * 3 ^ (j + 1) := by
        have : (1 : ℝ) ≤ 3 ^ (j + 1) := one_le_pow₀ (by norm_num)
        linarith
      have hq : 0 ≤ (B + 1) ^ (j + 2) * (η + 1 / N) := by positivity
      have e : 3 ^ (j + 2) * (B + 1) ^ (j + 2) * (η + 1 / N) =
          3 ^ (j + 1) * (B + 1) ^ (j + 2) * (η + 1 / N) + 2 * 3 ^ (j + 1) * ((B + 1) ^ (j + 2) * (η + 1 / N)) := by
        ring
      rw [e]
      nlinarith
    show B * epsIter B η N (j + 1) + (2 * η + B / N) * B ^ (j + 1) / ((j + 1).factorial : ℝ) ≤ _
    linarith

/-! ## §4 Moving to restricted positions -/

/-- Restriction of positions: 0 outside `A`. -/
noncomputable def restrict (A : ℕ → Prop) [DecidablePred A] (ξ : ℕ → ℝ) : ℕ → ℝ :=
  fun p => if A p then ξ p else 0

theorem restrict_le {A : ℕ → Prop} [DecidablePred A] {ξ : ℕ → ℝ} (hξ : ∀ p, 0 ≤ ξ p) (p : ℕ) :
    0 ≤ restrict A ξ p ∧ restrict A ξ p ≤ ξ p := by
  unfold restrict; split_ifs <;> simp [hξ p]

/-- **Carrying the hypothesis over to a restriction**: if at most `r` positions (`p < N`) lie outside `A` and `ξ ≤ B'`, the restricted sequence satisfies the hypothesis
with `η` replaced by `η + r B'/N`. -/
theorem iterHyp_restrict {B η B' : ℝ} {N r : ℕ} (hN : 1 ≤ N) {ξ : ℕ → ℝ} {Q : ℝ} (A : ℕ → Prop) [DecidablePred A]
    (h : IterHyp B η N ξ Q) (hB' : ∀ p, ξ p ≤ B') (hA : ((range N).filter (fun p => ¬ A p)).card ≤ r) :
    IterHyp B (η + r * B' / N) N (restrict A ξ) Q := by
  obtain ⟨hξ, hQ0, hQB, hpre, htot⟩ := h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hB'0 : 0 ≤ B' := le_trans (hξ 0) (hB' 0)
  refine ⟨fun p => (restrict_le hξ p).1, hQ0, hQB, fun n hn => ?_, ?_⟩
  · -- the sum removed by the restriction is at most `r B'`
    have hdiff : ∑ p ∈ range n, ξ p - ∑ p ∈ range n, restrict A ξ p =
        ∑ p ∈ (range n).filter (fun p => ¬ A p), ξ p := by
      rw [← sum_sub_distrib, ← sum_filter_add_sum_filter_not (range n) A]
      have h1 : ∑ p ∈ (range n).filter A, (ξ p - restrict A ξ p) = 0 :=
        sum_eq_zero (fun p hp => by simp [restrict, (mem_filter.mp hp).2])
      have h2 : ∑ p ∈ (range n).filter (fun p => ¬ A p), (ξ p - restrict A ξ p) =
          ∑ p ∈ (range n).filter (fun p => ¬ A p), ξ p :=
        sum_congr rfl (fun p hp => by simp [restrict, (mem_filter.mp hp).2])
      rw [h1, h2, zero_add]
    have hle : ∑ p ∈ (range n).filter (fun p => ¬ A p), ξ p ≤ r * B' := by
      calc ∑ p ∈ (range n).filter (fun p => ¬ A p), ξ p ≤ ∑ _p ∈ (range n).filter (fun p => ¬ A p), B' :=
            sum_le_sum (fun p _ => hB' p)
        _ = ((range n).filter (fun p => ¬ A p)).card * B' := by rw [sum_const, nsmul_eq_mul]
        _ ≤ r * B' := by
          apply mul_le_mul_of_nonneg_right _ hB'0
          have : ((range n).filter (fun p => ¬ A p)).card ≤ r :=
            le_trans (card_le_card (filter_subset_filter _ (range_subset_range.mpr hn))) hA
          exact_mod_cast this
    have hnn : 0 ≤ ∑ p ∈ (range n).filter (fun p => ¬ A p), ξ p := sum_nonneg (fun p _ => hξ p)
    have e : (η + r * B' / N) * N = η * N + r * B' := by field_simp
    rw [e]
    have h0 := hpre n hn
    rw [abs_le] at h0 ⊢
    constructor <;> linarith
  · calc ∑ p ∈ range N, restrict A ξ p ≤ ∑ p ∈ range N, ξ p := sum_le_sum (fun p _ => (restrict_le hξ p).2)
      _ ≤ B * N := htot

/-- An iterated sum is non-negative (if the sequences are non-negative). -/
theorem gsum_nonneg : ∀ (L : List ((ℕ → ℝ) × ℕ)), (∀ x ∈ L, ∀ p, 0 ≤ x.1 p) → ∀ n, 0 ≤ gsum L n
  | [], _, _ => by simp
  | x :: L, h, n => by
    rw [gsum_cons]
    exact sum_nonneg (fun p _ => mul_nonneg (h x List.mem_cons_self p)
      (gsum_nonneg L (fun y hy => h y (List.mem_cons_of_mem _ hy)) _))

/-- An iterated sum is monotone in `n`. -/
theorem gsum_mono : ∀ (L : List ((ℕ → ℝ) × ℕ)), (∀ x ∈ L, ∀ p, 0 ≤ x.1 p) → ∀ {n n' : ℕ}, n ≤ n' →
    gsum L n ≤ gsum L n'
  | [], _, _, _, _ => le_rfl
  | x :: L, h, n, n', hnn' => by
    rw [gsum_cons, gsum_cons]
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hnn') (fun p _ _ =>
      mul_nonneg (h x List.mem_cons_self p) (gsum_nonneg L (fun y hy => h y (List.mem_cons_of_mem _ hy)) _))

theorem isum_nonneg {ξs : List (ℕ → ℝ)} (h : ∀ ξ ∈ ξs, ∀ p, 0 ≤ ξ p) (n : ℕ) : 0 ≤ isum ξs n :=
  gsum_nonneg _ (fun x hx => by
    obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.mp hx
    exact h ξ hξ) n

theorem isum_mono_n {ξs : List (ℕ → ℝ)} (h : ∀ ξ ∈ ξs, ∀ p, 0 ≤ ξ p) {n n' : ℕ} (hnn' : n ≤ n') :
    isum ξs n ≤ isum ξs n' :=
  gsum_mono _ (fun x hx => by
    obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.mp hx
    exact h ξ hξ) hnn'

/-- **An iterated sum is monotone in the sequences** (`0 ≤ ξ'_k ≤ ξ_k`): the iterated sum of restricted sequences is at most the original one (and non-negative). -/
theorem isum_mono_aux {ξs' ξs : List (ℕ → ℝ)}
    (hF : List.Forall₂ (fun ξ' ξ => ∀ p, 0 ≤ ξ' p ∧ ξ' p ≤ ξ p) ξs' ξs) :
    ∀ n, 0 ≤ isum ξs' n ∧ isum ξs' n ≤ isum ξs n := by
  induction hF with
  | nil => intro n; simp
  | cons h _ ih =>
    intro n
    rw [isum_cons, isum_cons]
    exact ⟨sum_nonneg (fun p _ => mul_nonneg (h p).1 (ih p).1),
      sum_le_sum (fun p _ => mul_le_mul (h p).2 (ih p).2 (ih p).1 (le_trans (h p).1 (h p).2))⟩

theorem isum_mono {ξs' ξs : List (ℕ → ℝ)}
    (hF : List.Forall₂ (fun ξ' ξ => ∀ p, 0 ≤ ξ' p ∧ ξ' p ≤ ξ p) ξs' ξs) (n : ℕ) :
    isum ξs' n ≤ isum ξs n := (isum_mono_aux hF n).2

/-! ## §5 The version with gaps `≥ M` -/

/-- If the gaps are at least 1, the iterated sum with gaps is at most the iterated sum. -/
theorem gsum_le_isum : ∀ (L : List ((ℕ → ℝ) × ℕ)), (∀ x ∈ L, (∀ p, 0 ≤ x.1 p) ∧ 1 ≤ x.2) → ∀ n,
    gsum L n ≤ isum (L.map Prod.fst) n
  | [], _, _ => le_rfl
  | x :: L, h, n => by
    rw [gsum_cons, List.map_cons, isum_cons]
    have hL := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x List.mem_cons_self
    refine sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left ?_ (hx.1 p))
    calc gsum L (p + 1 - x.2) ≤ gsum L p := gsum_mono L (fun y hy => (hL y hy).1) (by omega)
      _ ≤ isum (L.map Prod.fst) p := gsum_le_isum L hL p

/-- A coarse upper bound: if `0 ≤ ξ ≤ B'`, then `I_s(n) ≤ B'^s n^s`. -/
theorem isum_le_pow {B' : ℝ} : ∀ (ξs : List (ℕ → ℝ)), (∀ ξ ∈ ξs, ∀ p, 0 ≤ ξ p ∧ ξ p ≤ B') → ∀ n,
    isum ξs n ≤ B' ^ ξs.length * (n : ℝ) ^ ξs.length
  | [], _, n => by simp
  | ξ :: ξs, h, n => by
    rw [isum_cons, List.length_cons]
    have hξs := fun ζ hζ => h ζ (List.mem_cons_of_mem _ hζ)
    have hξ := h ξ List.mem_cons_self
    have hB' : 0 ≤ B' := le_trans (hξ 0).1 (hξ 0).2
    calc ∑ p ∈ range n, ξ p * isum ξs p ≤ ∑ _p ∈ range n, B' * (B' ^ ξs.length * (n : ℝ) ^ ξs.length) := by
          refine sum_le_sum (fun p hp => mul_le_mul (hξ p).2 ?_ (isum_nonneg (fun ζ hζ q => (hξs ζ hζ q).1) p) hB')
          refine le_trans (isum_le_pow ξs hξs p) (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact pow_le_pow_left₀ (Nat.cast_nonneg p) (by exact_mod_cast (mem_range.mp hp).le) _
      _ = B' ^ (ξs.length + 1) * (n : ℝ) ^ (ξs.length + 1) := by
          rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- The difference of iterated sums over an interval: if `p' ≤ p ≤ n`, then `I(p) - I(p') ≤ (p - p') B'^s n^{s-1}` (`s ≥ 1`). -/
theorem isum_sub_le {B' : ℝ} (ξ : ℕ → ℝ) (ξs : List (ℕ → ℝ)) (h : ∀ ζ ∈ ξ :: ξs, ∀ p, 0 ≤ ζ p ∧ ζ p ≤ B')
    {p' p n : ℕ} (hpp' : p' ≤ p) (hpn : p ≤ n) :
    isum (ξ :: ξs) p - isum (ξ :: ξs) p' ≤ ((p - p' : ℕ) : ℝ) * B' ^ (ξs.length + 1) * (n : ℝ) ^ ξs.length := by
  rw [isum_cons, isum_cons, ← sum_range_add_sum_Ico _ hpp', add_sub_cancel_left]
  have hξs := fun ζ hζ => h ζ (List.mem_cons_of_mem _ hζ)
  have hξ := h ξ List.mem_cons_self
  have hB' : 0 ≤ B' := le_trans (hξ 0).1 (hξ 0).2
  calc ∑ q ∈ Ico p' p, ξ q * isum ξs q ≤ ∑ _q ∈ Ico p' p, B' * (B' ^ ξs.length * (n : ℝ) ^ ξs.length) := by
        refine sum_le_sum (fun q hq => mul_le_mul (hξ q).2 ?_ (isum_nonneg (fun ζ hζ r => (hξs ζ hζ r).1) q) hB')
        refine le_trans (isum_le_pow ξs hξs q) (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact pow_le_pow_left₀ (Nat.cast_nonneg q) (by exact_mod_cast (le_trans (mem_Ico.mp hq).2.le hpn)) _
    _ = ((p - p' : ℕ) : ℝ) * B' ^ (ξs.length + 1) * (n : ℝ) ^ ξs.length := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul]; ring

/-- **Bound for tuples with short gaps**: if `0 ≤ ξ ≤ B'` and all gaps are at most `M` (`≥ 1`), then
`I_s(n) - G(n) ≤ (s-1)(M-1) B'^s n^{s-1}`. -/
theorem isum_sub_gsum_le {B' : ℝ} {M : ℕ} (hM : 1 ≤ M) : ∀ (L : List ((ℕ → ℝ) × ℕ)),
    (∀ x ∈ L, (∀ p, 0 ≤ x.1 p ∧ x.1 p ≤ B') ∧ x.2 ≤ M) → ∀ n,
      isum (L.map Prod.fst) n - gsum L n ≤
        ((L.length - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ L.length * (n : ℝ) ^ (L.length - 1)
  | [], _, n => by simp
  | [x], h, n => by
    simp only [List.map_cons, List.map_nil, isum_cons, isum_nil, gsum_cons, gsum_nil, sub_self,
      List.length_cons, List.length_nil, zero_add, Nat.sub_self, Nat.cast_zero, zero_mul, le_refl]
  | x :: y :: L, h, n => by
    set rest := y :: L with hrest
    have hx := h x List.mem_cons_self
    have hR := fun z hz => h z (List.mem_cons_of_mem _ hz)
    have hB' : 0 ≤ B' := le_trans (hx.1 0).1 (hx.1 0).2
    have ih := isum_sub_gsum_le hM rest hR
    have hnn : ∀ z ∈ rest, ∀ p, 0 ≤ z.1 p := fun z hz p => ((hR z hz).1 p).1
    set r := rest.length with hr
    have hr1 : 1 ≤ r := by rw [hr, hrest, List.length_cons]; omega
    -- the difference at each position
    have hbr : ∀ p < n, isum (rest.map Prod.fst) p - gsum rest (p + 1 - x.2) ≤
        (r : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ r * (n : ℝ) ^ (r - 1) := by
      intro p hp
      have h1 : gsum rest (p + 1 - M) ≤ gsum rest (p + 1 - x.2) := gsum_mono rest hnn (by omega)
      have h2 : isum (rest.map Prod.fst) p - isum (rest.map Prod.fst) (p + 1 - M) ≤
          ((M - 1 : ℕ) : ℝ) * B' ^ r * (n : ℝ) ^ (r - 1) := by
        have hmap : rest.map Prod.fst = y.1 :: L.map Prod.fst := by rw [hrest]; rfl
        rw [hmap]
        have hall : ∀ ζ ∈ y.1 :: L.map Prod.fst, ∀ q, 0 ≤ ζ q ∧ ζ q ≤ B' := by
          intro ζ hζ q
          rw [← hmap] at hζ
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hζ
          exact (hR z hz).1 q
        have := isum_sub_le y.1 (L.map Prod.fst) hall (p' := p + 1 - M) (p := p) (n := n) (by omega) hp.le
        have hlen : (L.map Prod.fst).length + 1 = r := by rw [List.length_map, hr, hrest, List.length_cons]
        have hlen' : (L.map Prod.fst).length = r - 1 := by omega
        rw [hlen, hlen'] at this
        refine le_trans this (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity))
        exact_mod_cast (by omega : p - (p + 1 - M) ≤ M - 1)
      have h3 := ih (p + 1 - M)
      have h4 : ((r - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ r * ((p + 1 - M : ℕ) : ℝ) ^ (r - 1) ≤
          ((r - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ r * (n : ℝ) ^ (r - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega)) _)
          (by positivity)
      have e : (r : ℝ) = ((r - 1 : ℕ) : ℝ) + 1 := by rw [Nat.cast_sub hr1]; ring
      rw [e]
      nlinarith
    rw [List.map_cons, isum_cons, gsum_cons, ← sum_sub_distrib]
    calc ∑ p ∈ range n, (x.1 p * isum (rest.map Prod.fst) p - x.1 p * gsum rest (p + 1 - x.2))
        = ∑ p ∈ range n, x.1 p * (isum (rest.map Prod.fst) p - gsum rest (p + 1 - x.2)) := by
          refine sum_congr rfl (fun p _ => by ring)
      _ ≤ ∑ _p ∈ range n, B' * ((r : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ r * (n : ℝ) ^ (r - 1)) := by
          refine sum_le_sum (fun p hp => ?_)
          have hb := hbr p (mem_range.mp hp)
          have hX : 0 ≤ (r : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ r * (n : ℝ) ^ (r - 1) := by positivity
          calc x.1 p * (isum (rest.map Prod.fst) p - gsum rest (p + 1 - x.2))
              ≤ x.1 p * ((r : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ r * (n : ℝ) ^ (r - 1)) :=
                mul_le_mul_of_nonneg_left hb ((hx.1 p).1)
            _ ≤ B' * ((r : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ r * (n : ℝ) ^ (r - 1)) :=
                mul_le_mul_of_nonneg_right ((hx.1 p).2) hX
      _ = ((((x :: rest).length - 1 : ℕ) : ℝ)) * ((M - 1 : ℕ) : ℝ) * B' ^ (x :: rest).length *
            (n : ℝ) ^ ((x :: rest).length - 1) := by
          rw [sum_const, card_range, nsmul_eq_mul, List.length_cons, ← hr, Nat.add_sub_cancel]
          have e2 : (n : ℝ) ^ r = (n : ℝ) * (n : ℝ) ^ (r - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hr1]
          rw [e2, pow_succ]; ring

/-- **Upper and lower bounds together** (as used in Propositions 12.27 and 12.28; Lemma 12.15 (ii)): if the list `L = [((ξ_s, g_s), Q_s), …]` satisfies the hypothesis of
Lemma 12.15 (i), `0 ≤ ξ ≤ B'`, and the gaps satisfy `1 ≤ g ≤ M`, then for all `n ≤ N`
`main - ε_s N^s - (s-1)(M-1) B'^s n^{s-1} ≤ G(n) ≤ main + ε_s N^s` (`main = (∏Q/s!) n^s`). -/
theorem gsum_approx {B η B' : ℝ} {N M : ℕ} (hB : 0 ≤ B) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (L : List (((ℕ → ℝ) × ℕ) × ℝ))
    (hL : ∀ x ∈ L, IterHyp B η N x.1.1 x.2 ∧ (∀ p, x.1.1 p ≤ B') ∧ 1 ≤ x.1.2 ∧ x.1.2 ≤ M) :
    ∀ n ≤ N,
      gsum (L.map Prod.fst) n ≤ (L.map Prod.snd).prod / (L.length.factorial : ℝ) * (n : ℝ) ^ L.length +
          epsIter B η N L.length * (N : ℝ) ^ L.length ∧
      (L.map Prod.snd).prod / (L.length.factorial : ℝ) * (n : ℝ) ^ L.length -
          epsIter B η N L.length * (N : ℝ) ^ L.length -
          ((L.length - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ L.length * (n : ℝ) ^ (L.length - 1) ≤
        gsum (L.map Prod.fst) n := by
  intro n hn
  set L₁ : List ((ℕ → ℝ) × ℝ) := L.map (fun x => (x.1.1, x.2)) with hL₁
  have hfst : (L.map Prod.fst).map Prod.fst = L₁.map Prod.fst := by
    rw [hL₁, List.map_map, List.map_map]; rfl
  have hsnd : L₁.map Prod.snd = L.map Prod.snd := by rw [hL₁, List.map_map]; rfl
  have hlen : L₁.length = L.length := by rw [hL₁, List.length_map]
  have happ := iterSum_approx hB hN L₁ (fun z hz => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact (hL x hx).1) n hn
  rw [hsnd, hlen, ← hfst] at happ
  have hle := gsum_le_isum (L.map Prod.fst) (fun z hz => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact ⟨(hL x hx).1.1, (hL x hx).2.2.1⟩) n
  have hgap := isum_sub_gsum_le hM (L.map Prod.fst) (fun z hz => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact ⟨fun p => ⟨(hL x hx).1.1 p, (hL x hx).2.1 p⟩, (hL x hx).2.2.2⟩) n
  rw [List.length_map] at hgap
  rw [abs_le] at happ
  constructor <;> linarith [happ.1, happ.2]

end Collatz.Arctic.NatQ5.W3a

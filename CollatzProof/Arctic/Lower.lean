/-
The main theorem: Lemma 6.6 of the paper (lower bound for a sequence of concatenated close-to-uniform intervals), Section 6.3.
The only hypothesis is `HSP` (`CoreHyp.lean`; Corollary B.4).

* `TVClose` (the law is within total variation distance `δ` of uniform), `LowerAt` (the property in the conclusion).
* `lowerAt_of_good`: a word whose two intervals are both good (the first `m_l` letters contain `u*` and the rest is a good word) satisfies `LowerAt`
  (`lower_of_good` and the absorption of constants `lower_arith`; the split is at `m_l := L_l / κ`, `κ ≥ 4(∑_C Λ_C)/ε`).
* `lemma_56_11_2`: the lemma itself. The fraction of words whose part before the split does not contain `u*` (`noInfix_small`) and the fraction whose part after it is not a good word
  (`spgood_small`, from `HSP`) are bounded for uniform words, and combined by the total variation distance (`tv_bad_le`) and a union bound (`count_two`).
* Parts: `LowerPath.lean` (paths and restricted processes), `LowerLineage.lean` (lineages and stages, the deterministic part), `LowerCount.lean`
  (counting).
-/
import CollatzProof.Arctic.LowerLineage
import CollatzProof.Arctic.LowerCount
import CollatzProof.Arctic.RateUpper

namespace Collatz.Arctic.Lower

open MinIdeal Matrix

variable {D : ℕ}

/-- Real-number estimate (absorption of the constants). -/
lemma lower_arith {r R ε ε' L₁ L₂ m₁ m₂ a b Y Z G v : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R)
    (hε : 0 < ε) (hε'4 : ε' ≤ ε / 4) (hm₁ : 0 ≤ m₁) (hm₁L : m₁ ≤ L₁)
    (hm₂ : 0 ≤ m₂) (hm₂L : m₂ ≤ L₂) (hRm₁ : R * m₁ ≤ ε / 4 * L₁) (hRm₂ : R * m₂ ≤ ε / 4 * L₂)
    (ha : 0 ≤ a) (haG : a ≤ G) (hb : 0 ≤ b) (hbG : b ≤ G) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hv : (r - ε') * ((L₁ - m₁) + (L₂ - m₂)) ≤ v) :
    (r - ε) * (a + L₁ + b + L₂ + Y + Z) - R * (2 * G + Y + Z) ≤ v := by
  have e1 : r * m₁ ≤ R * m₁ := mul_le_mul_of_nonneg_right hrR hm₁
  have e2 : r * m₂ ≤ R * m₂ := mul_le_mul_of_nonneg_right hrR hm₂
  have e3 : ε' * (L₁ - m₁) ≤ ε / 4 * L₁ :=
    mul_le_mul hε'4 (by linarith) (by linarith) (by linarith)
  have e4 : ε' * (L₂ - m₂) ≤ ε / 4 * L₂ :=
    mul_le_mul hε'4 (by linarith) (by linarith) (by linarith)
  have e5 : r * (a + b + Y + Z) ≤ R * (2 * G + Y + Z) :=
    mul_le_mul hrR (by linarith) (by linarith) (by linarith)
  have e6 : 0 ≤ ε * (a + b + Y + Z) := mul_nonneg hε.le (by linarith)
  have e7 : 0 ≤ ε * (L₁ + L₂) := mul_nonneg hε.le (by linarith)
  nlinarith [e1, e2, e3, e4, e5, e6, e7]


/-- The law of a family of words `B : ι → Word` (under the uniform weight on `X`) is within total variation distance `δ` of the uniform law of length `L`
(the sum of the absolute differences is at most `2δ`). -/
def TVClose {ι : Type*} (X : Finset ι) (B : ι → Word) (L : ℕ) (δ : ℝ) : Prop :=
  ∑ v ∈ wordsOfLen L, |(((X.filter (fun x => B x = v)).card : ℝ) / X.card) - 1 / 2 ^ L| ≤ 2 * δ

/-- The property in the conclusion of Lemma 6.6 (for a word `ω`). With `N := |ω|`, `T := N - |z|` and `I` the set of classes hit by the support at time
`T - |u*|`: for `p ∈ I`, `j ∈ I`, `j ≤ p` and `b ∈ β_p`, the value `v` at time `T` is
at least `(Λ_{C(j)} - ε)N - Cst`. -/
def LowerAt {D : ℕ} {E : BRel (Fin D)} (u : Fin D → Arc) (A : Interp D) (hE : E * E = E)
    (ustar z : Word) (ε Cst : ℝ) (ω : Word) : Prop :=
  ∀ p ∈ hitSet hE (suppV (vecAfter u A (ω.take (ω.length - z.length - ustar.length)))),
  ∀ j ∈ hitSet hE (suppV (vecAfter u A (ω.take (ω.length - z.length - ustar.length)))),
  j ≤ p → ∀ b, beta hE p b → ∀ v : ℕ,
    vecAfter u A (ω.take (ω.length - z.length)) b = Arc.fin v →
      (classRate hE A j - ε) * ω.length - Cst ≤ v

/-- Count from the fractions of two bad events. -/
lemma count_two {ι : Type*} (X : Finset ι) (P₁ P₂ Q : ι → Prop) [DecidablePred P₁]
    [DecidablePred P₂] [DecidablePred Q]
    (h : ∀ x ∈ X, P₁ x → P₂ x → Q x) {η₁ η₂ : ℝ}
    (h₁ : ((X.filter (fun x => ¬ P₁ x)).card : ℝ) ≤ η₁ * X.card)
    (h₂ : ((X.filter (fun x => ¬ P₂ x)).card : ℝ) ≤ η₂ * X.card) :
    (1 - η₁ - η₂) * X.card ≤ ((X.filter Q).card : ℝ) := by
  classical
  have hsub : X ⊆ X.filter Q ∪ (X.filter (fun x => ¬ P₁ x) ∪ X.filter (fun x => ¬ P₂ x)) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases a : P₁ x
    · by_cases b : P₂ x
      · exact Or.inl ⟨hx, h x hx a b⟩
      · exact Or.inr (Or.inr ⟨hx, b⟩)
    · exact Or.inr (Or.inl ⟨hx, a⟩)
  have c := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have c' : (X.card : ℝ) ≤ ((X.filter Q).card : ℝ) + (((X.filter (fun x => ¬ P₁ x)).card : ℝ) +
      ((X.filter (fun x => ¬ P₂ x)).card : ℝ)) := by exact_mod_cast c
  linarith

/-- Facts about the split `m := L / κ` for an interval of length `L` (`κ ≥ 4R/ε`, `κ ≥ 2`). -/
lemma split_facts {R ε : ℝ} (hR0 : 0 ≤ R) (hε : 0 < ε) {κ : ℕ} (hκ : 4 * R / ε ≤ κ) (L : ℕ) :
    R * ((L / κ : ℕ) : ℝ) ≤ ε / 4 * L := by
  rcases Nat.eq_zero_or_pos κ with h0 | hpos
  · subst h0; simp only [Nat.div_zero, Nat.cast_zero, mul_zero]; positivity
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hpos
  have hRκ : R / κ ≤ ε / 4 := by
    rw [div_le_iff₀ hκpos]
    rw [div_le_iff₀ hε] at hκ
    linarith
  have h1 : ((L / κ : ℕ) : ℝ) ≤ (L : ℝ) / κ := Nat.cast_div_le
  calc R * ((L / κ : ℕ) : ℝ) ≤ R * ((L : ℝ) / κ) := mul_le_mul_of_nonneg_left h1 hR0
    _ = R / κ * L := by ring
    _ ≤ ε / 4 * L := mul_le_mul_of_nonneg_right hRκ (Nat.cast_nonneg L)

section Final

variable {A : Interp D} {K : Set (BRel (Fin D))} {E : BRel (Fin D)}
  (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) (hEK : E ∈ K) (hE : E * E = E)

open Classical in
include hK hEK in
/-- A word with good intervals satisfies `LowerAt` (`lower_of_good` and the absorption of constants). -/
theorem lowerAt_of_good (u : Fin D → Arc) (ustar : Word) (huE : suppRel (ev A ustar) = E)
    (y z : Word) (hy : IsDigits y) (hyu : ustar <:+ y) {ε ε' R : ℝ} (G : ℕ) (hε : 0 < ε)
    (hε'4 : ε' ≤ ε / 4) (hrR : ∀ C, rate A C ≤ R) (g₀ g₁ B₁ B₂ : Word) (hg₀ : g₀.length ≤ G)
    (hg₁ : IsDigits g₁) (hg₁G : g₁.length ≤ G) (hB₁ : IsDigits B₁) (hB₂ : IsDigits B₂)
    (m₁ m₂ : ℕ) (hm₁ : m₁ ≤ B₁.length) (hm₂ : m₂ ≤ B₂.length)
    (hRm₁ : R * m₁ ≤ ε / 4 * B₁.length) (hRm₂ : R * m₂ ≤ ε / 4 * B₂.length)
    (hi₁ : ustar <:+: B₁.take m₁) (hgood₁ : SPGood A ε' (B₁.drop m₁))
    (hi₂ : ustar <:+: B₂.take m₂) (hgood₂ : SPGood A ε' (B₂.drop m₂)) :
    LowerAt u A hE ustar z ε (R * (2 * G + y.length + z.length)) (g₀ ++ B₁ ++ g₁ ++ B₂ ++ y ++ z) := by
  intro p hp j hj hjp b hb v hv
  have hkey := lower_of_good hK hEK hE u ustar huE y z hy hyu g₀ g₁ B₁ B₂ hg₁ hB₁ hB₂ m₁ m₂
    hi₁ hgood₁ hi₂ hgood₂ p hp j hj hjp b hb v hv
  rw [List.length_drop, List.length_drop] at hkey
  obtain ⟨C, -, hCr⟩ : ∃ C : Finset (Fin D),
      (∀ a, a ∈ C ↔ a ∈ comp (B0 A) (B1 A) hE j) ∧ classRate hE A j = rate A C :=
    ⟨_, fun a => Set.mem_toFinset, rfl⟩
  have hr0 : 0 ≤ classRate hE A j := by rw [hCr]; exact rate_nonneg A C
  have hrR' : classRate hE A j ≤ R := by rw [hCr]; exact hrR C
  have hlen : ((g₀ ++ B₁ ++ g₁ ++ B₂ ++ y ++ z).length : ℝ) =
      g₀.length + B₁.length + g₁.length + B₂.length + y.length + z.length := by
    simp only [List.length_append]; push_cast; ring
  rw [hlen]
  rw [Nat.cast_sub hm₁, Nat.cast_sub hm₂] at hkey
  exact lower_arith hr0 hrR' hε hε'4 (Nat.cast_nonneg _) (by exact_mod_cast hm₁)
    (Nat.cast_nonneg _) (by exact_mod_cast hm₂) hRm₁ hRm₂ (Nat.cast_nonneg _)
    (by exact_mod_cast hg₀) (Nat.cast_nonneg _) (by exact_mod_cast hg₁G)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hkey

end Final

open Classical in
/-- **Lemma 6.6 (lower bound for a sequence of concatenated close-to-uniform intervals)** (Section 6.3, the form with two intervals). Under the hypothesis `HSP`:

Fix an automaton `A` (the finite entries of the digit matrices are natural numbers, so the weights are nonnegative), an initial row vector `u`, an idempotent `E` of the
minimal ideal `K` of `Mon (B0 A) (B1 A)`, a digit word `u*` of type `E` (`ustar`), a digit word `y` ending with `u*`, an arbitrary word `z`,
and a length bound `G`. There is a constant `Cst := (∑_C rate A C)(2G + |y| + |z|)` (the sum over all subsets `C` of indices;
it is used as an upper bound for `Λ_{C(j)}`; it depends only on `A`, `G`, `y`, `z`, not on `ε`)
such that for every `ε > 0` there is `L₀` such that, if `L₁, L₂ ≥ L₀`, the following holds. For a family of words over a finite index set `X` (uniform weight)
`ω x = g₀ x ++ B₁ x ++ g₁ x ++ B₂ x ++ y ++ z` (`|g₀ x|, |g₁ x| ≤ G`, `g₁ x` a digit word, `B_l x` a digit word of length
`L_l`) such that the law of `B_l` is within total variation distance `δ_l` of uniform (`TVClose`; no independence between the intervals is assumed),
the number of `x` satisfying `LowerAt` is at least `(1 - δ₁ - δ₂ - ε)|X|`. `LowerAt` says: with `N := |ω|`, `T := N - |z|` (the end of the last
occurrence of `u*` in `y`) and `I` the set of classes hit by the support at time `T - |u*|` (the upper set at time `T`), for `p ∈ I`, `j ∈ I`,
`j ≤ p` and `b ∈ β_p`, the value `v` of `b` at time `T` is at least `(Λ_{C(j)} - ε)N - Cst`.

In asymptotic form this is the statement "with probability at least `1 - Σ_l δ_l - o(1)`, for every `p ∈ I` that exits by `z`, the indices of `β_p` have values
at least `Λ_I(p)N - o(N)`" in the case of two intervals (taking the maximum over `j` gives `Λ_I(p) = max{Λ_{C(j)} : j ≤ p, j ∈ I}`).
Here `o(1)` is `ε` and `o(N)` is `εN + Cst`. The lower bound does not use that `p` exits by `z`, so it is proved for all `p ∈ I`. The last
sentence of Lemma 6.6 (`V ≥ (α_z(I) - ε)N - Cst`, through the exit vector `c`) is not included here; it is `lower_value` in `CoreLowerApp.lean`. -/
theorem lemma_56_11_2 (hSP : HSP) {D : ℕ} (A : Interp D) (u : Fin D → Arc)
    {K : Set (BRel (Fin D))} (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) {E : BRel (Fin D)}
    (hEK : E ∈ K) (hE : E * E = E) (ustar : Word) (hus : IsDigits ustar)
    (huE : suppRel (ev A ustar) = E) (y z : Word) (hy : IsDigits y) (hyu : ustar <:+ y) (G : ℕ) :
    ∃ Cst : ℝ, ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L₁ L₂ : ℕ, L₀ ≤ L₁ → L₀ ≤ L₂ →
      ∀ {ι : Type*} (X : Finset ι) (g₀ g₁ B₁ B₂ : ι → Word) (δ₁ δ₂ : ℝ),
        (∀ x ∈ X, (g₀ x).length ≤ G) → (∀ x ∈ X, IsDigits (g₁ x) ∧ (g₁ x).length ≤ G) →
        (∀ x ∈ X, B₁ x ∈ wordsOfLen L₁) → (∀ x ∈ X, B₂ x ∈ wordsOfLen L₂) →
        TVClose X B₁ L₁ δ₁ → TVClose X B₂ L₂ δ₂ →
        (1 - δ₁ - δ₂ - ε) * X.card ≤ ((X.filter (fun x =>
          LowerAt u A hE ustar z ε Cst (g₀ x ++ B₁ x ++ g₁ x ++ B₂ x ++ y ++ z))).card : ℝ) := by
  have hR0 : 0 ≤ ∑ C : Finset (Fin D), rate A C := Finset.sum_nonneg (fun C _ => rate_nonneg A C)
  have hrR : ∀ C, rate A C ≤ ∑ C : Finset (Fin D), rate A C := fun C =>
    Finset.single_le_sum (f := fun C => rate A C) (fun C _ => rate_nonneg A C) (Finset.mem_univ C)
  refine ⟨(∑ C : Finset (Fin D), rate A C) * (2 * G + y.length + z.length), fun ε hε => ?_⟩
  have hNP0 : (0 : ℝ) ≤ (Fintype.card (Finset (Fin D) × Finset (Fin D)) : ℝ) := Nat.cast_nonneg _
  obtain ⟨ε', hε'0, hε'4, hNPε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε / 4 ∧
      (Fintype.card (Finset (Fin D) × Finset (Fin D)) : ℝ) * ε' ≤ ε / 4 := by
    refine ⟨ε / (4 * ((Fintype.card (Finset (Fin D) × Finset (Fin D)) : ℝ) + 1)), by positivity,
      div_le_div_of_nonneg_left hε.le (by positivity) (by linarith), ?_⟩
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨LS, hLS⟩ := spgood_small hSP A hε'0
  obtain ⟨m₀, hm₀⟩ := noInfix_small ustar hus (η := ε / 4) (by positivity)
  obtain ⟨κ, hκ2, hκ⟩ : ∃ κ : ℕ, 2 ≤ κ ∧ 4 * (∑ C : Finset (Fin D), rate A C) / ε ≤ κ := by
    refine ⟨⌈4 * (∑ C : Finset (Fin D), rate A C) / ε⌉₊ + 2, by omega, ?_⟩
    have := Nat.le_ceil (4 * (∑ C : Finset (Fin D), rate A C) / ε)
    push_cast
    linarith
  refine ⟨κ * m₀ + 2 * LS, fun L₁ L₂ hL₁ hL₂ ι X g₀ g₁ B₁ B₂ δ₁ δ₂ hg₀ hg₁ hB₁ hB₂ hTV₁ hTV₂ => ?_⟩
  have hbad₁ := interval_frac A ustar hκ2 hm₀ hLS L₁ hL₁
  have hbad₂ := interval_frac A ustar hκ2 hm₀ hLS L₂ hL₂
  have hX₁ := tv_bad_le X B₁ L₁ hB₁ _ hbad₁ hTV₁
  have hX₂ := tv_bad_le X B₂ L₂ hB₂ _ hbad₂ hTV₂
  have hc := count_two X
    (fun x => ustar <:+: (B₁ x).take (L₁ / κ) ∧ SPGood A ε' ((B₁ x).drop (L₁ / κ)))
    (fun x => ustar <:+: (B₂ x).take (L₂ / κ) ∧ SPGood A ε' ((B₂ x).drop (L₂ / κ)))
    (fun x => LowerAt u A hE ustar z ε
      ((∑ C : Finset (Fin D), rate A C) * (2 * G + y.length + z.length))
      (g₀ x ++ B₁ x ++ g₁ x ++ B₂ x ++ y ++ z))
    (fun x hx h₁ h₂ => by
      obtain ⟨hlen₁, hdig₁⟩ := mem_wordsOfLen_iff_digits.1 (hB₁ x hx)
      obtain ⟨hlen₂, hdig₂⟩ := mem_wordsOfLen_iff_digits.1 (hB₂ x hx)
      refine lowerAt_of_good hK hEK hE u ustar huE y z hy hyu G hε hε'4 hrR (g₀ x) (g₁ x)
        (B₁ x) (B₂ x) (hg₀ x hx) (hg₁ x hx).1 (hg₁ x hx).2 hdig₁ hdig₂ (L₁ / κ) (L₂ / κ)
        (by rw [hlen₁]; exact Nat.div_le_self _ _) (by rw [hlen₂]; exact Nat.div_le_self _ _)
        ?_ ?_ h₁.1 h₁.2 h₂.1 h₂.2
      · rw [hlen₁]; exact split_facts hR0 hε hκ L₁
      · rw [hlen₂]; exact split_facts hR0 hε hκ L₂) hX₁ hX₂
  have hXn : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hXn) hc
  linarith

end Collatz.Arctic.Lower

#print axioms Collatz.Arctic.Lower.lemma_56_11_2

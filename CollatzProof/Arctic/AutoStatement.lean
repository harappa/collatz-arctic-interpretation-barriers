/-
The common hypothesis `AutoCore` carrying the probabilistic part (Definition 5.4 of the paper). **The statement is frozen** (two internal independent reviews).
It is derived from the three hypotheses of finite form (`CoreHyp.lean`) by `CoreFinal.autoCore_of_hyps`.

`Statement.ValueCore` is stated for the canonical value `Φ(can n)`; so that the dependency pair forms (Theorem 3.3) and the below-zero forms (Theorem 3.4) follow from the same hypothesis,
it is restated here for the values of general arctic automata reading binary digits.

* `autoVal u A c n := u ⊗ A_{b_1} ⊗ ⋯ ⊗ A_{b_k} ⊗ c`: the value of an automaton with entries in ℕ ∪ {−∞} that reads the binary digits of `n` from the top (without the leading 1; `binTail n`)
  (the value `V` of an automaton, Section 5 of the paper, as in Definition 5.4). The digit matrices are `A Letter.f` and `A Letter.t` (the paper's `N_0`, `N_1`).
* `AutoCore`: if the values of the automaton are finite and do not increase along steps of `T` by more than the slope `κ` (for `κ = 0`: do not increase), then for every rule `ρ`
  (of the 11 rules of 𝒯) and every `N` there are `n ≥ N` and a segment `n → T^m n` of a `T`-orbit (all points at least 2) with
  `V(n) < κ·len(n) + (number of uses of ρ)`. Justification (rewritten in the internal independent review of the statement):
  - **Dynamic and left-end rules, `κ = 0`**: Theorem 6.8 (the proof of Theorem 5.5) and the number of uses on the point family of Section 6.1
    (Proposition 6.7). On the family, `V(x_0) ≤ εℓ(x_0)` with positive probability, and the number of uses is at least `c'k` with probability → 1.
  - **Dynamic and left-end rules, `κ ≥ 1`**: the translation argument of Lemma 5.3 (the proof of Theorem 5.5 uses that the value does not increase
    only at one place, in the final contradiction; the intermediate claims about the translated value `V'` do not use that it is a translation). The minimal rate of a configuration is
    at most `κ`, and `V(x_0) ≤ (κ + C'ε)ℓ_0 + O(1)` with positive probability. Equivalently, in terms of `W := V - κ·lenT`
    (entries in ℤ, non-increasing): this is the value-level statement for entries in ℤ, obtained from Theorem 6.8 by the translation of Lemma 5.3 (if `W < 0` for infinitely many `n`, the conclusion is trivial with `m = 0`).
  - **Carry rules**: from another family (Proposition 3.7; parity words in which odd and even steps alternate) and a linear upper bound on the value. Neither the non-increase
    of the value nor the probabilistic part is used (proved without hypotheses in `ARuleMain.lean`).
  - `n ∈ {0, 1}` is not a witness (`binTail 0 = binTail 1 = []`, so `autoVal 0 = autoVal 1` is finite;
    by `T 0 = 0 < 2` and `T 1 = 2` the orbit condition forces `m = 0`, and the number of uses is 0; the comparison in the conclusion becomes `V(1) < 0`, which is false.
    The second internal review corrected a remark of the first one about a trivial witness `n = 0`.) The slope `κ` is the slope of the paper (Definition 5.4); it is unrelated to the `K` of `ValueCore` and to the length `K` of the top
    window in the proof of Theorem 5.5. The extension to ℋ needs a separate statement: `HTPDB.AutoCoreH` (through `Gen.AutoCoreG`, with the domain of `H` as a parameter).
* `CoreFinal.autoCore_of_hyps` assembles `AutoCore` from smaller hypotheses (window frequencies and a limit of max-plus products; `CoreHyp.lean`).
-/
import CollatzProof.Arctic.Statement

namespace Collatz.Arctic

open Matrix

/-- The value `u ⊗ A_{b_1} ⊗ ⋯ ⊗ A_{b_k} ⊗ c` computed by the automaton `(u, A, c)` reading the binary digits of `n` (from the top, without
the leading 1). -/
def autoVal {D : ℕ} (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (n : ℕ) : Arc :=
  u ⬝ᵥ (ev A (binTail n) *ᵥ c)

/-- The number of digits read by the automaton (for `n ≥ 1`, the number of binary digits of `n` minus 1). -/
def lenT (n : ℕ) : ℕ := (binTail n).length

/-- **The common hypothesis carrying the probabilistic part** (Definition 5.4 for $T$, proved as Theorem 5.5: the small values of Theorem 6.8, with the slope `κ` that absorbs the translation of Lemma 5.3, and the number of uses of rules on the point family). -/
def AutoCore : Prop :=
  ∀ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (κ : ℕ),
    (∀ n, 1 ≤ n → autoVal u A c n ≠ 0) →
    (∀ n, 2 ≤ n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a → autoVal u A c (T n) = Arc.fin b →
      b + κ * lenT n ≤ a + κ * lenT (T n)) →
    ∀ ρ ∈ rulesST, ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ autoVal u A c n < Arc.fin (κ * lenT n + usesOrbit ρ n m)

end Collatz.Arctic

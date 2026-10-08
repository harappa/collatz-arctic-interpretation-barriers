/-
The statement of the main theorem on the arctic barrier for the system 𝒯 (Theorem 3.1 of the paper). **This statement is frozen.**

* `canDeriv n`: the list of rules used by the canonical derivation `can n →* can (T n)` (Lemma 2.3 of the paper; the canonical-derivation lemma of Paper II).
  An even step uses `f. → .` once. An odd step uses `t. → 2.`, after which the ternary digit 2 crosses `bin'((n-1)/2)` from the low end to the high end
  (one carry rule at each position) and then uses one left-end rule at the left end.
* `uses ρ n`: the number of occurrences of the rule `ρ` in that list.
* `ValueCore`: **the hypothesis carrying the probabilistic part**. It follows from the value-level statement (Theorem 6.8: the form for arctic automata in which `Φ(can n)` does not increase along steps of `T`,
  as in the proof of Theorem 5.5, with the leading 1 absorbed into `lft` as in the canonical strings of Section 2.4) and from
  the number of uses of the rules on the point family of Section 6.1 (Propositions 6.7 and 3.7). For an arctic interpretation whose canonical value `Φ(can n)` does not increase along steps of `T`, for every rule `ρ` and every `K`
  there are `n ≥ K` and a segment `n → T^m n` of a `T`-orbit (all points of the segment are at least 2, since no rule applies to `can 1`) on which the number of uses of `ρ`
  exceeds `Φ(can n)`. It is not proved in this file: it is derived from `AutoCore`
  (`AutoBridge.lean`), which is proved without hypotheses (Theorem 5.5; see `Summary.lean` and Section 14 of the paper).
* The statement `ArcticBarrierST` of the main theorem (proved in `Main.lean` as `arctic_barrier_ST : ValueCore → ArcticBarrierST`): an arctic interpretation (of any dimension) that weakly orients all 11 rules of 𝒯 and in which every `(M_s)₀₀` is finite
  strictly orients none of the rules (Theorem 3.1 of the paper; in 𝒯 all 11 rules are used).
* Notation: the `0` of `Arc` is −∞ (so both −∞ in `Strict` means `= 0`, and finite in `Fin00` means `≠ 0`); finite values are `Arc.fin k`.
* **Frozen** after an internal independent review of the statement (which corrected the orbit condition in `ValueCore`).
-/
import CollatzProof.Arctic.Defs

namespace Collatz.Arctic

/-- The letter of a binary digit. -/
def bitL (b : ℕ) : Letter := if b = 0 then Letter.f else Letter.t

/-- The letter of a ternary digit. -/
def digL (d : ℕ) : Letter := if d = 0 then Letter.d0 else if d = 1 then Letter.d1 else Letter.d2

/-- The carry rule `b d → d' b'` (`3b + d = 2d' + b'`). -/
def aRule (b d : ℕ) : Rule := ⟨[bitL b, digL d], [digL ((3 * b + d) / 2), bitL ((3 * b + d) % 2)]⟩

/-- The left-end rule `/d → /bin'(3 + d)` (`/0 → /t`, `/1 → /ff`, `/2 → /ft`). -/
def leftRule (d : ℕ) : Rule :=
  if d = 0 then ⟨[Letter.lft, Letter.d0], [Letter.lft, Letter.t]⟩
  else if d = 1 then ⟨[Letter.lft, Letter.d1], [Letter.lft, Letter.f, Letter.f]⟩
  else ⟨[Letter.lft, Letter.d2], [Letter.lft, Letter.f, Letter.t]⟩

/-- The list of rules used while the ternary digit `d` crosses the binary digits (listed from the low end) until it reaches the left end. -/
def sweepRules : List ℕ → ℕ → List Rule
  | [], d => [leftRule d]
  | b :: bs, d => aRule b d :: sweepRules bs ((3 * b + d) / 2)

/-- The digits of `bin'(n)` listed from the low end (without the leading 1). -/
def tailBitsLSB (n : ℕ) : List ℕ := ((Nat.digits 2 n).reverse.drop 1).reverse

/-- The list of rules used by the canonical derivation `can n →* can (T n)` (`n ≥ 2`). -/
def canDeriv (n : ℕ) : List Rule :=
  if n % 2 = 0 then [⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩]
  else ⟨[Letter.t, Letter.rgt], [Letter.d2, Letter.rgt]⟩ :: sweepRules (tailBitsLSB ((n - 1) / 2)) 2

/-- The number of uses of the rule `ρ` in the canonical derivation. -/
def uses (ρ : Rule) (n : ℕ) : ℕ := (canDeriv n).count ρ

/-- The number of uses of `ρ` on the segment `n, T n, …, T^[m-1] n` of a `T`-orbit. -/
def usesOrbit (ρ : Rule) (n m : ℕ) : ℕ := ((List.range m).map (fun i => uses ρ (T^[i] n))).sum

/-- **The hypothesis carrying the probabilistic part** (Theorem 5.5 together with the number of uses of rules on the point family). -/
def ValueCore : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I →
    (∀ n, 2 ≤ n → Phi hd I (can (T n)) ≤ Phi hd I (can n)) →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ Phi hd I (can n) < Arc.fin (usesOrbit ρ n m)

/-- **Statement of the main theorem** (Theorem 3.1 of the paper, 𝒯): an arctic interpretation (of any dimension) in which every `(M_s)₀₀` is finite
and which weakly orients all rules strictly orients none of them. Proved by `arctic_barrier_ST` in `Main.lean`
(from the hypothesis `ValueCore` carrying the probabilistic part). -/
def ArcticBarrierST : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I → (∀ ρ ∈ rulesST, Weak I ρ) →
    ∀ ρ ∈ rulesST, ¬ Strict I ρ

end Collatz.Arctic

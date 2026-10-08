/-
Statements of the generic layer (Definition 7.1).
**The statements are frozen** (after an independent review).

Definitions for writing the point family, the assembly, the swap argument and the window frequencies of $T$ (the model of Section 6.1, the system $\mathcal T$) and $H$ (the model of Proposition 7.2, the systems $\mathcal H$ and $R_H$)
in a single form taking the model as an argument. The checked files for $T$ are not changed.

* `BlockModel`: the block model. The shape (the number of bits `(parityOf β).length = 8#X + 11#Y`, the number of factors of 3
  `terrasA (parityOf β) = 5#X + 7#Y`) is the same for $T$ and $H$, so `parityOf` is shared; the map `f`, the points `dom` where the canonical derivation is used,
  the **number of steps** `steps`, the residue `R` and the end constant `C` are given for each model. For $T$ the number of steps equals the number of bits, but
  for $H$ a block takes 3 or 4 steps (8 or 11 bits).
* `usesOrbitG`, `AutoRuleG`, `AutoCoreG`: `usesOrbit` and `AutoCore` with the map, the domain, the rules and the canonical derivation as arguments.
* Statements of the hypotheses (with the residue, the map and the number of steps as direct arguments, so that they can be proved without waiting for an instance of the structure):
  `HTerrasWinR` (`HTerrasWin`), `HKeyTopR` (`HKeyTop`), `SwapR` (the translation by swaps of Lemma B.5 (ii)),
  `HUseR` (the one-rule form of `HLeftUse`), `QuadR` (quadratic use of a carry rule).
* The instance `tModel` for $T$ and the agreement with the frozen statements for $T$ (`AutoCore`, `HTerrasWin`, `HKeyTop` are the same by definition,
  and `HUseR` follows from `HLeftUse`). The instances of the swap and of the carry rules for $T$ are in `ModelT.lean` (separated because it imports the proofs for $T$).
-/
import CollatzProof.Arctic.Family
import CollatzProof.Arctic.HTWKey

namespace Collatz.Arctic.Gen

open Collatz.Arctic

/-! ## Block model -/

/-- Block model. `β` is the choice of blocks (`true` = $X$, `false` = $Y$). -/
structure BlockModel where
  /-- The map (its values outside the domain `dom` do not affect any statement). -/
  f : ℕ → ℕ
  /-- The points where the canonical derivation is used (`2 ≤ n` for $T$, `HModel.HDom` for $H$). -/
  dom : ℕ → Prop
  /-- The number of steps of a block sequence (`(parityOf β).length` for $T$, `HModel.hSteps β` for $H$). -/
  steps : List Bool → ℕ
  /-- The residue `r_β` (the class modulo `2^m` of the numbers that follow `β`). -/
  R : List Bool → ℕ
  /-- The end constant `c_β`. -/
  C : List Bool → ℕ
  R_lt : ∀ β, R β < 2 ^ (parityOf β).length
  C_lt : ∀ β, C β < 3 ^ terrasA (parityOf β)
  /-- Terras consistency: the low digits of the residue of concatenated blocks are the residue of the first part. -/
  R_prefix : ∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁
  /-- Terras correspondence: `f^[steps β] (r_β + 2^m t) = c_β + 3^A t`. -/
  iter : ∀ β t, f^[steps β] (R β + 2 ^ (parityOf β).length * t) = C β + 3 ^ terrasA (parityOf β) * t
  /-- The points of the orbits of the family lie in the domain (`t ≥ 1`). -/
  orbit_dom : ∀ β t, 1 ≤ t → ∀ i < steps β, dom (f^[i] (R β + 2 ^ (parityOf β).length * t))
  /-- Images of points of the domain are at least 1 (so that the finiteness hypothesis on values applies to images). -/
  f_pos : ∀ n, dom n → 1 ≤ f n

/-! ## General forms on the side of the systems -/

/-- The number of uses of the rule `ρ` on the orbit segment `n, f n, …, f^[m-1] n`, for a map `f` and a canonical derivation `cd`
(by definition the same form as `Statement.usesOrbit`). -/
def usesOrbitG (f : ℕ → ℕ) (cd : ℕ → List Rule) (ρ : Rule) (n m : ℕ) : ℕ :=
  ((List.range m).map (fun i => (cd (f^[i] n)).count ρ)).sum

/-- The conclusion of `AutoCore` for one rule `ρ` (`AutoStatement.AutoCore` with `ρ` fixed). -/
def AutoRuleG (f : ℕ → ℕ) (dom : ℕ → Prop) (cd : ℕ → List Rule) (ρ : Rule) : Prop :=
  ∀ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (κ : ℕ),
    (∀ n, 1 ≤ n → autoVal u A c n ≠ 0) →
    (∀ n, dom n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a → autoVal u A c (f n) = Arc.fin b →
      b + κ * lenT n ≤ a + κ * lenT (f n)) →
    ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, dom (f^[i] n)) ∧ autoVal u A c n < Arc.fin (κ * lenT n + usesOrbitG f cd ρ n m)

/-- The general `AutoCore` (map `f`, domain `dom`, rules `rules`, canonical derivation `cd`). -/
def AutoCoreG (f : ℕ → ℕ) (dom : ℕ → Prop) (rules : List Rule) (cd : ℕ → List Rule) : Prop :=
  ∀ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (κ : ℕ),
    (∀ n, 1 ≤ n → autoVal u A c n ≠ 0) →
    (∀ n, dom n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a → autoVal u A c (f n) = Arc.fin b →
      b + κ * lenT n ≤ a + κ * lenT (f n)) →
    ∀ ρ ∈ rules, ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, dom (f^[i] n)) ∧ autoVal u A c n < Arc.fin (κ * lenT n + usesOrbitG f cd ρ n m)

/-- `AutoCoreG` from the conclusions for each rule. -/
theorem autoCoreG_of_rules {f : ℕ → ℕ} {dom : ℕ → Prop} {rules : List Rule} {cd : ℕ → List Rule}
    (h : ∀ ρ ∈ rules, AutoRuleG f dom cd ρ) : AutoCoreG f dom rules cd :=
  fun D u A c κ hfin hsl ρ hρ N => h ρ hρ D u A c κ hfin hsl N

/-! ## Statements of the hypotheses (with the residue, the map and the number of steps as arguments) -/

/-- `CoreHyp.HTerrasWin` with the residue as an argument: with probability close to 1, the window frequencies of the bits of an interval of block indices are close to uniform. -/
def HTerrasWinR (R : List Bool → ℕ) : Prop :=
  ∀ (β₀ : List Bool) (J : ℕ) (δ ε₀ ε : ℚ), 0 < δ → 0 < ε₀ → 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ∀ i₁ i₂ : ℕ, β₀.length ≤ i₁ → (i₁ : ℚ) + ε₀ * k ≤ i₂ → i₂ ≤ β₀.length + k →
      1 - ε ≤ Prσ β₀ k (fun β =>
        WinClose (bitsMSB (parityOf β).length (R β))
          ((parityOf β).length - blockEnd β i₂) ((parityOf β).length - blockEnd β i₁) J δ)

open Classical in
/-- `HTWKey.HKeyTop` with the residue as an argument: the law of the bits of the part formed by the `K` blocks `γ` placed at the end is close to uniform. -/
def HKeyTopR (R : List Bool → ℕ) : Prop :=
  ∀ (K : ℕ) (τ : ℚ), 0 < τ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (β₀ γ : List Bool), γ.length = K →
    ∑ u ∈ Finset.range (2 ^ (parityOf γ).length),
      abs ((∑ β ∈ (blockChoices n).filter (fun β =>
          R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length = u), wtβ β)
        - 1 / 2 ^ (parityOf γ).length) ≤ 2 * τ

/-- Translation by swaps (the block-sequence form of Lemma B.5 (ii)): modulo `2^m` (`m` is the total number of bits)
`R(φ X Y χ) = R(φ Y X χ) - 2^{m_φ + ν₂} 3^{-(A_φ + ν₃)}`, where the swap exponents `(ν₂, ν₃)` are the arguments `e₂`, `e₃`. For $T$, `ν₂ = 9`, `ν₃ = 7`; for $H$, `ν₂ = 8`, `ν₃ = 8`. -/
def SwapR (R : List Bool → ℕ) (e₂ e₃ : ℕ) : Prop :=
  ∀ φ χ : List Bool,
    ((R (φ ++ [true, false] ++ χ) : ℕ) : ZMod (2 ^ (parityOf (φ ++ [true, false] ++ χ)).length)) =
      (R (φ ++ [false, true] ++ χ) : ZMod _) -
        2 ^ ((parityOf φ).length + e₂) * ((3 : ZMod _)⁻¹) ^ (terrasA (parityOf φ) + e₃)

/-- With probability close to 1, the rule `ρ` is used at least `c k` times on the orbit of the family (`steps β` steps from `R β + 2^m t`)
(the one-rule form of `CoreHyp.HLeftUse`; for the dynamic rules this is an event of probability 1). -/
def HUseR (f : ℕ → ℕ) (R steps : List Bool → ℕ) (cd : ℕ → List Rule) (ρ : Rule) : Prop :=
  ∀ β₀ : List Bool, ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    1 - ε ≤ Prσ β₀ k (fun β => ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesOrbitG f cd ρ (R β + 2 ^ (parityOf β).length * t) (steps β) : ℚ))

/-- Quadratic use of a carry rule (the form of the output of `ARuleFamily.quad_of_family`): orbit segments whose number of uses exceeds any linear function of the length of the starting point
can be taken with starting points `≥ N`. -/
def QuadR (f : ℕ → ℕ) (dom : ℕ → Prop) (cd : ℕ → List Rule) (ρ : Rule) : Prop :=
  ∀ C N : ℕ, ∃ n, N ≤ n ∧ ∃ m, (∀ i < m, dom (f^[i] n)) ∧ C * (lenT n + 1) < usesOrbitG f cd ρ n m

/-! ## The instance for $T$ and the agreement with the frozen statements for $T$ -/

/-- The model of $T$ (Section 6.1). The fields are existing lemmas of `TModel` and `Family`. -/
def tModel : BlockModel where
  f := T
  dom := fun n => 2 ≤ n
  steps := fun β => (parityOf β).length
  R := fun β => terrasR (parityOf β)
  C := fun β => terrasC (parityOf β)
  R_lt := fun _ => terrasR_lt _
  C_lt := fun _ => terrasC_lt _
  R_prefix := fun β₁ β₂ => fam_terrasR_mod (List.prefix_append β₁ β₂)
  iter := fun _ t => terras_iter _ t
  orbit_dom := fun _ t ht i hi => terras_orbit_two_le _ t ht i hi
  f_pos := fun n hn => by unfold T; split_ifs <;> omega

/-- `AutoCore` (frozen) is an instance of the general form. -/
theorem autoCore_iff : AutoCore ↔ AutoCoreG T (fun n => 2 ≤ n) rulesST canDeriv := Iff.rfl

/-- `HTerrasWin` (frozen) is an instance of the general form. -/
theorem hTerrasWin_iff : HTerrasWin ↔ HTerrasWinR tModel.R := Iff.rfl

/-- `HKeyTop` is an instance of the general form (they differ only in the notation for absolute values). -/
theorem hKeyTop_iff : HKeyTop ↔ HKeyTopR tModel.R := by
  unfold HKeyTop HKeyTopR; rfl

/-- From `HLeftUse` (frozen), `HUseR` for each left-end rule. -/
theorem hUseR_of_hLeftUse (h : HLeftUse) (d : ℕ) (hd : d ≤ 2) :
    HUseR T tModel.R tModel.steps canDeriv (leftRule d) := by
  intro β₀
  obtain ⟨c, hc, hk⟩ := h β₀
  exact ⟨c, hc, fun ε hε => by
    obtain ⟨k₀, hk₀⟩ := hk ε hε
    exact ⟨k₀, fun k hk' => hk₀ k hk' d hd⟩⟩

end Collatz.Arctic.Gen

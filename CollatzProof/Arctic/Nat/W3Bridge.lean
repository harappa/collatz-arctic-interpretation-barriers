/-
# Natural-number interpretations of 𝒯 (Section 12.5): bridges between encodings and the point family

Bridges between three encodings; the splitting into intervals of the words of the point family of Section 6.1 (the model of `T`,
`Family.lean`); the transfer of window frequencies; and the residue coordinates.

* **Three encodings**: `binWord n : List (Fin 2)` of `ValueAuto.lean` (from the most significant end, without the leading 1), the arctic `binTail n : Word`
  (letters `f`, `t`) and `bitsMSB m r : Word`, and the `List Bool` read by the DFA of Section 12.4. The bridges are `binWord_eq_map`
  (`binWord n = (binTail n).map l2f`), `binWord_map_f2b` (`(binWord n).map f2b = (binTail n).map toB`) and
  `map_ofB_binWord` (the word for the window frequencies of Section 12.4: `((binWord n).map f2b).map ofB = binTail n`).
* **Splitting the words of the family**: `binTail_famX0_split` (`bin'(x₀) = bin'(τ) · u (F digits) · ρ (s' digits) · r_σ (m digits)`;
  unlike `Family.fam_binTail_X0` it does not use `β₀ <+: β`), `binWordB_famX0` (the `Bool` form), and for the end point
  `binTail_famX1_split`, `binWord_famX1`, `binWordB_famX1` (`bin'(h) · top K digits of ϖ · middle · r_{σ₀}`). The length `length_binTail_famT`.
* **Transfer of window frequencies**: `winClose_famX0_terras` (the interval `[a, b)` of the word of `r_σ` in `HTerrasWin` becomes the interval
  `[n - 1 + a, n - 1 + b)` of the point word), `winClose_famX0_free` (the interval `[a, b)` of the free bits `u` becomes `[K - 1 + a, K - 1 + b)`).
  The probability form `terrasWin_famX0` (from `hTerrasWin`) and the counting form `freeWin_famX0_count`.
* **A check that the composition works**: `lln_terras_famX0` (the composition of `HTerrasWin` and `lln_of_winClose` of Section 12.4,
  a law of large numbers on an interval of block indices of the Terras part, for finitely many `φ` at once) and `lln_free_famX0` (on an interval
  of the free bits, counting `u`). **The transfer works**: in the order `∃ J₀ δ' ∀ J' ≥ J₀ ∃ N₀` of `lln_of_winClose`, one can pass
  `J := J'` and `δ := δ'` to `HTerrasWin`, and the length of the interval, `L_{i₂} - L_{i₁} ≥ 8 (i₂ - i₁) ≥ 8 ε₀ k` (`blockEnd_sub_ge`), exceeds `N₀`.
  That the state at the start of the interval lies in the class (`Reach δ q₀ x`) is left to the downstream files (`W3h*.lean`).
* **Residue coordinates** (the lift `lift` of `Lift.lean` starts at residue 1, and after reading the prefix `ω.take p` the residue is
  `valW 1 (ω.take p) mod M`): `valW_append`, `valW_one_take_binWord` (the value of the prefix is `n / 2^{N - p}`),
  `valW_famX0_take_tau`, `valW_famX0_take_free`, `valW_famX0_take_t` (at the boundaries of the parts of a point of the family the values are `τ`, `τ 2^F + u`, `t`),
  `valW_binWord_famX0_zmod` (modulo `M`, `valW 1 (binWord x₀) ≡ r_σ + 2^m t`).

Only the three standard axioms (the axiom checks are in `verify/Probe.lean`). No `sorry`, `axiom` or `native_decide` is used.
-/
import CollatzProof.Arctic.Nat.Lift
import CollatzProof.Arctic.Nat.DfaLln
import CollatzProof.Arctic.FamilyDigits
import CollatzProof.Arctic.KeyFinal
import CollatzProof.Arctic.HLUMain

namespace Collatz.Arctic.NatQ5.W3a

open Collatz.Arctic

/-! ## §1 Three encodings -/

/-- A digit letter as `Fin 2` (`t ↦ 1`, all others 0; a left inverse of `bitLetter` of `ValueAuto.lean`). -/
def l2f (s : Letter) : Fin 2 := if s = Letter.t then 1 else 0

@[simp] theorem l2f_bitLetter (b : Fin 2) : l2f (bitLetter b) = b := by
  fin_cases b <;> rfl

theorem bitLetter_l2f {s : Letter} (h : s = Letter.f ∨ s = Letter.t) : bitLetter (l2f s) = s := by
  rcases h with rfl | rfl <;> rfl

/-- The letters of `binTail` are `f` or `t`. -/
theorem binTail_isDigits (n : ℕ) : ∀ s ∈ binTail n, s = Letter.f ∨ s = Letter.t := by
  intro s hs
  unfold binTail at hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  split_ifs <;> simp

/-- The letters of `bitsMSB` are `f` or `t`. -/
theorem bitsMSB_isDigits' (m r : ℕ) : ∀ s ∈ bitsMSB m r, s = Letter.f ∨ s = Letter.t :=
  bitsMSB_isDigits m r

/-- **`binWord` of `ValueAuto.lean` is the arctic `binTail` read by `l2f`**. -/
theorem binWord_eq_map (n : ℕ) : binWord n = (binTail n).map l2f := by
  rw [NatQ5.binTail_eq, List.map_map]
  conv_lhs => rw [← List.map_id (binWord n)]
  refine List.map_congr_left (fun b _ => ?_)
  simp

/-- A binary word read by `l2f` and turned back by `bitLetter` is unchanged. -/
theorem map_bitLetter_map_l2f {w : Word} (hw : ∀ s ∈ w, s = Letter.f ∨ s = Letter.t) :
    (w.map l2f).map bitLetter = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left (fun s hs => bitLetter_l2f (hw s hs))

/-- **The `Bool` encoding**: `(binWord n).map f2b = (binTail n).map toB`. -/
theorem binWord_map_f2b (n : ℕ) : (binWord n).map W3d.f2b = (binTail n).map W3d.toB := by
  rw [binWord_eq_map, List.map_map]
  refine List.map_congr_left (fun s hs => ?_)
  rcases binTail_isDigits n s hs with rfl | rfl <;> rfl

/-- A `Fin 2` word turned into letters is the word read as `Bool` and turned into letters by `ofB` (the `bitLetter` form of `map_fin2_letter` of Section 12.4). -/
theorem map_bitLetter_eq (ω : List (Fin 2)) : ω.map bitLetter = (ω.map W3d.f2b).map W3d.ofB :=
  W3d.map_fin2_letter ω

/-- **The word for the window frequencies of Section 12.4**: `((binWord n).map f2b).map ofB = binTail n`. -/
theorem map_ofB_binWord (n : ℕ) : ((binWord n).map W3d.f2b).map W3d.ofB = binTail n := by
  rw [binWord_map_f2b]
  exact W3d.map_ofB_map_toB (binTail_isDigits n)

theorem length_binWord (n : ℕ) : (binWord n).length = lenT n := by
  rw [binWord_eq_map, List.length_map]; rfl

/-! ## §2 Splitting the words of the family -/

section Split

variable {β₀ β : List Bool} {n K τ u : ℕ}

/-- `bin'(t) = bin'(τ) · u (F digits) · ρ (s' digits)` (`F = n - K - s'`). -/
theorem binTail_famT (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    binTail (famT β₀ β n K τ u) = binTail τ ++ bitsMSB (n - K - (parityOf β₀).length) u
      ++ bitsMSB (parityOf β₀).length (famRho β₀ β) := by
  set s := (parityOf β₀).length with hs
  have ht : famT β₀ β n K τ u = famRho β₀ β + 2 ^ s * (u + 2 ^ (n - K - s) * τ) := by
    unfold famT
    rw [fam_pow_split (n - K) s (by omega)]; ring
  have hpos : 1 ≤ u + 2 ^ (n - K - s) * τ :=
    le_trans (Nat.mul_le_mul Nat.one_le_two_pow hτ) (Nat.le_add_left _ _)
  rw [ht, binTail_add_mul s _ _ hpos (fam_rho_lt β₀ β), binTail_add_mul _ _ _ hτ hu]

/-- `bin'(x₀) = bin'(t) · r_σ (m digits)`. -/
theorem binTail_famX0 (hτ : 1 ≤ τ) :
    binTail (famX0 β₀ β n K τ u) = binTail (famT β₀ β n K τ u)
      ++ bitsMSB (parityOf β).length (terrasR (parityOf β)) := by
  unfold famX0
  exact binTail_add_mul _ _ _ (fam_T_pos u hτ) (terrasR_lt _)

/-- **Splitting the word of the starting point**: `bin'(x₀) = bin'(τ) · u (F digits) · ρ (s' digits) · r_σ (m digits)` (`β₀ <+: β` is not used). -/
theorem binTail_famX0_split (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    binTail (famX0 β₀ β n K τ u) = binTail τ ++ bitsMSB (n - K - (parityOf β₀).length) u
      ++ bitsMSB (parityOf β₀).length (famRho β₀ β)
      ++ bitsMSB (parityOf β).length (terrasR (parityOf β)) := by
  rw [binTail_famX0 hτ, binTail_famT hKn hτ hu]

/-- `bin'(t)` has `n - 1` digits. -/
theorem length_binTail_famT (hK : 1 ≤ K) (hKn : K + (parityOf β₀).length ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hτ2 : τ < 2 ^ K) (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    (binTail (famT β₀ β n K τ u)).length = n - 1 := by
  have h1 := fam_T_ge (β₀ := β₀) (β := β) (n := n) u hK (by omega) hτ1
  have h2 := fam_T_lt (β := β) hKn hτ2 hu
  exact fam_lenT_of_bounds h1 (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)])

/-- The form of `binWord`: `binWord x₀` is the concatenation of the images under `l2f` of the four intervals. -/
theorem binWord_famX0 (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    binWord (famX0 β₀ β n K τ u) = (binTail τ).map l2f
      ++ (bitsMSB (n - K - (parityOf β₀).length) u).map l2f
      ++ (bitsMSB (parityOf β₀).length (famRho β₀ β)).map l2f
      ++ (bitsMSB (parityOf β).length (terrasR (parityOf β))).map l2f := by
  rw [binWord_eq_map, binTail_famX0_split hKn hτ hu]
  simp only [List.map_append]

/-- The `Bool` form: the word of the point `x₀` read by the DFA of Section 12.4. -/
theorem binWordB_famX0 (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    (binWord (famX0 β₀ β n K τ u)).map W3d.f2b = (binTail τ).map W3d.toB
      ++ (bitsMSB (n - K - (parityOf β₀).length) u).map W3d.toB
      ++ (bitsMSB (parityOf β₀).length (famRho β₀ β)).map W3d.toB
      ++ (bitsMSB (parityOf β).length (terrasR (parityOf β))).map W3d.toB := by
  rw [binWord_map_f2b, binTail_famX0_split hKn hτ hu]
  simp only [List.map_append]

/-- **Splitting the word of the end point** (combining `fam_binTail_X1` and `fam_bitsMSB_varpi` of `FamilyDigits`):
`bin'(x₁) = bin'(h) · top K digits of ϖ · middle F digits · r_{σ₀}` (`h = ⌊x₁/2^n⌋`, `ϖ = x₁ mod 2^n`). -/
theorem binTail_famX1_split (hK : 1 ≤ K) (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ)
    (hA : 1 ≤ terrasA (parityOf β)) :
    binTail (famX1 β₀ β n K τ u) = binTail (famX1 β₀ β n K τ u / 2 ^ n)
      ++ bitsMSB K (famX1 β₀ β n K τ u % 2 ^ n / 2 ^ (n - K))
      ++ bitsMSB (n - K - (parityOf β₀).length)
          (famX1 β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)
      ++ bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) := by
  rw [fam_binTail_X1 u hK (by omega) hτ1 hA, fam_bitsMSB_varpi τ u hKn]
  simp only [List.append_assoc]

/-- The form of `binWord` (`Fin 2`) of the end point. -/
theorem binWord_famX1 (hK : 1 ≤ K) (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ)
    (hA : 1 ≤ terrasA (parityOf β)) :
    binWord (famX1 β₀ β n K τ u) = (binTail (famX1 β₀ β n K τ u / 2 ^ n)).map l2f
      ++ (bitsMSB K (famX1 β₀ β n K τ u % 2 ^ n / 2 ^ (n - K))).map l2f
      ++ (bitsMSB (n - K - (parityOf β₀).length)
          (famX1 β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)).map l2f
      ++ (bitsMSB (parityOf β₀).length (terrasR (parityOf β₀))).map l2f := by
  rw [binWord_eq_map, binTail_famX1_split hK hKn hτ1 hA]
  simp only [List.map_append]

/-- The `Bool` form of the end point. -/
theorem binWordB_famX1 (hK : 1 ≤ K) (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ)
    (hA : 1 ≤ terrasA (parityOf β)) :
    (binWord (famX1 β₀ β n K τ u)).map W3d.f2b = (binTail (famX1 β₀ β n K τ u / 2 ^ n)).map W3d.toB
      ++ (bitsMSB K (famX1 β₀ β n K τ u % 2 ^ n / 2 ^ (n - K))).map W3d.toB
      ++ (bitsMSB (n - K - (parityOf β₀).length)
          (famX1 β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)).map W3d.toB
      ++ (bitsMSB (parityOf β₀).length (terrasR (parityOf β₀))).map W3d.toB := by
  rw [binWord_map_f2b, binTail_famX1_split hK hKn hτ1 hA]
  simp only [List.map_append]

/-- If `β ≠ []`, there is at least one odd step (the hypothesis of `binTail_famX1_split`). -/
theorem one_le_terrasA_of_ne_nil {β : List Bool} (h : β ≠ []) : 1 ≤ terrasA (parityOf β) := by
  have := fam_terrasA_ge β
  have : 1 ≤ β.length := List.length_pos_iff.mpr h
  omega

end Split

/-! ## §3 Transfer of window frequencies -/

/-- The conditions on a point of the family (the range in which the splitting and the length of the word of `famX0` hold). -/
def FamOK (β₀ : List Bool) (n K τ u : ℕ) : Prop :=
  1 ≤ K ∧ K + (parityOf β₀).length ≤ n ∧ 2 ^ (K - 1) ≤ τ ∧ τ < 2 ^ K ∧
    u < 2 ^ (n - K - (parityOf β₀).length)

/-- The `Bool` word of the point `x₀` (the word read by the DFA of Section 12.4 from the most significant end). -/
def ptB (β₀ β : List Bool) (n K τ u : ℕ) : List Bool := (binWord (famX0 β₀ β n K τ u)).map W3d.f2b

theorem map_ofB_ptB (β₀ β : List Bool) (n K τ u : ℕ) :
    (ptB β₀ β n K τ u).map W3d.ofB = binTail (famX0 β₀ β n K τ u) := map_ofB_binWord _

/-- **Transfer of the windows of the Terras part**: the window frequencies of the interval `[a, b)` of the word of `r_σ` are those of the interval `[n - 1 + a, n - 1 + b)` of the point word. -/
theorem winClose_famX0_terras {β₀ β : List Bool} {n K τ u a b J : ℕ} {δ : ℚ} (hF : FamOK β₀ n K τ u)
    (h : WinClose (bitsMSB (parityOf β).length (terrasR (parityOf β))) a b J δ) :
    WinClose ((ptB β₀ β n K τ u).map W3d.ofB) (n - 1 + a) (n - 1 + b) J δ := by
  obtain ⟨hK, hKn, hτ1, hτ2, hu⟩ := hF
  rw [map_ofB_ptB, binTail_famX0 (by have := Nat.one_le_two_pow (n := K - 1); omega)]
  have := W3d.winClose_append_left (binTail (famT β₀ β n K τ u)) h
  rwa [length_binTail_famT hK hKn hτ1 hτ2 hu] at this

/-- **Transfer of the windows of the free bits**: the window frequencies of the interval `[a, b)` of the word of `u` are those of the interval `[K - 1 + a, K - 1 + b)` of the point word. -/
theorem winClose_famX0_free {β₀ β : List Bool} {n K τ u a b J : ℕ} {δ : ℚ} (hF : FamOK β₀ n K τ u)
    (h : WinClose (bitsMSB (n - K - (parityOf β₀).length) u) a b J δ) :
    WinClose ((ptB β₀ β n K τ u).map W3d.ofB) (K - 1 + a) (K - 1 + b) J δ := by
  obtain ⟨hK, hKn, hτ1, hτ2, hu⟩ := hF
  have hτ : 1 ≤ τ := by have := Nat.one_le_two_pow (n := K - 1); omega
  rw [map_ofB_ptB, binTail_famX0_split hKn hτ hu]
  have h1 := W3d.winClose_append_left (binTail τ) h
  have h2 := W3d.winClose_append_right (bitsMSB (parityOf β₀).length (famRho β₀ β)
    ++ bitsMSB (parityOf β).length (terrasR (parityOf β))) h1
  rw [fam_binTail_tau_length hK hτ1 hτ2] at h2
  simpa only [List.append_assoc] using h2

/-- An interval `[i₁, i₂)` of blocks (`i₂ ≤ |β|`) has at least 8 (i₂ - i₁) bits (each block has at least 8 steps). -/
theorem blockEnd_sub_ge (β : List Bool) {i₁ i₂ : ℕ} (h12 : i₁ ≤ i₂) (h2 : i₂ ≤ β.length) :
    blockEnd β i₁ + 8 * (i₂ - i₁) ≤ blockEnd β i₂ := by
  unfold blockEnd
  have e : β.take i₂ = β.take i₁ ++ (β.take i₂).drop i₁ := by
    conv_lhs => rw [← List.take_append_drop i₁ (β.take i₂)]
    rw [List.take_take, Nat.min_eq_left h12]
  rw [e, fam_parityOf_append, List.length_append]
  have hl : ((β.take i₂).drop i₁).length = i₂ - i₁ := by
    rw [List.length_drop, List.length_take, Nat.min_eq_left h2]
  have := (parityOf_length_bounds ((β.take i₂).drop i₁)).1
  rw [hl] at this
  omega

/-- **The probability form** (from `hTerrasWin`): the probability that the window frequencies of the point word on the interval of block indices `[i₁, i₂)` of the Terras part are within
`δ` of uniform is at least `1 - ε` if `k` is large (uniformly in the interval, `n`, `K`, `τ`, `u`). -/
theorem terrasWin_famX0 (β₀ : List Bool) (J : ℕ) (δ ε₀ ε : ℚ) (hδ : 0 < δ) (hε₀ : 0 < ε₀) (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i₁ i₂ : ℕ, β₀.length ≤ i₁ → (i₁ : ℚ) + ε₀ * k ≤ i₂ → i₂ ≤ β₀.length + k →
      1 - ε ≤ Prσ β₀ k (fun β => ∀ n K τ u : ℕ, FamOK β₀ n K τ u →
        WinClose ((ptB β₀ β n K τ u).map W3d.ofB)
          (n - 1 + ((parityOf β).length - blockEnd β i₂)) (n - 1 + ((parityOf β).length - blockEnd β i₁))
          J δ) := by
  obtain ⟨k₀, hk₀⟩ := hTerrasWin β₀ J δ ε₀ ε hδ hε₀ hε
  refine ⟨k₀, fun k hk i₁ i₂ h1 h2 h3 => ?_⟩
  refine le_trans (hk₀ k hk i₁ i₂ h1 h2 h3) (Prσ_mono β₀ k (fun β' _ hw n K τ u hF => ?_))
  exact winClose_famX0_terras hF hw

open Classical in
/-- **The counting form** (from `CoreU.win_bad_count`): on an interval `[a, b) ⊆ [0, F)` of the free bits (`b - a ≥ M₀`), at most `ε 2^F` values `u` give a point word
whose window frequencies are not close to uniform. -/
theorem freeWin_famX0_count (J : ℕ) (δ ε : ℚ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ (β₀ β : List Bool) (n K τ a b : ℕ), 1 ≤ K → K + (parityOf β₀).length ≤ n →
      2 ^ (K - 1) ≤ τ → τ < 2 ^ K → a ≤ b → b ≤ n - K - (parityOf β₀).length → M₀ ≤ b - a →
      (((Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
          ¬ WinClose ((ptB β₀ β n K τ u).map W3d.ofB) (K - 1 + a) (K - 1 + b) J δ)).card : ℚ) ≤
        ε * 2 ^ (n - K - (parityOf β₀).length) := by
  obtain ⟨M₀, hM₀⟩ := win_bad_count J δ ε hδ hε
  refine ⟨M₀, fun β₀ β n K τ a b hK hKn hτ1 hτ2 hab hbF hM => ?_⟩
  refine le_trans ?_ (hM₀ _ a b hab hbF hM)
  have hsub : (Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
        ¬ WinClose ((ptB β₀ β n K τ u).map W3d.ofB) (K - 1 + a) (K - 1 + b) J δ) ⊆
      (Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
        ¬ WinClose (bitsMSB (n - K - (parityOf β₀).length) u) a b J δ) := by
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨hu.1, fun hw => hu.2 ?_⟩
    exact winClose_famX0_free ⟨hK, hKn, hτ1, hτ2, Finset.mem_range.mp hu.1⟩ hw
  exact_mod_cast Finset.card_le_card hsub

/-! ## §4 A check that the composition works: `HTerrasWin` and `lln_of_winClose` -/

section LLN

variable {S : Type*} [Fintype S] [DecidableEq S] {δ : S → Bool → S} (J : ℕ)

/-- A common positive lower bound for finitely many positive rationals. -/
theorem exists_pos_le_all {ι : Type*} [Fintype ι] (f : ι → ℚ) (hf : ∀ i, 0 < f i) :
    ∃ c : ℚ, 0 < c ∧ ∀ i, c ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty f, ?_, fun i => Finset.inf'_le f (Finset.mem_univ i)⟩
    exact (Finset.lt_inf'_iff _).2 (fun i _ => hf i)

/-- The positions on the point word of an interval of the Terras part (the start `a` and the end `b` of the interval). -/
def terA (β : List Bool) (n i₂ : ℕ) : ℕ := n - 1 + ((parityOf β).length - blockEnd β i₂)

def terB (β : List Bool) (n i₁ : ℕ) : ℕ := n - 1 + ((parityOf β).length - blockEnd β i₁)

/-- **Moving `HTerrasWin` into the hypothesis of `lln_of_winClose`** (Lemma 12.16 (i): Theorem 12.13 (iii) on the points of the family):
for the class of a recurrent state `q₀`, bounded `φ i` (finitely many `i`) and `ε > 0`, once the first blocks `β₀`, the width `ε₀ k` of the interval and the failure
probability `η` are fixed, for `k` large, with probability at least `1 - η`, on the interval `[terA, terB]` of the point word that corresponds to the interval of block indices
`[i₁, i₂)`, from every starting state in the class, for all `i` and all prefixes the sum is within `ε (terB - terA)` of `statMean · length`
(uniformly in `n`, `K`, `τ`, `u` and the interval). -/
theorem lln_terras_famX0 {ι : Type*} [Fintype ι] {φ : ι → S → List Bool → ℝ} {q₀ : S}
    (hrec : Dfa.Recurrent δ q₀) {C : ℝ} (hC : ∀ i x v, |φ i x v| ≤ C) (ε : ℝ) (hε : 0 < ε)
    (β₀ : List Bool) (ε₀ η : ℚ) (hε₀ : 0 < ε₀) (hη : 0 < η) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i₁ i₂ : ℕ, β₀.length ≤ i₁ → (i₁ : ℚ) + ε₀ * k ≤ i₂ → i₂ ≤ β₀.length + k →
      1 - η ≤ Prσ β₀ k (fun β => ∀ n K τ u : ℕ, FamOK β₀ n K τ u → ∀ i x, Dfa.Reach δ q₀ x →
        ∀ p, terA β n i₂ ≤ p → p ≤ terB β n i₁ →
          |W3d.wsum δ J (φ i) x ((ptB β₀ β n K τ u).drop (terA β n i₂)) (p - terA β n i₂)
            - W3d.statMean δ J (φ i) q₀ * ((p - terA β n i₂ : ℕ) : ℝ)| ≤
            ε * ((terB β n i₁ - terA β n i₂ : ℕ) : ℝ)) := by
  have hlln := fun i => W3d.lln_of_winClose J hrec (hC i) ε hε
  choose J₀ δ' hδ' hJ using hlln
  set J' := Finset.univ.sup J₀ with hJ'
  obtain ⟨δ'', hδ''0, hδ''le⟩ := exists_pos_le_all δ' hδ'
  have hN := fun i => hJ i J' (Finset.le_sup (f := J₀) (Finset.mem_univ i))
  choose N₀ hN₀ using hN
  set N := Finset.univ.sup N₀ with hNdef
  obtain ⟨k₁, hk₁⟩ := terrasWin_famX0 β₀ J' δ'' ε₀ η hδ''0 hε₀ hη
  refine ⟨max k₁ ⌈(N : ℚ) / (8 * ε₀)⌉₊, fun k hk i₁ i₂ h1 h2 h3 => ?_⟩
  refine le_trans (hk₁ k (le_of_max_le_left hk) i₁ i₂ h1 h2 h3)
    (Prσ_mono β₀ k (fun β' hβ' hw n K τ u hF i x hx p hp1 hp2 => ?_))
  set β := β₀ ++ β' with hβ
  have hβlen : β.length = β₀.length + k := by
    rw [hβ, List.length_append, length_of_mem_blockChoices hβ']
  -- the width of the interval
  have hk0 : (0 : ℚ) ≤ ε₀ * k := by positivity
  have h12 : i₁ ≤ i₂ := by
    have : (i₁ : ℚ) ≤ i₂ := by linarith
    exact_mod_cast this
  have hge := blockEnd_sub_ge β h12 (by omega)
  have hle := blockEnd_le_full β i₂
  have hwidth : terB β n i₁ - terA β n i₂ = blockEnd β i₂ - blockEnd β i₁ := by
    unfold terA terB; omega
  have hNle : N₀ i ≤ terB β n i₁ - terA β n i₂ := by
    rw [hwidth]
    have hNi : N₀ i ≤ N := Finset.le_sup (f := N₀) (Finset.mem_univ i)
    have hkc : (N : ℚ) / (8 * ε₀) ≤ k := by
      have := Nat.le_ceil ((N : ℚ) / (8 * ε₀))
      have hk' : (⌈(N : ℚ) / (8 * ε₀)⌉₊ : ℚ) ≤ k := by exact_mod_cast le_of_max_le_right hk
      linarith
    have h8 : (N : ℚ) ≤ 8 * ((i₂ : ℚ) - i₁) := by
      rw [div_le_iff₀ (by positivity)] at hkc
      nlinarith
    have h8' : N ≤ 8 * (i₂ - i₁) := by
      have : ((i₂ - i₁ : ℕ) : ℚ) = (i₂ : ℚ) - i₁ := by rw [Nat.cast_sub h12]
      have h8q : (N : ℚ) ≤ 8 * ((i₂ - i₁ : ℕ) : ℚ) := by rw [this]; exact h8
      exact_mod_cast h8q
    omega
  have hwin := hw n K τ u hF
  have hwin' := W3d.winClose_mono hwin (hδ''le i)
  exact hN₀ i (ptB β₀ β n K τ u) (terA β n i₂) (terB β n i₁) hwin' hNle x hx p hp1 hp2

open Classical in
/-- **The law of large numbers on an interval of the free bits** (Lemma 12.16 (ii): Theorem 12.13 (iii) on the points of the family, counting `u`): on an interval
`[a, b) ⊆ [0, F)` of the free bits (`b - a ≥ N₀`), at most `η 2^F` values `u` fail the estimate on the interval `[K - 1 + a, K - 1 + b]` of the point word for some starting state in the class,
some `i` or some prefix. -/
theorem lln_free_famX0 {ι : Type*} [Fintype ι] {φ : ι → S → List Bool → ℝ} {q₀ : S}
    (hrec : Dfa.Recurrent δ q₀) {C : ℝ} (hC : ∀ i x v, |φ i x v| ≤ C) (ε : ℝ) (hε : 0 < ε)
    (η : ℚ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ (β₀ β : List Bool) (n K τ a b : ℕ), 1 ≤ K → K + (parityOf β₀).length ≤ n →
      2 ^ (K - 1) ≤ τ → τ < 2 ^ K → a ≤ b → b ≤ n - K - (parityOf β₀).length → N₀ ≤ b - a →
      (((Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
          ¬ ∀ i x, Dfa.Reach δ q₀ x → ∀ p, K - 1 + a ≤ p → p ≤ K - 1 + b →
            |W3d.wsum δ J (φ i) x ((ptB β₀ β n K τ u).drop (K - 1 + a)) (p - (K - 1 + a))
              - W3d.statMean δ J (φ i) q₀ * ((p - (K - 1 + a) : ℕ) : ℝ)| ≤ ε * ((b - a : ℕ) : ℝ))).card : ℚ) ≤
        η * 2 ^ (n - K - (parityOf β₀).length) := by
  have hlln := fun i => W3d.lln_of_winClose J hrec (hC i) ε hε
  choose J₀ δ' hδ' hJ using hlln
  set J' := Finset.univ.sup J₀ with hJ'
  obtain ⟨δ'', hδ''0, hδ''le⟩ := exists_pos_le_all δ' hδ'
  have hN := fun i => hJ i J' (Finset.le_sup (f := J₀) (Finset.mem_univ i))
  choose N₀ hN₀ using hN
  set N := Finset.univ.sup N₀ with hNdef
  obtain ⟨M₀, hM₀⟩ := freeWin_famX0_count J' δ'' η hδ''0 hη
  refine ⟨max N M₀, fun β₀ β n K τ a b hK hKn hτ1 hτ2 hab hbF hNb => ?_⟩
  refine le_trans ?_ (hM₀ β₀ β n K τ a b hK hKn hτ1 hτ2 hab hbF (le_of_max_le_right hNb))
  have hsub : (Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
        ¬ ∀ i x, Dfa.Reach δ q₀ x → ∀ p, K - 1 + a ≤ p → p ≤ K - 1 + b →
          |W3d.wsum δ J (φ i) x ((ptB β₀ β n K τ u).drop (K - 1 + a)) (p - (K - 1 + a))
            - W3d.statMean δ J (φ i) q₀ * ((p - (K - 1 + a) : ℕ) : ℝ)| ≤ ε * ((b - a : ℕ) : ℝ)) ⊆
      (Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
        ¬ WinClose ((ptB β₀ β n K τ u).map W3d.ofB) (K - 1 + a) (K - 1 + b) J' δ'') := by
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨hu.1, fun hw => hu.2 (fun i x hx p hp1 hp2 => ?_)⟩
    have hwin' := W3d.winClose_mono hw (hδ''le i)
    have hNi : N₀ i ≤ N := Finset.le_sup (f := N₀) (Finset.mem_univ i)
    have hlen : N₀ i ≤ K - 1 + b - (K - 1 + a) := by have := le_of_max_le_left hNb; omega
    have := hN₀ i (ptB β₀ β n K τ u) (K - 1 + a) (K - 1 + b) hwin' hlen x hx p hp1 hp2
    rwa [show K - 1 + b - (K - 1 + a) = b - a by omega] at this
  exact_mod_cast Finset.card_le_card hsub

end LLN

/-! ## §5 Residue coordinates -/

/-- `valW` composes along concatenation. -/
theorem valW_append (r : ℕ) (w₁ w₂ : List (Fin 2)) : valW r (w₁ ++ w₂) = valW (valW r w₁) w₂ := by
  induction w₁ generalizing r with
  | nil => rfl
  | cons b w ih => simp only [List.cons_append, valW]; exact ih _

/-- `valW 0 w < 2^{|w|}`. -/
theorem valW_zero_lt (w : List (Fin 2)) : valW 0 w < 2 ^ w.length := by
  have key : ∀ (w : List (Fin 2)) (r : ℕ), valW r w < (r + 1) * 2 ^ w.length := by
    intro w
    induction w with
    | nil => intro r; simp [valW]
    | cons b w ih =>
      intro r
      simp only [valW, List.length_cons]
      have hb : (b : ℕ) ≤ 1 := Nat.lt_succ_iff.mp b.isLt
      have := ih (2 * r + b)
      calc valW (2 * r + b) w < (2 * r + b + 1) * 2 ^ w.length := this
        _ ≤ (2 * r + 2) * 2 ^ w.length := Nat.mul_le_mul_right _ (by omega)
        _ = (r + 1) * 2 ^ (w.length + 1) := by rw [pow_succ]; ring
  simpa using key w 0

/-- The value of a `bitsMSB` word: `valW r ((bitsMSB m x).map l2f) = r 2^m + x` (`x < 2^m`). -/
theorem valW_map_bitsMSB (r m x : ℕ) (hx : x < 2 ^ m) :
    valW r ((bitsMSB m x).map l2f) = r * 2 ^ m + x := by
  induction m generalizing r x with
  | zero => simp at hx; subst hx; simp [bitsMSB, valW]
  | succ m ih =>
    have hq : x / 2 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hx; omega
    have hdm := Nat.mod_add_div x (2 ^ m)
    simp only [bitsMSB, List.map_cons, valW]
    rw [ih _ _ (Nat.mod_lt _ (by positivity))]
    have hbit : ((l2f (bitL (x / 2 ^ m % 2)) : Fin 2) : ℕ) = x / 2 ^ m := by
      have h01 : x / 2 ^ m = 0 ∨ x / 2 ^ m = 1 := by generalize x / 2 ^ m = q at hq; omega
      rcases h01 with h | h <;> simp [h, bitL, l2f]
    rw [hbit, pow_succ]
    calc (2 * r + x / 2 ^ m) * 2 ^ m + x % 2 ^ m
        = 2 * r * 2 ^ m + (x % 2 ^ m + 2 ^ m * (x / 2 ^ m)) := by ring
      _ = r * (2 ^ m * 2) + x := by rw [hdm]; ring

/-- **The value of a prefix**: `valW 1 ((binWord n).take p) = n / 2^{|binWord n| - p}`
(the residue coordinate of the lift at position `p` is the residue of this value). -/
theorem valW_one_take_binWord (n p : ℕ) (hn : 1 ≤ n) :
    valW 1 ((binWord n).take p) = n / 2 ^ ((binWord n).length - p) := by
  have h := valW_binWord n hn
  have e : binWord n = (binWord n).take p ++ (binWord n).drop p := (List.take_append_drop p _).symm
  rw [e, valW_append, valW_eq] at h
  have hlt := valW_zero_lt ((binWord n).drop p)
  rw [List.length_drop] at h hlt
  have key : ∀ V R k m : ℕ, V * 2 ^ k + R = m → R < 2 ^ k → V = m / 2 ^ k := by
    intro V R k m hm hR
    subst hm
    rw [mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hR, add_zero]
  exact key _ _ _ _ h hlt

/-- The residue at a boundary of the parts of a point of the family: after reading the part `τ`, the value is `τ`. -/
theorem valW_famX0_take_tau {β₀ β : List Bool} {n K τ u : ℕ} (hF : FamOK β₀ n K τ u) :
    valW 1 ((binWord (famX0 β₀ β n K τ u)).take (K - 1)) = τ := by
  obtain ⟨hK, hKn, hτ1, hτ2, hu⟩ := hF
  have hτ : 1 ≤ τ := by have := Nat.one_le_two_pow (n := K - 1); omega
  rw [binWord_famX0 hKn hτ hu, List.append_assoc, List.append_assoc,
    List.take_append_of_le_length (by rw [List.length_map, fam_binTail_tau_length hK hτ1 hτ2]),
    List.take_of_length_le (by rw [List.length_map, fam_binTail_tau_length hK hτ1 hτ2]),
    ← binWord_eq_map, valW_binWord τ hτ]

/-- The residue at a boundary of the parts of a point of the family: after reading up to the free bits, the value is `τ 2^F + u`. -/
theorem valW_famX0_take_free {β₀ β : List Bool} {n K τ u : ℕ} (hF : FamOK β₀ n K τ u) :
    valW 1 ((binWord (famX0 β₀ β n K τ u)).take (K - 1 + (n - K - (parityOf β₀).length))) =
      τ * 2 ^ (n - K - (parityOf β₀).length) + u := by
  obtain ⟨hK, hKn, hτ1, hτ2, hu⟩ := hF
  have hτ : 1 ≤ τ := by have := Nat.one_le_two_pow (n := K - 1); omega
  have hl1 : ((binTail τ).map l2f).length = K - 1 := by
    rw [List.length_map, fam_binTail_tau_length hK hτ1 hτ2]
  have hl2 : ((bitsMSB (n - K - (parityOf β₀).length) u).map l2f).length =
      n - K - (parityOf β₀).length := by rw [List.length_map, bitsMSB_length]
  rw [binWord_famX0 hKn hτ hu, List.append_assoc,
    List.take_append_of_le_length (by rw [List.length_append, hl1, hl2]),
    List.take_of_length_le (by rw [List.length_append, hl1, hl2]), valW_append, ← binWord_eq_map,
    valW_binWord τ hτ, valW_map_bitsMSB _ _ _ hu]

/-- The residue at a boundary of the parts of a point of the family: after reading all of `t`, the value is `t`. -/
theorem valW_famX0_take_t {β₀ β : List Bool} {n K τ u : ℕ} (hF : FamOK β₀ n K τ u) :
    valW 1 ((binWord (famX0 β₀ β n K τ u)).take (n - 1)) = famT β₀ β n K τ u := by
  obtain ⟨hK, hKn, hτ1, hτ2, hu⟩ := hF
  have hτ : 1 ≤ τ := by have := Nat.one_le_two_pow (n := K - 1); omega
  have hlen := length_binTail_famT (β := β) hK hKn hτ1 hτ2 hu
  rw [binWord_eq_map, binTail_famX0 hτ, List.map_append,
    List.take_append_of_le_length (by rw [List.length_map, hlen]),
    List.take_of_length_le (by rw [List.length_map, hlen]), ← binWord_eq_map,
    valW_binWord _ (fam_T_pos u hτ)]

/-- **The residue of `x₀`** (the value of the residue coordinate of the lift, modulo `M`): `valW 1 (binWord x₀) ≡ r_σ + 2^m t`. For 𝒯, the persistent class
`3 ∤ x₀` depends on the free bits of `t` (`M = 3`). -/
theorem valW_binWord_famX0_zmod (M : ℕ) {β₀ β : List Bool} {n K τ u : ℕ} (hτ : 1 ≤ τ) :
    ((valW 1 (binWord (famX0 β₀ β n K τ u)) : ℕ) : ZMod M) =
      (terrasR (parityOf β) : ZMod M) + 2 ^ (parityOf β).length * (famT β₀ β n K τ u : ZMod M) := by
  have hx : 1 ≤ famX0 β₀ β n K τ u := by
    unfold famX0
    have := fam_T_pos (β₀ := β₀) (β := β) (n := n) (K := K) u hτ
    have : 1 ≤ 2 ^ (parityOf β).length * famT β₀ β n K τ u := Nat.mul_pos (by positivity) this
    omega
  rw [valW_binWord _ hx]
  unfold famX0
  push_cast
  ring

end Collatz.Arctic.NatQ5.W3a

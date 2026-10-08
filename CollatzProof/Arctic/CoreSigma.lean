/-
Existence lemma on the side of `σ` for the assembly of Theorem 6.8 of the paper: the events (S1)–(S3) for the block sequence in the proof of Theorem 6.8.
Fix the initial block sequence `β₀`; the remaining `k` blocks `β` can be chosen so that the following three hold simultaneously (`k` can
be taken arbitrarily large).

1. On each interval `[|β₀| + ⌊jk/M⌋, |β₀| + ⌊(j+1)k/M⌋)` of block indices (`j < M`), the windows of length `J` of the digits of `r_σ`, written from
   the most significant end, are `δ`-close to uniform (hypothesis `HTerrasWin`, Theorem B.8).
2. For every `t ≥ 2^m`, along the canonical derivations from `x₀ = r_σ + 2^m t` to `T^m x₀`, each of the three left-end rules
   (`d = 0, 1, 2`) is used at least `c_L k` times (hypothesis `HLeftUse`, Proposition 6.7 (ii)).
3. Expansion `2^{m + ⌈c_e k⌉} ≤ 3^A` (`fam_expansion_lln`).

The constants `c_L` (the constant of `HLeftUse` for `β₀`) and `c_e` (the constant of `fam_expansion_lln`) depend only on `β₀` (not on `J`, `δ`, `M`,
`N`).

The proof is a union bound: if `k ≥ 2M`, each interval has width at least `k/(2M)`, so we apply `HTerrasWin` with `ε₀ = 1/(2M)`,
`ε = 1/(4M)` to each interval (with a `k₀` uniform over the intervals), `HLeftUse` with `ε = 1/12` to `d = 0, 1, 2`, and
the expansion with `ε = 1/8`. All events hold together with probability at least `1 - M/(4M) - 3/12 - 1/8 = 3/8 > 0`, so
`exists_of_Prσ_pos` gives `β`.

* `sig_congr`, `sig_one_le`, `sig_and`, `sig_forall_lt`: union bounds for `Prσ` (total weight 1).
  `Prσ` is a filter under `open Classical`, so here we do not unfold its definition and use only `Prσ_and_ge` and `fam_pr_ge`.
* `sig_div_ge`, `sig_width`, `sig_upper`, `sig_gap`: bounds on the integer divisions at the ends of the intervals.
* `sigma_good`: the main statement.
-/
import CollatzProof.Arctic.CoreProb
import CollatzProof.Arctic.FamilyExp

namespace Collatz.Arctic

/-! ## Union bounds for `Prσ` -/

/-- Equivalent events have equal probability. -/
theorem sig_congr (β₀ : List Bool) (k : ℕ) {E F : List Bool → Prop} (h : ∀ β, E β ↔ F β) :
    Prσ β₀ k E = Prσ β₀ k F := by
  have hEF : E = F := funext fun β => propext (h β)
  rw [hEF]

/-- An event that always holds has probability at least 1 (`fam_pr_ge` applied with an empty bad event). -/
theorem sig_one_le (β₀ : List Bool) (k : ℕ) {E : List Bool → Prop} (h : ∀ β, E β) :
    1 ≤ Prσ β₀ k E := by
  have := fam_pr_ge β₀ k E (fun _ => 0) 0 (fun _ _ => le_refl 0)
    (fun β _ hn => absurd (h _) hn) (by simp)
  simpa using this

/-- Union bound for two events (total weight 1). -/
theorem sig_and (β₀ : List Bool) (k : ℕ) (E₁ E₂ : List Bool → Prop) :
    Prσ β₀ k E₁ + Prσ β₀ k E₂ - 1 ≤ Prσ β₀ k (fun β => E₁ β ∧ E₂ β) := by
  have := Prσ_and_ge β₀ k E₁ E₂ wtβ_nonneg
  rwa [(fam_moments k).1] at this

/-- Union bound for finitely many events: if each has probability at least `1 - η`, then `n` of them hold simultaneously with probability at least `1 - nη`. -/
theorem sig_forall_lt (β₀ : List Bool) (k : ℕ) (E : ℕ → List Bool → Prop) (η : ℚ) :
    ∀ n : ℕ, (∀ j < n, 1 - η ≤ Prσ β₀ k (E j)) →
      1 - n * η ≤ Prσ β₀ k (fun β => ∀ j < n, E j β) := by
  intro n
  induction n with
  | zero =>
    intro _
    simpa using sig_one_le β₀ k (E := fun β => ∀ j < 0, E j β)
      (fun _ j hj => absurd hj (Nat.not_lt_zero j))
  | succ n ih =>
    intro h
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    have h3 := sig_and β₀ k (fun β => ∀ j < n, E j β) (E n)
    have h4 : Prσ β₀ k (fun β => ∀ j < n + 1, E j β)
        = Prσ β₀ k (fun β => (∀ j < n, E j β) ∧ E n β) := by
      apply sig_congr
      intro β
      constructor
      · intro hb
        exact ⟨fun j hj => hb j (by omega), hb n (by omega)⟩
      · rintro ⟨hb, hn⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hb j hj
        · exact hn
    rw [h4]
    push_cast
    linarith

/-! ## Bounds at the ends of the intervals -/

/-- If `2M ≤ k` then `k ≤ 2 M ⌊k/M⌋`. -/
theorem sig_div_ge (k M : ℕ) (hM : 1 ≤ M) (hk : 2 * M ≤ k) : k ≤ 2 * (M * (k / M)) := by
  have h1 := Nat.div_add_mod k M
  have h2 := Nat.mod_lt k (by omega : 0 < M)
  generalize M * (k / M) = P at h1 ⊢
  omega

/-- Width of an interval: `⌊jk/M⌋ + ⌊k/M⌋ ≤ ⌊(j+1)k/M⌋`. -/
theorem sig_width (j k M : ℕ) : j * k / M + k / M ≤ (j + 1) * k / M := by
  rw [add_mul, one_mul]
  exact Nat.div_add_div_le_add_div

/-- Right end of an interval: if `j < M` then `⌊(j+1)k/M⌋ ≤ k`. -/
theorem sig_upper (j k M : ℕ) (hj : j < M) : (j + 1) * k / M ≤ k := by
  calc (j + 1) * k / M ≤ M * k / M := Nat.div_le_div_right (Nat.mul_le_mul_right k hj)
    _ = k := Nat.mul_div_cancel_left k (by omega)

/-- The width condition of `HTerrasWin`: if `2M ≤ k`, the interval `[b + ⌊jk/M⌋, b + ⌊(j+1)k/M⌋)` has width at least `k/(2M)`. -/
theorem sig_gap (b j k M : ℕ) (hM : 1 ≤ M) (hk : 2 * M ≤ k) :
    ((b + j * k / M : ℕ) : ℚ) + 1 / (2 * (M : ℚ)) * k ≤ ((b + (j + 1) * k / M : ℕ) : ℚ) := by
  have h1 := sig_div_ge k M hM hk
  have h2 := sig_width j k M
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have h1q : (k : ℚ) ≤ 2 * ((M : ℚ) * ((k / M : ℕ) : ℚ)) := by exact_mod_cast h1
  have h2q : ((j * k / M : ℕ) : ℚ) + ((k / M : ℕ) : ℚ) ≤ (((j + 1) * k / M : ℕ) : ℚ) := by
    exact_mod_cast h2
  have h3 : 1 / (2 * (M : ℚ)) * k ≤ ((k / M : ℕ) : ℚ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have e1 : ((b + j * k / M : ℕ) : ℚ) = (b : ℚ) + ((j * k / M : ℕ) : ℚ) := by push_cast; ring
  have e2 : ((b + (j + 1) * k / M : ℕ) : ℚ) = (b : ℚ) + (((j + 1) * k / M : ℕ) : ℚ) := by
    push_cast; ring
  rw [e1, e2]
  linarith

/-! ## Main statement -/

/-- **Existence on the side of `σ`** (the events for the block sequence in the proof of Theorem 6.8). Fixing the initial block sequence `β₀`, there are constants
`c_L, c_e > 0` (depending only on `β₀`) such that for all `J`, `δ > 0`, `M ≥ 1` and `N` there are `k ≥ N` and a choice `β` of
`k` blocks such that for `β₀ ++ β` (1) the window frequencies on the `M` intervals, (2) the uses of the left-end rules and (3) the expansion
hold simultaneously. -/
theorem sigma_good (hTW : HTerrasWin) (hLU : HLeftUse) (β₀ : List Bool) :
    ∃ cL : ℚ, 0 < cL ∧ ∃ ce : ℚ, 0 < ce ∧ ∀ (J : ℕ) (δ : ℚ), 0 < δ → ∀ M : ℕ, 1 ≤ M →
      ∀ N : ℕ, ∃ k, N ≤ k ∧ ∃ β : List Bool, β.length = k ∧
      (∀ j < M, WinClose (bitsMSB (parityOf (β₀ ++ β)).length (terrasR (parityOf (β₀ ++ β))))
          ((parityOf (β₀ ++ β)).length - blockEnd (β₀ ++ β) (β₀.length + (j + 1) * k / M))
          ((parityOf (β₀ ++ β)).length - blockEnd (β₀ ++ β) (β₀.length + j * k / M)) J δ) ∧
      (∀ d ≤ 2, ∀ t : ℕ, 2 ^ (parityOf (β₀ ++ β)).length ≤ t →
          cL * k ≤ (usesOrbit (leftRule d)
            (terrasR (parityOf (β₀ ++ β)) + 2 ^ (parityOf (β₀ ++ β)).length * t)
            (parityOf (β₀ ++ β)).length : ℚ)) ∧
      2 ^ ((parityOf (β₀ ++ β)).length + ⌈ce * k⌉₊) ≤ 3 ^ terrasA (parityOf (β₀ ++ β)) := by
  obtain ⟨c, hc, hLc⟩ := hLU β₀
  obtain ⟨ce, hce, hE⟩ := fam_expansion_lln
  refine ⟨c, hc, ce, hce, ?_⟩
  intro J δ hδ M hM N
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  obtain ⟨k₁, hk₁⟩ := hTW β₀ J δ (1 / (2 * (M : ℚ))) (1 / (4 * (M : ℚ))) hδ
    (by positivity) (by positivity)
  obtain ⟨k₂, hk₂⟩ := hLc (1 / 12) (by norm_num)
  obtain ⟨k₃, hk₃⟩ := hE β₀ (1 / 8) (by norm_num)
  -- `k` is at least `N`, `2M` and each `k₀` (take the sum)
  obtain ⟨k, hkN, hkM, hk1, hk2, hk3⟩ : ∃ k, N ≤ k ∧ 2 * M ≤ k ∧ k₁ ≤ k ∧ k₂ ≤ k ∧ k₃ ≤ k :=
    ⟨N + 2 * M + k₁ + k₂ + k₃, by omega, by omega, by omega, by omega, by omega⟩
  -- (1) window frequencies: `M` intervals
  have pW := sig_forall_lt β₀ k (fun j β =>
      WinClose (bitsMSB (parityOf β).length (terrasR (parityOf β)))
        ((parityOf β).length - blockEnd β (β₀.length + (j + 1) * k / M))
        ((parityOf β).length - blockEnd β (β₀.length + j * k / M)) J δ)
    (1 / (4 * (M : ℚ))) M (fun j hj =>
      hk₁ k hk1 (β₀.length + j * k / M) (β₀.length + (j + 1) * k / M) (Nat.le_add_right _ _)
        (sig_gap β₀.length j k M hM hkM)
        (by have := sig_upper j k M hj; omega))
  -- (2) uses of the left-end rules: `d = 0, 1, 2`
  have pL := sig_forall_lt β₀ k (fun d β => ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesOrbit (leftRule d)
        (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) (parityOf β).length : ℚ))
    (1 / 12) 3 (fun d hd => hk₂ k hk2 d (by omega))
  -- (3) expansion
  have pE := hk₃ k hk3
  -- union bound: all events hold with probability at least `1 - 1/4 - 1/4 - 1/8 = 3/8`
  have pLE := sig_and β₀ k (fun β => ∀ d < 3, ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesOrbit (leftRule d)
        (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) (parityOf β).length : ℚ))
    (fun β => 2 ^ ((parityOf β).length + ⌈ce * k⌉₊) ≤ 3 ^ terrasA (parityOf β))
  have pAll := sig_and β₀ k (fun β => ∀ j < M,
      WinClose (bitsMSB (parityOf β).length (terrasR (parityOf β)))
        ((parityOf β).length - blockEnd β (β₀.length + (j + 1) * k / M))
        ((parityOf β).length - blockEnd β (β₀.length + j * k / M)) J δ)
    (fun β => (∀ d < 3, ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesOrbit (leftRule d)
        (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) (parityOf β).length : ℚ)) ∧
      2 ^ ((parityOf β).length + ⌈ce * k⌉₊) ≤ 3 ^ terrasA (parityOf β))
  have hM4 : (M : ℚ) * (1 / (4 * (M : ℚ))) = 1 / 4 := by field_simp
  have h3 : ((3 : ℕ) : ℚ) = 3 := by norm_num
  rw [hM4] at pW
  rw [h3] at pL
  have hpos : (0 : ℚ) < _ := lt_of_lt_of_le (by linarith) pAll
  obtain ⟨β, hβ, hev⟩ := exists_of_Prσ_pos β₀ k _ hpos
  refine ⟨k, hkN, β, length_of_mem_blockChoices hβ, hev.1, ?_, hev.2.2⟩
  intro d hd t ht
  exact hev.2.1 d (by omega) t ht

end Collatz.Arctic

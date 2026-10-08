/-
Generic layer: the existence lemma on the side of `σ` in the assembly, and summing the slope.

Adapted from `CoreSigma.lean` (`sigma_good`) and `CoreProb.lean` (`slope_orbit`) for $T$. The union bounds for `Prσ`
(`sig_and`, `sig_forall_lt`, `sig_gap`, etc.) and the law of large numbers for the expansion `fam_expansion_lln` depend only on the shape, so they are used from the source
as they are.

* `slope_orbitG`: sums the slope hypothesis for `κ` along an orbit segment `n → f^[m] n` all of whose points lie in the domain `dom`
  (the `T n ≥ 1` of the source is replaced by the hypothesis `hpos` that images are at least 1 (the model's `f_pos`)).
* `sigma_good`: the event on `σ` in the proof of Theorem 6.8. Fix the first block `β₀` and choose the remaining `k` blocks `β` so that
  (1) the window frequencies on `M` intervals of block indices (hypothesis `HTerrasWinR BM.R`), (2) the number of uses of the rule `ρ` is at least `c_L k`
  (hypothesis `HUseR`; an event for **a single rule**, and the length of the orbit is the number of steps `BM.steps`), and (3) the expansion `2^{m + ⌈c_e k⌉} ≤ 3^A`
  (`m` is the number of bits) hold at the same time. The source applied the events for the three left-end rules with `ε = 1/12` each; here
  the single event is applied with `ε = 1/4` (the total probability is at least `1 - 1/4 - 1/4 - 1/8 = 3/8 > 0`).
-/
import CollatzProof.Arctic.Gen.Model
import CollatzProof.Arctic.CoreSigma

namespace Collatz.Arctic.Gen

open Collatz.Arctic

/-- Sums the slope hypothesis for `κ` along an orbit segment `n → f^[m] n` all of whose points lie in the domain. -/
theorem slope_orbitG {D : ℕ} (f : ℕ → ℕ) (dom : ℕ → Prop) (hpos : ∀ n, dom n → 1 ≤ f n)
    (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (κ : ℕ)
    (hfin : ∀ n, 1 ≤ n → autoVal u A c n ≠ 0)
    (hslope : ∀ n, dom n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a → autoVal u A c (f n) = Arc.fin b →
      b + κ * lenT n ≤ a + κ * lenT (f n)) :
    ∀ (m n : ℕ), (∀ i < m, dom (f^[i] n)) → ∀ a b : ℕ, autoVal u A c n = Arc.fin a →
      autoVal u A c (f^[m] n) = Arc.fin b → b + κ * lenT n ≤ a + κ * lenT (f^[m] n) := by
  intro m
  induction m with
  | zero =>
    intro n _ a b ha hb
    simp only [Function.iterate_zero, id] at hb
    rw [ha] at hb
    have := congrArg Arc.val hb
    simp only [Arc.val_fin] at this
    have hab : a = b := by exact_mod_cast this
    subst hab
    simp
  | succ m ih =>
    intro n horb a b ha hb
    have hn : dom n := by simpa using horb 0 (Nat.succ_pos m)
    have hfn : 1 ≤ f n := hpos n hn
    obtain ⟨c', hc'⟩ := (Arc.val_ne_bot_iff _).mp
      ((Arc.ne_zero_iff_val _).mp (hfin (f n) hfn))
    have h1 := hslope n hn a c' ha hc'
    have horb' : ∀ i < m, dom (f^[i] (f n)) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hb' : autoVal u A c (f^[m] (f n)) = Arc.fin b := by
      rwa [← Function.iterate_succ_apply]
    have h2 := ih (f n) horb' c' b hc' hb'
    rw [Function.iterate_succ_apply]
    omega

/-- **Existence on the side of `σ`** (the event on `σ` in the proof of Theorem 6.8, the form for a single rule `ρ`). Fixing the first block `β₀`,
there are constants `c_L, c_e > 0` (depending only on `β₀`) such that for every `J`, `δ > 0`, `M ≥ 1` and `N` there are `k ≥ N` and a choice `β` of `k`
blocks for which, for `β₀ ++ β`, (1) the window frequencies on `M` intervals, (2) the uses of the rule `ρ`, and (3) the expansion
hold at the same time. -/
theorem sigma_good (BM : BlockModel) (cd : ℕ → List Rule) (ρ : Rule) (hTW : HTerrasWinR BM.R)
    (hU : HUseR BM.f BM.R BM.steps cd ρ) (β₀ : List Bool) :
    ∃ cL : ℚ, 0 < cL ∧ ∃ ce : ℚ, 0 < ce ∧ ∀ (J : ℕ) (δ : ℚ), 0 < δ → ∀ M : ℕ, 1 ≤ M →
      ∀ N : ℕ, ∃ k, N ≤ k ∧ ∃ β : List Bool, β.length = k ∧
      (∀ j < M, WinClose (bitsMSB (parityOf (β₀ ++ β)).length (BM.R (β₀ ++ β)))
          ((parityOf (β₀ ++ β)).length - blockEnd (β₀ ++ β) (β₀.length + (j + 1) * k / M))
          ((parityOf (β₀ ++ β)).length - blockEnd (β₀ ++ β) (β₀.length + j * k / M)) J δ) ∧
      (∀ t : ℕ, 2 ^ (parityOf (β₀ ++ β)).length ≤ t →
          cL * k ≤ (usesOrbitG BM.f cd ρ
            (BM.R (β₀ ++ β) + 2 ^ (parityOf (β₀ ++ β)).length * t) (BM.steps (β₀ ++ β)) : ℚ)) ∧
      2 ^ ((parityOf (β₀ ++ β)).length + ⌈ce * k⌉₊) ≤ 3 ^ terrasA (parityOf (β₀ ++ β)) := by
  obtain ⟨c, hc, hUc⟩ := hU β₀
  obtain ⟨ce, hce, hE⟩ := fam_expansion_lln
  refine ⟨c, hc, ce, hce, ?_⟩
  intro J δ hδ M hM N
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  obtain ⟨k₁, hk₁⟩ := hTW β₀ J δ (1 / (2 * (M : ℚ))) (1 / (4 * (M : ℚ))) hδ
    (by positivity) (by positivity)
  obtain ⟨k₂, hk₂⟩ := hUc (1 / 4) (by norm_num)
  obtain ⟨k₃, hk₃⟩ := hE β₀ (1 / 8) (by norm_num)
  -- `k` is at least `N`, `2M` and each `k₀` (take the sum)
  obtain ⟨k, hkN, hkM, hk1, hk2, hk3⟩ : ∃ k, N ≤ k ∧ 2 * M ≤ k ∧ k₁ ≤ k ∧ k₂ ≤ k ∧ k₃ ≤ k :=
    ⟨N + 2 * M + k₁ + k₂ + k₃, by omega, by omega, by omega, by omega, by omega⟩
  -- (1) window frequencies: `M` intervals
  have pW := sig_forall_lt β₀ k (fun j β =>
      WinClose (bitsMSB (parityOf β).length (BM.R β))
        ((parityOf β).length - blockEnd β (β₀.length + (j + 1) * k / M))
        ((parityOf β).length - blockEnd β (β₀.length + j * k / M)) J δ)
    (1 / (4 * (M : ℚ))) M (fun j hj =>
      hk₁ k hk1 (β₀.length + j * k / M) (β₀.length + (j + 1) * k / M) (Nat.le_add_right _ _)
        (sig_gap β₀.length j k M hM hkM)
        (by have := sig_upper j k M hj; omega))
  -- (2) uses of the rule `ρ`
  have pU := hk₂ k hk2
  -- (3) expansion
  have pE := hk₃ k hk3
  -- union bound: the probability of all events together is at least `1 - 1/4 - 1/4 - 1/8 = 3/8`
  have pUE := sig_and β₀ k (fun β => ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesOrbitG BM.f cd ρ (BM.R β + 2 ^ (parityOf β).length * t) (BM.steps β) : ℚ))
    (fun β => 2 ^ ((parityOf β).length + ⌈ce * k⌉₊) ≤ 3 ^ terrasA (parityOf β))
  have pAll := sig_and β₀ k (fun β => ∀ j < M,
      WinClose (bitsMSB (parityOf β).length (BM.R β))
        ((parityOf β).length - blockEnd β (β₀.length + (j + 1) * k / M))
        ((parityOf β).length - blockEnd β (β₀.length + j * k / M)) J δ)
    (fun β => (∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesOrbitG BM.f cd ρ (BM.R β + 2 ^ (parityOf β).length * t) (BM.steps β) : ℚ)) ∧
      2 ^ ((parityOf β).length + ⌈ce * k⌉₊) ≤ 3 ^ terrasA (parityOf β))
  have hM4 : (M : ℚ) * (1 / (4 * (M : ℚ))) = 1 / 4 := by field_simp
  rw [hM4] at pW
  have hpos : (0 : ℚ) < _ := lt_of_lt_of_le (by linarith) pAll
  obtain ⟨β, hβ, hev⟩ := exists_of_Prσ_pos β₀ k _ hpos
  exact ⟨k, hkN, β, length_of_mem_blockChoices hβ, hev.1, hev.2.1, hev.2.2⟩

end Collatz.Arctic.Gen

/-
# Case A: values and numbers of uses in degree 0 (Lemma 12.30 of the paper)

The consequence of `d ≤ 0` and the step on the numbers of uses, for automata all of whose components are 0/1
(adapted from an earlier, longer argument that is not used here).

* **`caseA`**: if the set `𝔎` of configurations contains a configuration `c` whose coefficients of positive degree are all 0, then the conclusion
  of the core statement holds (for every rule `ρ` and every `K` there are `n ≥ K` with `3 ∤ n` and a segment of the orbit, all of whose points are at least 2, on which `V(n) <` the number of uses of `ρ`).
* Proof: take `σ` in the event of the left-end rules (`uses_family_inter`, probability at least 1/2), choose `n` so that the cyclic class matches the event (c)
  (`eventC`, `exists_len_cls`), and take `u` in the intersection of the set of `u` of the event (c) with the event on the numbers of uses. The configuration of the point `x₀` is
  `c`, its value is `V0 c` (`aval_eq_V0`, independent of `k`), `3 ∤ x₀` (the residue condition of `𝔎`), and each of the 11 rules is used at least `c' k` times.
-/
import CollatzProof.Arctic.Nat.W3hCoef
import CollatzProof.Arctic.Nat.W3Uses

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel IsMinIdeal InH)

set_option linter.unusedSectionVars false

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- The configuration of the starting point: from the state after reading the free bits, read the word `w_σ (u♯)^R` of `σ`. -/
theorem conf_mid0 (β : List Bool) (n u : ℕ) :
    S.conf (S.mid0 β n u) =
      ((bitsMSB S.s' (famRho S.β₀ β)).map W3a.l2f ++
        (bitsMSB ((parityOf β).length - S.s') (famRtop S.β₀ β)).map W3a.l2f ++ S.y'' ++ S.τ).foldl (stepF B)
        (((bitsMSB (S.Flen n) u).map W3a.l2f).foldl (stepF B) S.P1) := by
  unfold conf mid0 P1
  simp only [List.append_assoc, List.foldl_append]

/-- The starting point of the family is positive: `1 ≤ x₀` (`famX0`). -/
theorem x0_pos (β : List Bool) (n u : ℕ) : 1 ≤ famX0 S.β₀ β n S.Kc S.T0 u := by
  unfold famX0
  have := fam_T_pos (β₀ := S.β₀) (β := β) (n := n) (K := S.Kc) u S.T0_pos
  have : 1 ≤ 2 ^ (parityOf β).length * famT S.β₀ β n S.Kc S.T0 u := Nat.mul_pos (by positivity) this
  omega

/-- **Case A** (Lemma 12.30 of the paper): if a configuration `c` of `𝔎` has all coefficients of positive degree equal to 0, the conclusion of the core statement holds. -/
theorem caseA {c : PSt B} (hc : c ∈ S.Kset) (hcoef : ∀ d, 1 ≤ d → S.coef d c.1 = 0) :
    ∀ ρ ∈ rulesST, ∀ K₀ : ℕ, ∃ n, K₀ ≤ n ∧ ¬ 3 ∣ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ aval B (binWord n) < usesOrbit ρ n m := by
  intro ρ hρ K₀
  obtain ⟨cU, hcU, hU⟩ := W3a.uses_family_inter S.β₀
  obtain ⟨L, hL⟩ := S.eventC
  set V := S.V0 c.1
  obtain ⟨k₀, hk₀⟩ := hU (1 / 2) (by norm_num) L
  -- take `k` large (`c' k > V`)
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt ((V : ℚ) / cU)
  set k := max k₀ (k₁ + 1)
  have hkV : (V : ℚ) < cU * k := by
    have h1 : (k₁ : ℚ) ≤ k := by exact_mod_cast (show k₁ ≤ k by omega)
    rw [div_lt_iff₀ hcU] at hk₁
    nlinarith
  obtain ⟨hprob, hinter⟩ := hk₀ k (le_max_left _ _)
  have hpos : 0 < Prσ S.β₀ k (W3a.EvLeft cU k) := by linarith
  obtain ⟨β', hβ', hEv⟩ := exists_of_Prσ_pos S.β₀ k _ hpos
  set β := S.β₀ ++ β'
  have hβlen : β.length = S.β₀.length + k := by
    simp [β, length_of_mem_blockChoices hβ']
  set m := (parityOf β).length
  set w := (bitsMSB S.s' (famRho S.β₀ β)).map W3a.l2f ++
    (bitsMSB (m - S.s') (famRtop S.β₀ β)).map W3a.l2f ++ S.y''
  obtain ⟨b, hbc, hcnt⟩ := hL c hc w
  -- the length `F` that matches the cyclic class
  obtain ⟨F, hF₀, -, hFcls⟩ := exists_len_cls (Dfa.period_pos (stepP B) S.P1) (Dfa.cls (stepP B) S.P1 b)
    (L + m + k + K₀ + 1)
  set n := F + S.Kc + S.s'
  have hFn : S.Flen n = F := by simp only [Flen, n]; omega
  have hKn : S.Kc + S.s' ≤ n := by omega
  -- the set of `u` of the event (c)
  set sC := (Finset.range (2 ^ F)).filter (fun u =>
    ((bitsMSB F u).map W3a.l2f).foldl (stepF B) S.P1 = b)
  have hsC : 2 ^ (F - L) ≤ sC.card := hcnt F (by omega) hFcls
  have hK1 : 1 ≤ S.Kc := by simp [Kc]
  have hKn' : S.Kc + (parityOf S.β₀).length ≤ n := hKn
  have hmn : (parityOf β).length < n := by omega
  have hkF : k ≤ n - S.Kc - (parityOf S.β₀).length := by
    show k ≤ n - S.Kc - S.s'; omega
  have hFeq : n - S.Kc - (parityOf S.β₀).length = F := hFn
  obtain ⟨u, hu, hPu, hUses⟩ := hinter β hEv (by omega) n S.Kc S.T0 hK1 hKn' S.T0_bounds.1 hmn hkF
    (fun u => ((bitsMSB F u).map W3a.l2f).foldl (stepF B) S.P1 = b) sC
    (fun u hu => by
      rw [Finset.mem_filter, Finset.mem_range] at hu
      rw [hFeq]; exact hu)
    (by rw [hFeq]; exact hsC)
  rw [hFeq] at hu
  -- the point `x₀`
  set x₀ := famX0 S.β₀ β n S.Kc S.T0 u
  have hbw : binWord x₀ = fullW S.us [] S.y'' S.z (S.mid0 β n u) S.R :=
    S.binWord_x0 β' hKn (by rw [hFn]; exact hu)
  have hconf : S.conf (S.mid0 β n u) = c := by
    rw [conf_mid0, hFn, hPu]
    simpa [w, List.append_assoc] using hbc
  have hx1 : 1 ≤ x₀ := S.x0_pos β n u
  have hval : valW 1 (binWord x₀) = x₀ := valW_binWord x₀ hx1
  have h3 : ¬ 3 ∣ x₀ := by
    have := S.not_dvd_of_conf (S.mid0 β n u) (by rw [hconf]; exact hc)
    rwa [← hbw, hval] at this
  have hΦ : aval B (binWord x₀) = V := by
    rw [hbw, S.aval_eq_V0 (S.mid0 β n u) (fun d hd => by
      rw [← S.conf_fst, hconf]; exact hcoef d hd)]
    simp only [V, ← S.conf_fst, hconf]
  refine ⟨x₀, ?_, h3, m, fam_orbit_two_le S.β₀ β u S.T0_pos, ?_⟩
  · -- `x₀ ≥ 2^{n+m-1} ≥ n ≥ K₀`
    have hge : 2 ^ (n + m - 1) ≤ x₀ := fam_X0_ge S.β₀ β (n := n) (K := S.Kc) (τ := S.T0) u hK1 (by omega) S.T0_bounds.1
    have : n + m - 1 < 2 ^ (n + m - 1) := Nat.lt_two_pow_self
    omega
  · rw [hΦ]
    have := hUses ρ hρ
    have h2 : (V : ℚ) < usesOrbit ρ x₀ m := lt_of_lt_of_le hkV this
    exact_mod_cast h2

end Setup

end Collatz.Arctic.NatQ5.W3h

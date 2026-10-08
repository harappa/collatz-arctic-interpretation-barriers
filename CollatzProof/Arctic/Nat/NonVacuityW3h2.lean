/-
# Natural-number matrix interpretations ($\mathcal T$): the premise of case B is not vacuous (Proposition 12.31)

**Source**: copied from the example of an internal reviewer of the whole proof of Theorem 10.10 (a minor point of that review; `CaseBNonVac.lean` in the
reviewer's scratch space). The proof is the reviewer's, unchanged (only the namespace was moved to `Collatz.Arctic.NatQ5.W4a`). Outside the closure of the main theorems.

The example `laneAuto 0` of §1 of `NonVacuityW3h.lean` has value identically 1 on the numbers prime to 3, so it does not go through case B (the contradiction in
`caseB_false`). Here we give an example in which the premise of case B actually holds.

* `autoS_caseB_hyp`: for the automaton `autoS` whose value is the length of the word (`NV.autoS` of `NonVacuityW3c.lean`, `V(ω) = |ω|`), in every setting `S`
  every configuration of the set of configurations `𝔎` has a positive coefficient of positive degree (the premise `hB` of `caseB_false`). This checks that the
  coefficients `coef` do not vanish identically because of the way they are defined. Only `aval_eq_V0` (if the coefficients vanish, the value is constant) and the count
  `eventC` are used: if some configuration has all coefficients of positive degree equal to 0, two point words of different lengths have the same value `V₀`,
  contradicting the fact that the value is the length.
* `autoS_caseB_hyp_nonempty`: settings actually exist (all components of `autoS` are 0/1). So the premise `hB` holds in a non-empty situation.
* `autoS_not_mono3`: by contraposition, `autoS` does not satisfy `AutoMono3`, condition (M_3) (from `caseB_false`). This is obvious, since the value is the length,
  but it checks the content of `caseB_false`.
-/
import CollatzProof.Arctic.Nat.Final
import CollatzProof.Arctic.Nat.NonVacuityW3c

namespace Collatz.Arctic.NatQ5.W4a

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c Collatz.Arctic.NatQ5.W3h

/-- **The premise of case B holds** (the example of the internal reviewer): in every setting of `autoS`, every configuration of `𝔎` has a positive coefficient
of positive degree. -/
theorem autoS_caseB_hyp (S : Setup NV.autoS) : ∀ c ∈ S.Kset, ∃ d, 1 ≤ d ∧ 0 < S.coef d c.1 := by
  intro c hc
  by_contra hne
  push Not at hne
  have hz : ∀ d, 1 ≤ d → S.coef d c.1 = 0 := fun d hd => le_antisymm (hne d hd) (S.coef_nonneg d c.1)
  obtain ⟨L, hL⟩ := S.eventC
  obtain ⟨b, hb, hcnt⟩ := hL c hc S.y''
  have hp : 0 < Dfa.period (stepP NV.autoS) S.P1 := Dfa.period_pos _ _
  obtain ⟨F₁, hF₁, -, hcls₁⟩ := Setup.exists_len_cls hp (Dfa.cls (stepP NV.autoS) S.P1 b) L
  have hcls₂ : ((F₁ + Dfa.period (stepP NV.autoS) S.P1 : ℕ) : ZMod (Dfa.period (stepP NV.autoS) S.P1)) =
      Dfa.cls (stepP NV.autoS) S.P1 b := by
    push_cast; rw [ZMod.natCast_self, add_zero]; exact hcls₁
  have pick : ∀ F, L ≤ F → ((F : ℕ) : ZMod (Dfa.period (stepP NV.autoS) S.P1)) = Dfa.cls (stepP NV.autoS) S.P1 b →
      ∃ u, ((bitsMSB F u).map W3a.l2f).foldl (stepF NV.autoS) S.P1 = b := by
    intro F hF hcl
    have h := hcnt F hF hcl
    have hpos : 0 < ((Finset.range (2 ^ F)).filter (fun u =>
        ((bitsMSB F u).map W3a.l2f).foldl (stepF NV.autoS) S.P1 = b)).card :=
      lt_of_lt_of_le (Nat.two_pow_pos _) h
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hu
    exact ⟨u, hu.2⟩
  obtain ⟨u₁, hu₁⟩ := pick F₁ hF₁ hcls₁
  obtain ⟨u₂, hu₂⟩ := pick (F₁ + Dfa.period (stepP NV.autoS) S.P1) (by omega) hcls₂
  have key : ∀ F u, ((bitsMSB F u).map W3a.l2f).foldl (stepF NV.autoS) S.P1 = b →
      (fullW S.us [] S.y'' S.z (List.replicate 8 0 ++ (bitsMSB F u).map W3a.l2f) S.R).length = S.V0 c.1 := by
    intro F u hu
    have hconf : S.conf (List.replicate 8 0 ++ (bitsMSB F u).map W3a.l2f) = c := by
      unfold Setup.conf
      simp only [List.foldl_append]
      rw [show (List.foldl (stepF NV.autoS) S.P0 (List.replicate 8 0)) = S.P1 from rfl, hu]
      simpa [List.foldl_append] using hb
    have hsT : S.D.sT (List.replicate 8 0 ++ (bitsMSB F u).map W3a.l2f) = c.1 := by
      rw [← S.conf_fst, hconf]
    rw [← NV.aval_autoS, S.aval_eq_V0 _ (fun d hd => by rw [hsT]; exact hz d hd), hsT]
  have e₁ := key F₁ u₁ hu₁
  have e₂ := key _ u₂ hu₂
  rw [length_fullW, List.length_append, List.length_map, bitsMSB_length] at e₁ e₂
  omega

/-- Settings actually exist (all components of `autoS` are 0/1). So the premise `hB` of `caseB_false` holds in a non-empty situation. -/
theorem autoS_caseB_hyp_nonempty : ∃ S : Setup NV.autoS, ∀ c ∈ S.Kset, ∃ d, 1 ≤ d ∧ 0 < S.coef d c.1 := by
  obtain ⟨S⟩ := W3h.exists_setup decompStmtT0 NV.autoS NV.autoS_h01
  exact ⟨S, autoS_caseB_hyp S⟩

/-- Contraposition: `autoS` does not satisfy `AutoMono3` (from `caseB_false`). This is obvious, since the value is the length, but it checks the content of
`caseB_false`. -/
theorem autoS_not_mono3 : ¬ AutoMono3 NV.autoS := by
  intro h
  obtain ⟨S, hS⟩ := autoS_caseB_hyp_nonempty
  exact S.caseB_false h hS

end Collatz.Arctic.NatQ5.W4a

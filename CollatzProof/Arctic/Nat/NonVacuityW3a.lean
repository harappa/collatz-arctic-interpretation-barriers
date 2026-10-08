/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for the point family, the uses of rules and iterated sums (Section 12)

Checks that the premises of the main theorems of `W3Bridge`, `W3Uses` and `W3Iter` can be satisfied and that their conclusions are not trivial (outside the import closure).
Only the three standard axioms (the axiom checks are in `verify/Probe.lean`). Computations are checked by `decide +kernel` (`native_decide` is not used).

* **§1 (the point family)**: a concrete point of the family (`β₀ = []`, `β = [X']`, `n = 27`, `K = 1`, `τ = 1`, `u = 59556384`) satisfies `FamOK`, with its value
  (`ex_famOK`, `ex_famX0`), and the residue coordinate (`ex_valW_t`). The event of window frequencies on the point family is not empty: there is a choice of blocks
  whose window frequencies on the whole Terras part `[n - 1, n - 1 + m)` are close to uniform (`exists_terrasWin_point`).
* **§2 (uses of rules)**: the free bits `u` of the point above contain (read from the low end) each of the six patterns `pat5 b d` (`ex_occ`), and each of the six carry rules
  is used in the canonical derivation of that point (`ex_uses`; an example in which the left-hand side of `uses_aRule_famX0_ge` is positive). As a consequence of the main theorem (Corollary 12.18),
  **for every `N` there is a point of size at least `N` at which each of the 11 rules is used at least `N` times on the same orbit segment** (`all_rules_used`,
  without hypotheses).
* **§3 (iterated sums)**: the constant sequence 1 satisfies the hypothesis (IH) of Lemma 12.15 with `η = 0` (`iterHyp_const`), and the conclusion is `|I_2(N) - N^2/2| ≤ N`
  (`ex_iterSum_two`; the error is `o(N^2)` of the main term). Values of an iterated sum (`ex_isum_four`: the 6 pairs `p₁ < p₂ < 4`) and of an iterated sum with gaps
  (`ex_gsum_gap`: the 3 pairs `p₁ + 2 ≤ p₂ < 4`).
-/
import CollatzProof.Arctic.Nat.W3Uses
import CollatzProof.Arctic.Nat.W3Iter

namespace Collatz.Arctic.NatQ5.W3a

open Collatz.Arctic

/-! ## §1 The point family -/

/-- The condition on the points of the family can be satisfied. -/
theorem ex_famOK : FamOK [] 27 1 1 59556384 := by
  unfold FamOK; decide +kernel

/-- The value of the point of the family: `x₀ = r_{X'} + 2^8 t`, `t = 2^{26} + u` (`r_{X'} = 249`, `ρ = 0`). -/
theorem ex_famX0 : famX0 [] [true] 27 1 1 59556384 = 249 + 256 * (2 ^ 26 + 59556384) := by
  decide +kernel

/-- The residue coordinate: the value after reading all of `t` is `t` (an example of `valW_famX0_take_t`). -/
theorem ex_valW_t : valW 1 ((binWord (famX0 [] [true] 27 1 1 59556384)).take 26) = 2 ^ 26 + 59556384 := by
  rw [valW_famX0_take_t ex_famOK]; decide +kernel

/-- **The event of window frequencies on the point family is not empty**: for all `J`, `δ > 0` and `K₀` there is a choice `β` of `k ≥ K₀` blocks such that for every point
of the family (`β₀ = []`) the window frequencies of the point word on the whole Terras part `[n - 1, n - 1 + m)` are within `δ` of uniform. -/
theorem exists_terrasWin_point (J : ℕ) (δ : ℚ) (hδ : 0 < δ) (K₀ : ℕ) :
    ∃ k ≥ K₀, ∃ β ∈ blockChoices k, ∀ n K τ u : ℕ, FamOK [] n K τ u →
      WinClose ((ptB [] β n K τ u).map W3d.ofB) (n - 1 + ((parityOf β).length - blockEnd β k))
        (n - 1 + ((parityOf β).length - blockEnd β 0)) J δ := by
  obtain ⟨k₀, hk₀⟩ := terrasWin_famX0 [] J δ 1 (1 / 2) hδ one_pos (by norm_num)
  set k := max k₀ K₀ with hk
  have hpr := hk₀ k (le_max_left _ _) 0 k le_rfl (by simp) (by simp)
  have hpos : 0 < Prσ [] k (fun β => ∀ n K τ u : ℕ, FamOK [] n K τ u →
      WinClose ((ptB [] β n K τ u).map W3d.ofB) (n - 1 + ((parityOf β).length - blockEnd β k))
        (n - 1 + ((parityOf β).length - blockEnd β 0)) J δ) := by linarith
  obtain ⟨β, hβ, hE⟩ := exists_of_Prσ_pos [] k _ hpos
  rw [List.nil_append] at hE
  exact ⟨k, le_max_right _ _, β, hβ, hE⟩

/-! ## §2 Uses of rules -/

/-- The free bits of the point above (read from the low end) contain each of the six patterns. -/
theorem ex_occ : ∀ b < 2, ∀ d ≤ 2, 1 ≤ occS (((bitsMSB 26 59556384).reverse).map l2n) (pat5 b d) := by
  decide +kernel

/-- Each of the six carry rules is used in the canonical derivation of the point above. -/
theorem ex_uses : ∀ b < 2, ∀ d ≤ 2, 1 ≤ uses (aRule b d) (famX0 [] [true] 27 1 1 59556384) := by
  decide +kernel

/-- The premises of `uses_aRule_famX0_ge` can be satisfied, and its left-hand side is positive (at the point above). -/
theorem ex_uses_ge (b : ℕ) (hb : b < 2) (d : ℕ) (hd : d ≤ 2) :
    1 ≤ uses (aRule b d) (famX0 [] [true] 27 1 1 59556384) := by
  have h := uses_aRule_famX0_ge (β₀ := []) (β := [true]) (n := 27) (K := 1) (τ := 1) (u := 59556384)
    (by simp) (by simp [parityOf]) le_rfl (by norm_num [parityOf]) b d hd
  have hF : 27 - 1 - (parityOf ([] : List Bool)).length = 26 := by simp [parityOf]
  rw [hF] at h
  exact le_trans (ex_occ b hb d hd) h

/-- **For every `N` there is a point of size at least `N` at which each of the 11 rules is used at least `N` times on the same orbit segment** (without hypotheses;
`uses_family_inter` applied with `β₀ = []` and the whole set as the event (c)). -/
theorem all_rules_used (N : ℕ) : ∃ x₀ m : ℕ, N ≤ x₀ ∧ (∀ i < m, 2 ≤ T^[i] x₀) ∧
    ∀ ρ ∈ rulesST, N ≤ usesOrbit ρ x₀ m := by
  obtain ⟨c, hc, h⟩ := uses_family_inter []
  obtain ⟨k₀, hk⟩ := h (1 / 2) (by norm_num) 0
  obtain ⟨k, hk1, hk2, hk3⟩ : ∃ k, k₀ ≤ k ∧ ⌈(N : ℚ) / c⌉₊ ≤ k ∧ N + 1 ≤ k :=
    ⟨k₀ + ⌈(N : ℚ) / c⌉₊ + N + 1, by omega, by omega, by omega⟩
  obtain ⟨hpr, hdet⟩ := hk k hk1
  have hpos : 0 < Prσ [] k (EvLeft c k) := by linarith
  obtain ⟨β, hβ, hEv⟩ := exists_of_Prσ_pos [] k _ hpos
  rw [List.nil_append] at hEv
  have hβlen : β.length = k := length_of_mem_blockChoices hβ
  have hs : (parityOf ([] : List Bool)).length = 0 := by simp [parityOf]
  obtain ⟨u, -, -, hgood⟩ := hdet β hEv (by omega) ((parityOf β).length + k + 1) 1 1 le_rfl
    (by rw [hs]; omega) (by norm_num) (by omega) (by rw [hs]; omega) (fun _ => True)
    (Finset.range (2 ^ ((parityOf β).length + k + 1 - 1 - (parityOf ([] : List Bool)).length)))
    (fun u hu => ⟨Finset.mem_range.mp hu, trivial⟩) (by rw [Finset.card_range]; exact le_rfl)
  refine ⟨famX0 [] β ((parityOf β).length + k + 1) 1 1 u, (parityOf β).length, ?_,
    fam_orbit_two_le [] β u le_rfl, fun ρ hρ => ?_⟩
  · have h1 := fam_X0_ge [] β (n := (parityOf β).length + k + 1) (K := 1) (τ := 1) u le_rfl (by omega)
      (by norm_num)
    have h2 : (parityOf β).length + k + 1 + (parityOf β).length - 1 <
        2 ^ ((parityOf β).length + k + 1 + (parityOf β).length - 1) := Nat.lt_two_pow_self
    omega
  · have h1 := hgood ρ hρ
    have hk' : (N : ℚ) ≤ c * k := by
      have hc1 : (N : ℚ) / c ≤ (⌈(N : ℚ) / c⌉₊ : ℚ) := Nat.le_ceil _
      have hk2' : ((⌈(N : ℚ) / c⌉₊ : ℕ) : ℚ) ≤ k := by exact_mod_cast hk2
      rw [div_le_iff₀ hc] at hc1
      nlinarith
    exact_mod_cast hk'.trans h1

/-! ## §3 Iterated sums -/

/-- The constant sequence 1 satisfies the hypothesis (IH) of Lemma 12.15 with `B = 1`, `η = 0` and `Q = 1`. -/
theorem iterHyp_const (N : ℕ) : IterHyp 1 0 N (fun _ => (1 : ℝ)) 1 := by
  refine ⟨fun _ => zero_le_one, zero_le_one, le_rfl, fun n _ => ?_, ?_⟩
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_mul, sub_self, abs_zero, zero_mul]
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_mul]

/-- **An example for Lemma 12.15**: `|I_2(N) - N^2/2| ≤ N` (two constant sequences 1, `ε_2 = 1/N`). -/
theorem ex_iterSum_two (N : ℕ) (hN : 1 ≤ N) :
    |isum [fun _ => 1, fun _ => 1] N - (N : ℝ) ^ 2 / 2| ≤ (N : ℝ) := by
  have h := iterSum_approx (B := 1) (η := 0) zero_le_one hN [((fun _ => (1 : ℝ)), 1), ((fun _ => (1 : ℝ)), 1)]
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact iterHyp_const N) N le_rfl
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have he : epsIter 1 0 N 2 = 1 / N := by
    simp only [epsIter]; norm_num
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.length_cons,
    List.length_nil, he] at h
  norm_num [Nat.factorial] at h
  have e1 : (N : ℝ)⁻¹ * (N : ℝ) ^ 2 = N := by field_simp
  have e2 : (N : ℝ) ^ 2 / 2 = 1 / 2 * (N : ℝ) ^ 2 := by ring
  rw [e2]
  rw [e1] at h
  exact h

/-- A value of an iterated sum: there are 6 pairs `p₁ < p₂ < 4`. -/
theorem ex_isum_four : isum [fun _ => 1, fun _ => 1] 4 = 6 := by
  simp only [isum_cons, isum_nil, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- A value of an iterated sum with gaps: there are 3 pairs `p₁ + 2 ≤ p₂ < 4` (`(0,2)`, `(0,3)`, `(1,3)`). -/
theorem ex_gsum_gap : gsum [((fun _ => 1), 2), ((fun _ => 1), 1)] 4 = 3 := by
  simp only [gsum_cons, gsum_nil, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end Collatz.Arctic.NatQ5.W3a

/-
Analytic ingredients of the swap argument (Appendix B.2), part 3: Proposition B.6 (average over the swap choices `e` and over `w`, `SpecQavg`).

* `ka_law_sum`, `ka_law_total`, `ka_law_Q`: sums against `μ_w` (`keyLaw`), and (Q1) applied to `μ_w`:
  `Q_λ(μ_w) = 4^{-I} Σ_{e,e'} k_λ(T(e') - T(e)) - λ²/2^V` (`e, e'` independent and uniform; `z₀` cancels in the difference).
* `ka_count_agree`: there are `2^{#{j : o_j = 0}}` vectors `e'` with `e_j = e'_j` for every `j` with `o_j ≠ 0`.
* `specQavg`: average over `w` for each pair `e, e'`. If they agree at every `o_j ≠ 0`, the difference is 0 and `k_λ(0) = λ`.
  Otherwise the difference is `2^{V - v_{j*}} ϑ` (`ϑ` a unit, `KeyAnal2.ka_D_mixed`), and its average over `w` is `λ²/2^V`
  (`KeyAnal2.ka_kappa_mixed`, the form of (Q2)). The proportion of agreeing pairs is `2^{-M}` (`M = #{j : o_j ≠ 0}`).
-/
import CollatzProof.Arctic.KeyAnal2

namespace Collatz.Arctic

open Finset

/-! ## Sums against `μ_w` -/

/-- `Σ_z μ(z) f(z) = 2^{-I} Σ_e f(z₀ + Σ_j e_j a_j)`. -/
lemma ka_law_sum (V I : ℕ) (z₀ : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) (f : ZMod (2 ^ V) → ℝ) :
    ∑ z, keyLaw V I z₀ a z * f z =
      (∑ e : Fin I → Bool, f (z₀ + ∑ j, if e j then a j else 0)) / 2 ^ I := by
  unfold keyLaw
  simp only [Finset.natCast_card_filter, div_mul_eq_mul_div, ← sum_div, sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

/-- `μ_w` is a probability measure. -/
lemma ka_law_total (V I : ℕ) (z₀ : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) :
    ∑ z, keyLaw V I z₀ a z = 1 := by
  have h := ka_law_sum V I z₀ a (fun _ => 1)
  simp only [mul_one, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  rw [h]
  push_cast
  field_simp

/-- (Q1) applied to `μ_w`: `Q_λ(μ) = 4^{-I} Σ_{e,e'} k_λ(T(e') - T(e)) - λ²/2^V`. -/
lemma ka_law_Q (V lam I : ℕ) (z₀ : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) :
    keyQ V lam (keyLaw V I z₀ a) =
      (∑ e : Fin I → Bool, ∑ e' : Fin I → Bool,
        kaKappa V lam ((z₀ + ∑ j, if e' j then a j else 0) - (z₀ + ∑ j, if e j then a j else 0)))
        / 2 ^ I / 2 ^ I - (lam : ℝ) ^ 2 / 2 ^ V := by
  rw [ka_keyQ_eq V lam _ (ka_law_total V I z₀ a)]
  congr 1
  simp_rw [mul_assoc, ← mul_sum]
  simp_rw [ka_law_sum V I z₀ a (fun z' => kaKappa V lam _)]
  rw [ka_law_sum V I z₀ a (fun z => (∑ e' : Fin I → Bool, kaKappa V lam
    ((z₀ + ∑ j, if e' j then a j else 0) - z)) / 2 ^ I)]
  simp only [sum_div]

/-! ## The number of agreeing pairs -/

/-- There are `2^{#{j : ¬P j}}` vectors `e'` that agree with `e` at every `j` with `P j`. -/
lemma ka_count_agree (I : ℕ) (P : Fin I → Prop) [DecidablePred P] (e : Fin I → Bool) :
    (univ.filter (fun e' : Fin I → Bool => ∀ j, P j → e j = e' j)).card =
      2 ^ (univ.filter (fun j => ¬ P j)).card := by
  have h : univ.filter (fun e' : Fin I → Bool => ∀ j, P j → e j = e' j) =
      Fintype.piFinset (fun j => if P j then {e j} else univ) := by
    ext e'
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' (fun j => ?_)
    by_cases hj : P j
    · simp only [hj, ite_true, mem_singleton, true_imp_iff]
      exact eq_comm
    · simp only [hj, ite_false, mem_univ, false_imp_iff]
  rw [h, Fintype.card_piFinset]
  simp only [apply_ite card, card_singleton, card_univ, Fintype.card_bool]
  rw [prod_ite, prod_const_one, prod_const, one_mul]

/-! ## Proposition B.6 -/

theorem specQavg : SpecQavg := by
  -- that `w₀` is odd is not used (the average is the same on every class `w₀ + 8G`).
  intro V ℓ d I hℓ hd hV o ω v z₀ w₀ ho hω hv hvb _hw₀
  -- notation: `λ = 2^{V-ℓ} + 2^{V-ℓ-d}`, `W = w₀ + 8G`, `c_j = o_j ω_j 2^{V - v_j}`, `D(e, e') = Σ_j (e'_j - e_j) c_j`.
  set lam : ℕ := 2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) with hlam
  have hlamV : lam ≤ 2 ^ V := by
    have h1 : 2 ^ (V - ℓ) ≤ 2 ^ (V - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (V - ℓ - d) ≤ 2 ^ (V - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ V = 2 ^ (V - 1) + 2 ^ (V - 1) := by
      rw [← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega)]
    omega
  have hlamR : (lam : ℝ) = 2 ^ (V - ℓ) + 2 ^ (V - ℓ - d) := by rw [hlam]; push_cast; ring
  set W := univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8) with hW
  have hWpos : (0 : ℝ) < W.card := by
    exact_mod_cast card_pos.mpr ⟨w₀, by simp [hW]⟩
  set c : Fin I → ZMod (2 ^ V) := fun j => (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) with hc
  set D : (Fin I → Bool) → (Fin I → Bool) → ZMod (2 ^ V) :=
    fun e e' => ∑ j, ((if e' j then c j else 0) - (if e j then c j else 0)) with hD
  set X : ℝ := (lam : ℝ) ^ 2 / 2 ^ V with hX
  -- `Q_λ(μ_w)` for each `w`.
  have hQ : ∀ w, keyQ V lam (keyLaw V I (z₀ w)
      (fun j => (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) * w)) =
      (∑ e : Fin I → Bool, ∑ e' : Fin I → Bool, kaKappa V lam (D e e' * w)) / 2 ^ I / 2 ^ I - X := by
    intro w
    have hdiff : ∀ e e' : Fin I → Bool,
        (z₀ w + ∑ j, if e' j then (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) * w else 0) -
          (z₀ w + ∑ j, if e j then (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) * w else 0) =
        D e e' * w := by
      intro e e'
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, hD, sum_mul]
      refine sum_congr rfl (fun j _ => ?_)
      simp only [hc]
      split_ifs <;> ring
    rw [ka_law_Q]
    simp only [hdiff]
    rfl
  -- the sum over `w` for each pair `(e, e')`.
  have hpair : ∀ e e' : Fin I → Bool, ∑ w ∈ W, kaKappa V lam (D e e' * w) =
      W.card * (X + if (∀ j, o j ≠ 0 → e j = e' j) then (lam : ℝ) - X else 0) := by
    intro e e'
    by_cases hag : ∀ j, o j ≠ 0 → e j = e' j
    · have hD0 : D e e' = 0 := by
        simp only [hD]
        apply sum_eq_zero
        intro j _
        by_cases hoj : o j = 0
        · simp [hc, hoj]
        · rw [hag j hoj, sub_self]
      simp only [hD0, zero_mul, ka_kappa_zero V lam hlamV, sum_const, nsmul_eq_mul,
        ite_eq_left hag]
      ring
    · have hmix : ∃ j, o j ≠ 0 ∧ e j ≠ e' j := by
        by_contra hno
        exact hag (fun j hj => by
          by_contra hne
          exact hno ⟨j, hj, hne⟩)
      obtain ⟨k, hk1, hk2, ϑ, hϑ, hDk⟩ := ka_D_mixed V ℓ d I o ω v ho hω hv hvb e e' hmix
      have hDe : D e e' = 2 ^ (V - k) * ϑ := hDk
      have hm : 2 ^ (V - k + 3) ∣ lam := by
        rw [hlam]
        apply dvd_add
        · exact pow_dvd_pow 2 (by omega)
        · exact pow_dvd_pow 2 (by omega)
      have := ka_kappa_mixed V (V - k) lam (by omega) hm ϑ hϑ w₀
      rw [ite_eq_right (c := ∀ j, o j ≠ 0 → e j = e' j) hag, add_zero]
      simp only [hDe]
      rw [this, hX]
      ring
  -- sum over the pairs: the number of agreeing pairs is `2^I 2^K` (`K = #{j : o_j = 0}`).
  set K := (univ.filter (fun j => ¬ (o j ≠ 0))).card with hK
  set M := (univ.filter (fun j => o j ≠ 0)).card with hM
  have hMK : M + K = I := by
    rw [hM, hK, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hcount : ∀ e : Fin I → Bool, ∑ e' : Fin I → Bool,
      (if (∀ j, o j ≠ 0 → e j = e' j) then (lam : ℝ) - X else 0) = 2 ^ K * ((lam : ℝ) - X) := by
    intro e
    rw [← sum_filter, sum_const, nsmul_eq_mul, ka_count_agree I (fun j => o j ≠ 0) e]
    push_cast
    rfl
  have hcardI : (Fintype.card (Fin I → Bool) : ℝ) = 2 ^ I := by
    simp [Fintype.card_bool, Fintype.card_fin]
  have htot : ∑ w ∈ W, keyQ V lam (keyLaw V I (z₀ w)
      (fun j => (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) * w)) =
      W.card * (2 ^ K / 2 ^ I * ((lam : ℝ) - X)) := by
    rw [sum_congr rfl (fun w _ => hQ w), sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_div,
      ← sum_div, Finset.sum_comm]
    rw [sum_congr rfl (fun e _ => Finset.sum_comm)]
    simp only [hpair, ← mul_sum, sum_add_distrib, hcount, sum_const, card_univ, hcardI,
      nsmul_eq_mul]
    field_simp
    ring
  rw [htot]
  have h2I : (2 : ℝ) ^ I = 2 ^ M * 2 ^ K := by rw [← pow_add, hMK]
  rw [h2I, ← hlamR, hX]
  field_simp

end Collatz.Arctic

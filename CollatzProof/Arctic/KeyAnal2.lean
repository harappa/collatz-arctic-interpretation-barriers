/-
Analytic ingredients of the swap argument (Appendix B.2), part 2: (Q2) and ingredients of Proposition B.6 (`SpecQavg`,
proved in `KeyAnal3`).

* `ka_mod8_iff`, `ka_odd_iff`, `ka_isUnit_of_odd`: residue classes modulo 8 and parity in `ZMod (2^V)` via the images in `ZMod 8`, `ZMod 2`.
* `ka_shift_count`: the periodicity argument. If `S` is invariant under translation by `s₀` and `φ(w + s₀) = φ(w) + m` (`m ∣ 2^V`, `m ∣ λ`), then
  `Σ_{w∈S} #{y' < λ : y' = c + φ(w)} = λ|S|/2^V`.
* `ka_kappa_coset`: **(Q2)** (the average of `k_λ` over a coset of the subgroup `mG` is `λ²/2^V`).
* `ka_mixed`, `ka_kappa_mixed`: if `w` is uniform on `w₀ + 8G` and `ϑ` is a unit, the average of `k_λ(2^a ϑ w)` is `λ²/2^V`
  (`2^{a+3} ∣ λ`. The paper's argument "`ϑw` is uniform on `ϑw₀ + 8G`, and `2^a ·` maps it to the uniform law on a coset of a subgroup" is
  reduced to `ka_shift_count` via the translation `w ↦ w + 8ϑ⁻¹`). `ka_kappa_zero`: `k_λ(0) = λ` (`λ ≤ 2^V`).
* `ka_D_mixed`: if there is a mixed coin (`o_j ≠ 0` and `e_j ≠ e'_j`), the difference `Σ_j (e'_j - e_j) o_j ω_j 2^{V-v_j}` is `2^{V-v_{j*}} ϑ`
  (`ϑ` a unit), where `j*` is the mixed coin with the smallest index (the largest `v`, since `v` is strictly decreasing).
-/
import CollatzProof.Arctic.KeyAnal

namespace Collatz.Arctic

open Finset

/-! ## Parity and residues modulo 8 in `ZMod (2^V)` -/

lemma ka_dvd_pow (V k : ℕ) (hk : k ≤ V) : 2 ^ k ∣ 2 ^ V := pow_dvd_pow 2 hk

/-- The value of the image under `ZMod 2^V → ZMod 2^k` is `val % 2^k`. -/
lemma ka_cast_val (V k : ℕ) (hk : k ≤ V) (x : ZMod (2 ^ V)) :
    (ZMod.castHom (ka_dvd_pow V k hk) (ZMod (2 ^ k)) x) = ((x.val : ℕ) : ZMod (2 ^ k)) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

/-- Membership in a residue class modulo 8 via the image in `ZMod 8`. -/
lemma ka_mod8_iff (V : ℕ) (hV : 3 ≤ V) (w w₀ : ZMod (2 ^ V)) :
    w.val % 8 = w₀.val % 8 ↔
      ZMod.castHom (ka_dvd_pow V 3 hV) (ZMod (2 ^ 3)) w =
        ZMod.castHom (ka_dvd_pow V 3 hV) (ZMod (2 ^ 3)) w₀ := by
  rw [ka_cast_val V 3 hV, ka_cast_val V 3 hV, ZMod.natCast_eq_natCast_iff']
  norm_num

/-- Oddness via the image in `ZMod 2`. -/
lemma ka_two_dvd (V : ℕ) (hV : 1 ≤ V) : 2 ∣ 2 ^ V := dvd_pow_self 2 (by omega)

lemma ka_odd_iff (V : ℕ) (hV : 1 ≤ V) (x : ZMod (2 ^ V)) :
    x.val % 2 = 1 ↔ ZMod.castHom (ka_two_dvd V hV) (ZMod 2) x = 1 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, show (1 : ZMod 2) = ((1 : ℕ) : ZMod 2) by norm_num,
    ZMod.natCast_eq_natCast_iff']

/-- Odd elements are units. -/
lemma ka_isUnit_of_odd (V : ℕ) (x : ZMod (2 ^ V)) (h : x.val % 2 = 1) : IsUnit x := by
  have hc : Nat.Coprime x.val (2 ^ V) :=
    Nat.Coprime.pow_right V (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr h))
  have := (ZMod.isUnit_iff_coprime x.val (2 ^ V)).mpr hc
  rwa [ZMod.natCast_zmod_val] at this

/-! ## (Q2) and the average over `w` -/

/-- **The periodicity argument**: if `S ⊆ G` is invariant under translation by `s₀`, `φ(w + s₀) = φ(w) + m`, `m ∣ 2^V` and `m ∣ λ`, then
`Σ_{w∈S} #{y' < λ : y' = c + φ(w)} = λ |S| / 2^V`. The sequence `t ↦ #{w ∈ S : t = c + φ(w)}` has period `m`,
and its sum over `[0, 2^V)` is `|S|`. -/
theorem ka_shift_count (V m lam : ℕ) (hmV : m ∣ 2 ^ V) (hm : m ∣ lam) (S : Finset (ZMod (2 ^ V)))
    (φ : ZMod (2 ^ V) → ZMod (2 ^ V)) (s₀ : ZMod (2 ^ V)) (hS : ∀ w, w + s₀ ∈ S ↔ w ∈ S)
    (hφ : ∀ w, φ (w + s₀) = φ w + (m : ZMod (2 ^ V))) (c : ZMod (2 ^ V)) :
    ∑ w ∈ S, ∑ y' ∈ range lam, (if (y' : ZMod (2 ^ V)) = c + φ w then (1 : ℝ) else 0) =
      (lam : ℝ) / 2 ^ V * (S.card : ℝ) := by
  set g : ℕ → ℝ := fun t => ∑ w ∈ S, if (t : ZMod (2 ^ V)) = c + φ w then (1 : ℝ) else 0 with hg
  rw [Finset.sum_comm]
  change ∑ t ∈ range lam, g t = _
  -- periodicity: recount via `w ↦ w - s₀`.
  have hper : ∀ t, g (t + m) = g t := by
    intro t
    simp only [hg]
    refine Finset.sum_nbij' (fun w => w - s₀) (fun w => w + s₀) ?_ ?_ ?_ ?_ ?_
    · intro w hw
      rw [← hS, sub_add_cancel]
      exact hw
    · intro w hw
      exact (hS w).mpr hw
    · intro w _; exact sub_add_cancel w s₀
    · intro w _; exact add_sub_cancel_right w s₀
    · intro w _
      have h1 : φ w = φ (w - s₀) + (m : ZMod (2 ^ V)) := by
        rw [← hφ, sub_add_cancel]
      apply if_congr _ rfl rfl
      rw [h1]
      push_cast
      constructor
      · intro h; exact add_right_cancel (b := (m : ZMod (2 ^ V))) (by rw [h]; ring)
      · intro h; rw [h]; ring
  -- the total sum is `|S|`.
  have htot : ∑ t ∈ range (2 ^ V), g t = S.card := by
    simp only [hg]
    rw [ka_sum_zmod (2 ^ V) (fun x : ZMod (2 ^ V) =>
      ∑ w ∈ S, if x = c + φ w then (1 : ℝ) else 0), Finset.sum_comm]
    simp only [sum_ite_eq', mem_univ, ite_true, sum_const, nsmul_eq_mul, mul_one]
  obtain ⟨q₁, hq₁⟩ := hm
  obtain ⟨q₂, hq₂⟩ := hmV
  have hS1 := ka_sum_periodic m q₁ g hper
  have hS2 := ka_sum_periodic m q₂ g hper
  rw [mul_comm q₂, ← hq₂, htot] at hS2
  rw [hq₁, mul_comm m q₁, hS1, nsmul_eq_mul, hS2, nsmul_eq_mul]
  have hq₂R : (2 : ℝ) ^ V = (m : ℝ) * q₂ := by exact_mod_cast hq₂
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hq₂R
    exact absurd hq₂R (by positivity)
  have hq0 : (q₂ : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq₂R
    exact absurd hq₂R (by positivity)
  rw [hq₂R]
  push_cast
  field_simp

/-- **(Q2)**: if `m ∣ 2^V` and `m ∣ λ`, then on every coset `y₀ + H` of the subgroup `H = mG = {x : m ∣ x}` (of order `2^V/m`)
the average of `k_λ` is `λ²/2^V`: `Σ_{h∈H} k_λ(y₀ + h) = λ²/2^V · |H|`. -/
theorem ka_kappa_coset (V m lam : ℕ) (hmV : m ∣ 2 ^ V) (hm : m ∣ lam) (y₀ : ZMod (2 ^ V)) :
    ∑ h ∈ univ.filter (fun x : ZMod (2 ^ V) => m ∣ x.val), kaKappa V lam (y₀ + h) =
      (lam : ℝ) ^ 2 / 2 ^ V * ((univ.filter (fun x : ZMod (2 ^ V) => m ∣ x.val)).card : ℝ) := by
  have hS : ∀ w : ZMod (2 ^ V), w + (m : ZMod (2 ^ V)) ∈ univ.filter (fun x : ZMod (2 ^ V) => m ∣ x.val)
      ↔ w ∈ univ.filter (fun x : ZMod (2 ^ V) => m ∣ x.val) := by
    intro w
    simp only [mem_filter, mem_univ, true_and]
    rw [ZMod.val_add, ZMod.val_natCast, Nat.dvd_mod_iff hmV]
    exact Nat.dvd_add_left ((Nat.dvd_mod_iff hmV).mpr (dvd_refl m))
  unfold kaKappa
  rw [Finset.sum_comm]
  have : ∀ y ∈ range lam, ∑ h ∈ univ.filter (fun x : ZMod (2 ^ V) => m ∣ x.val),
      ∑ y' ∈ range lam, (if (y : ZMod (2 ^ V)) + (y₀ + h) = y' then (1 : ℝ) else 0) =
      (lam : ℝ) / 2 ^ V * ((univ.filter (fun x : ZMod (2 ^ V) => m ∣ x.val)).card : ℝ) := by
    intro y _
    rw [← ka_shift_count V m lam hmV hm _ (fun h => y₀ + h) (m : ZMod (2 ^ V)) hS
      (fun w => by ring) (y : ZMod (2 ^ V))]
    exact sum_congr rfl (fun w _ => sum_congr rfl (fun y' _ => if_congr eq_comm rfl rfl))
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
  ring

/-- The sum over `W = {w : w ≡ w₀ (mod 8)}` of the number of times `c + 2^a ϑ w` falls in `J_λ` is `λ |W| / 2^V`
(`ϑ` a unit, `a + 3 ≤ V`, `2^{a+3} ∣ λ`). The map `w ↦ w + 8 ϑ⁻¹` preserves `W` and moves `2^a ϑ w` by `2^{a+3}`. -/
theorem ka_mixed (V a lam : ℕ) (haV : a + 3 ≤ V) (hm : 2 ^ (a + 3) ∣ lam) (ϑ : ZMod (2 ^ V))
    (hϑ : IsUnit ϑ) (w₀ c : ZMod (2 ^ V)) :
    ∑ w ∈ univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8),
      ∑ y' ∈ range lam, (if (y' : ZMod (2 ^ V)) = c + 2 ^ a * ϑ * w then (1 : ℝ) else 0) =
    (lam : ℝ) / 2 ^ V * ((univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8)).card : ℝ) := by
  set s₀ : ZMod (2 ^ V) := 8 * ϑ⁻¹ with hs₀
  have hDs : 2 ^ a * ϑ * s₀ = 2 ^ (a + 3) := by
    have hinv := ZMod.mul_inv_of_unit ϑ hϑ
    calc 2 ^ a * ϑ * s₀ = 2 ^ a * 8 * (ϑ * ϑ⁻¹) := by ring
      _ = 2 ^ (a + 3) := by rw [hinv, pow_add]; norm_num
  have hWs : ∀ w : ZMod (2 ^ V), w + s₀ ∈ univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8)
      ↔ w ∈ univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8) := by
    intro w
    simp only [mem_filter, mem_univ, true_and]
    rw [ka_mod8_iff V (by omega), ka_mod8_iff V (by omega), map_add]
    have : ZMod.castHom (ka_dvd_pow V 3 (by omega)) (ZMod (2 ^ 3)) s₀ = 0 := by
      simp only [hs₀, map_mul]
      rw [show ((ZMod.castHom (ka_dvd_pow V 3 (by omega)) (ZMod (2 ^ 3))) 8) = 0 by
        rw [map_ofNat]; rfl]
      ring
    rw [this, add_zero]
  refine ka_shift_count V (2 ^ (a + 3)) lam (pow_dvd_pow 2 haV) hm _ (fun w => 2 ^ a * ϑ * w) s₀
    hWs (fun w => ?_) c
  rw [mul_add, hDs]
  push_cast
  rfl

/-- The average over `w` (mixed case): `Σ_{w∈W} k_λ(2^a ϑ w) = λ²/2^V · |W|` ((Q2) in the form used on `W`). -/
theorem ka_kappa_mixed (V a lam : ℕ) (haV : a + 3 ≤ V) (hm : 2 ^ (a + 3) ∣ lam) (ϑ : ZMod (2 ^ V))
    (hϑ : IsUnit ϑ) (w₀ : ZMod (2 ^ V)) :
    ∑ w ∈ univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8), kaKappa V lam (2 ^ a * ϑ * w) =
    (lam : ℝ) ^ 2 / 2 ^ V *
      ((univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8)).card : ℝ) := by
  unfold kaKappa
  rw [Finset.sum_comm]
  have : ∀ y ∈ range lam, ∑ w ∈ univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8),
      ∑ y' ∈ range lam, (if (y : ZMod (2 ^ V)) + 2 ^ a * ϑ * w = y' then (1 : ℝ) else 0) =
      (lam : ℝ) / 2 ^ V *
        ((univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = w₀.val % 8)).card : ℝ) := by
    intro y _
    rw [← ka_mixed V a lam haV hm ϑ hϑ w₀ (y : ZMod (2 ^ V))]
    refine sum_congr rfl (fun w _ => sum_congr rfl (fun y' _ => ?_))
    exact if_congr eq_comm rfl rfl
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
  ring

/-- If `λ ≤ 2^V`, then `k_λ(0) = λ`. -/
lemma ka_kappa_zero (V lam : ℕ) (h : lam ≤ 2 ^ V) : kaKappa V lam 0 = lam := by
  unfold kaKappa
  have : ∀ y ∈ range lam,
      ∑ y' ∈ range lam, (if (y : ZMod (2 ^ V)) + 0 = y' then (1 : ℝ) else 0) = 1 := by
    intro y hy
    rw [mem_range] at hy
    rw [sum_eq_single y]
    · simp
    · intro y' hy' hne
      rw [mem_range] at hy'
      apply ite_eq_right
      intro heq
      rw [add_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at heq
      exact hne heq.symm
    · intro hy'; exact absurd (mem_range.mpr hy) hy'
  rw [sum_congr rfl this]
  simp

/-! ## The shape of the difference for mixed coins -/

/-- `[x] = 1` (`x` true), `0` (false). -/
def kaB {R : Type*} [Ring R] (x : Bool) : R := if x then 1 else 0

lemma ka_ite_sub {R : Type*} [Ring R] (p q : Bool) (x : R) :
    (if p then x else 0) - (if q then x else 0) = (kaB p - kaB q) * x := by
  cases p <;> cases q <;> simp [kaB]

lemma ka_cast_kaB (V : ℕ) (hV : 1 ≤ V) (x : Bool) :
    ZMod.castHom (ka_two_dvd V hV) (ZMod 2) (kaB x) = kaB x := by
  unfold kaB
  cases x <;> simp only [Bool.false_eq_true, ↓reduceIte, map_one, map_zero]

/-- If there is a mixed coin, the difference is `2^{V - v_{j*}} ϑ` (`ϑ` a unit, `j*` the mixed coin with the smallest index,
that is, with the largest `v`). -/
theorem ka_D_mixed (V ℓ d I : ℕ) (o : Fin I → ℤ) (ω : Fin I → ZMod (2 ^ V)) (v : Fin I → ℕ)
    (ho : ∀ j, o j = -1 ∨ o j = 0 ∨ o j = 1) (hω : ∀ j, (ω j).val % 2 = 1)
    (hv : ∀ i j, i < j → v j < v i) (hvb : ∀ j, ℓ + d + 3 ≤ v j ∧ v j ≤ V)
    (e e' : Fin I → Bool) (hmix : ∃ j, o j ≠ 0 ∧ e j ≠ e' j) :
    ∃ k, ℓ + d + 3 ≤ k ∧ k ≤ V ∧ ∃ ϑ : ZMod (2 ^ V), IsUnit ϑ ∧
      ∑ j, ((if e' j then (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) else 0) -
        (if e j then (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) else 0)) = 2 ^ (V - k) * ϑ := by
  classical
  set Sx := univ.filter (fun j => o j ≠ 0 ∧ e j ≠ e' j) with hSx
  have hne : Sx.Nonempty := by
    obtain ⟨j, hj⟩ := hmix
    exact ⟨j, by simp [hSx, hj]⟩
  set js := Sx.min' hne with hjs
  have hjsS : o js ≠ 0 ∧ e js ≠ e' js := by
    have := Sx.min'_mem hne
    simpa [hSx] using this
  have hmin : ∀ j, j < js → ¬ (o j ≠ 0 ∧ e j ≠ e' j) := by
    intro j hj hjS
    have : js ≤ j := Sx.min'_le j (by simp [hSx, hjS])
    exact absurd hj (not_lt.mpr this)
  -- the terms with `j < js` vanish.
  have hz : ∀ j, j < js → (kaB (e' j) - kaB (e j)) * (o j : ZMod (2 ^ V)) = 0 := by
    intro j hj
    have := hmin j hj
    rw [not_and_or, not_not, not_not] at this
    rcases this with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hV1 : 1 ≤ V := by have := hvb js; omega
  set k := v js with hk
  refine ⟨k, (hvb js).1, (hvb js).2, ?_⟩
  set ϑ : ZMod (2 ^ V) :=
    ∑ j, (kaB (e' j) - kaB (e j)) * (o j : ZMod (2 ^ V)) * ω j * 2 ^ (k - v j) with hϑ
  have hterm : ∀ j, ((if e' j then (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) else 0) -
        (if e j then (o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j) else 0)) =
      2 ^ (V - k) * ((kaB (e' j) - kaB (e j)) * (o j : ZMod (2 ^ V)) * ω j * 2 ^ (k - v j)) := by
    intro j
    rw [ka_ite_sub]
    by_cases hjk : v j ≤ k
    · have : (2 : ZMod (2 ^ V)) ^ (V - v j) = 2 ^ (V - k) * 2 ^ (k - v j) := by
        rw [← pow_add]
        congr 1
        have := (hvb js).2
        omega
      rw [this]
      ring
    · have hjlt : j < js := by
        by_contra hge
        rcases eq_or_lt_of_le (not_lt.mp hge) with h | h
        · exact hjk (by rw [hk, h])
        · exact hjk (le_of_lt (hv js j h))
      rw [show (kaB (e' j) - kaB (e j)) * ((o j : ZMod (2 ^ V)) * ω j * 2 ^ (V - v j)) =
          ((kaB (e' j) - kaB (e j)) * (o j : ZMod (2 ^ V))) * (ω j * 2 ^ (V - v j)) by ring,
        show (kaB (e' j) - kaB (e j)) * (o j : ZMod (2 ^ V)) * ω j * 2 ^ (k - v j) =
          ((kaB (e' j) - kaB (e j)) * (o j : ZMod (2 ^ V))) * (ω j * 2 ^ (k - v j)) by ring,
        hz j hjlt]
      simp
  refine ⟨ϑ, ?_, by rw [hϑ, mul_sum]; exact sum_congr rfl (fun j _ => hterm j)⟩
  -- `ϑ` is odd: its image in `ZMod 2` comes only from the term `j*`, and `±1 · ±1 · 1 = 1`.
  apply ka_isUnit_of_odd
  rw [ka_odd_iff V hV1, hϑ, map_sum]
  rw [sum_eq_single js]
  · have hωs : ZMod.castHom (ka_two_dvd V hV1) (ZMod 2) (ω js) = 1 := (ka_odd_iff V hV1 (ω js)).mp (hω js)
    rw [show k - v js = 0 by rw [hk, Nat.sub_self], pow_zero, mul_one, map_mul, map_mul, map_sub,
      map_intCast, ka_cast_kaB V hV1, ka_cast_kaB V hV1, hωs, mul_one]
    have hne' := hjsS.2
    have hpm : ((o js : ℤ) : ZMod 2) = 1 := by
      rcases ho js with h | h | h
      · rw [h]; decide
      · exact absurd h hjsS.1
      · rw [h]; decide
    rw [hpm, mul_one]
    cases hx : e js <;> cases hy : e' js
    · exact absurd (hx.trans hy.symm) hne'
    · decide
    · decide
    · exact absurd (hx.trans hy.symm) hne'
  · intro j _ hjne
    rcases lt_or_gt_of_ne hjne with h | h
    · rw [show (kaB (e' j) - kaB (e j)) * (o j : ZMod (2 ^ V)) * ω j * 2 ^ (k - v j) =
          ((kaB (e' j) - kaB (e j)) * (o j : ZMod (2 ^ V))) * (ω j * 2 ^ (k - v j)) by ring,
        hz j h]
      simp
    · have hlt : v j < k := hv js j h
      rw [map_mul, map_pow]
      have : (ZMod.castHom (ka_two_dvd V hV1) (ZMod 2) 2) ^ (k - v j) = 0 := by
        rw [map_ofNat]
        obtain ⟨r, hr⟩ : ∃ r, k - v j = r + 1 := ⟨k - v j - 1, by omega⟩
        rw [hr, pow_succ, show (2 : ZMod 2) = 0 by decide, mul_zero]
      rw [this, mul_zero]
  · intro h; exact absurd (mem_univ js) h

end Collatz.Arctic

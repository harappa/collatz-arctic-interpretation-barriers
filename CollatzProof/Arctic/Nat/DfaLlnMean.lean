/-
# Natural-number interpretations of 𝒯 (Section 12.4), part (2): stationary means of finite DFAs

The "stationary mean" `Q(φ)` of Definition 12.12 is defined **without constructing a stationary distribution**.

* A finite DFA `δ : S → Bool → S` reading from the most significant end (`Dfa.run`), and a function `φ : S → List Bool → ℝ` of a state and the window of the next `J` digits.
  The sum along a word `wsum δ J φ x w L = ∑_{p<L} φ(run δ x (w.take p), (w.drop p).take J)` (`ws(x, w, L)` of Definition 12.12).
* The expectation `mexp δ J φ x L`: the average of `wsum` over the uniform words of length `L + J`. The Markov property `mexp_add`.
* **Doeblin** (`Dfa2.count_words`): the difference of the expectations started from two states of the same cyclic class of the closed class is bounded
  independently of `L` (`osc_cls`, by the contraction of oscillations `contract` and strong induction). It is bounded also for different cyclic classes (`osc_all`; the length that aligns the classes is less than the period).
  **No period is assumed** (neither aperiodicity nor stationary distributions of irreducible chains are used).
* Fekete's lemma (Mathlib's `Subadditive`), applied from above and from below to the almost additive sequence `a_L := mexp δ J φ q₀ L` (`|a_{L+L'} - a_L - a_{L'}| ≤ K`),
  gives the **stationary mean** `statMean δ J φ q₀ := lim a_L / L` and the bound `|mexp δ J φ x L - statMean · L| ≤ K` (`mexp_near`), uniform over all
  starting states `x` of the class.
* Properties: `|statMean| ≤ C`; monotone, additive, homogeneous, determined by the values on the class (`statMean_congr`); unchanged when the window is lengthened
  (`statMean_take`) and when another state of the class is taken as the base point (`statMean_eq_of_reach`); **positivity** `statMean_pos`
  (if `φ ≥ 0` and `φ` is positive somewhere on the class, then `0 < statMean`; Lemma 12.14, replacing the positivity of stationary distributions of an earlier argument) and
  its corollary `eq_zero_of_statMean_eq_zero`.

An earlier written form defines `Q(ξ) := ∑_x π_𝔅(x) 𝔼[φ(x, ·)]` (with a stationary distribution `π_𝔅`). Here `statMean` is a Cesàro limit, and it is not proved
that the two values agree (downstream uses only the properties).
-/
import CollatzProof.Arctic.Nat.DfaLlnAvg

namespace Collatz.Arctic.NatQ5.W3d

open Collatz.Arctic Collatz.Arctic.Dfa Filter Topology

/-! ## Sums along words -/

section Wsum

variable {S : Type*} (δ : S → Bool → S) (J : ℕ) (φ : S → List Bool → ℝ)

/-- The sum of `φ` along the word `w`: the state `run δ x (w.take p)` at the position `p < L` and the following window `(w.drop p).take J`. -/
def wsum (x : S) (w : List Bool) (L : ℕ) : ℝ :=
  ∑ p ∈ Finset.range L, φ (run δ x (w.take p)) ((w.drop p).take J)

/-- The average of `wsum` over the uniform words of length `L + J`. -/
noncomputable def mexp (x : S) (L : ℕ) : ℝ := avg (L + J) (fun w => wsum δ J φ x w L)

/-- **The stationary mean**: the limit of `mexp δ J φ q₀ L / L` (it exists if `q₀` is recurrent: `tendsto_statMean`). -/
noncomputable def statMean (q₀ : S) : ℝ := limUnder atTop (fun L : ℕ => mexp δ J φ q₀ L / L)

variable {δ J φ}

theorem nonneg_of_bound {q₀ : S} {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) : 0 ≤ C :=
  le_trans (abs_nonneg _) (hC q₀ [])

@[simp] theorem wsum_zero (x : S) (w : List Bool) : wsum δ J φ x w 0 = 0 := by simp [wsum]

/-- The sum over an interval is additive (the part after `L` reads the rest of the word from the state at time `L`). -/
theorem wsum_add (x : S) (w : List Bool) (L L' : ℕ) :
    wsum δ J φ x w (L + L') = wsum δ J φ x w L + wsum δ J φ (run δ x (w.take L)) (w.drop L) L' := by
  unfold wsum
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [List.take_add, run_append, List.drop_drop]

/-- `wsum δ J φ x w L` depends only on the first `L + J` letters. -/
theorem wsum_take (x : S) (w : List Bool) {L n : ℕ} (hn : L + J ≤ n) :
    wsum δ J φ x (w.take n) L = wsum δ J φ x w L := by
  unfold wsum
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp' := Finset.mem_range.mp hp
  rw [List.take_take, List.drop_take, List.take_take, Nat.min_eq_left (by omega),
    Nat.min_eq_left (by omega)]

theorem abs_wsum_le {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) (x : S) (w : List Bool) (L : ℕ) :
    |wsum δ J φ x w L| ≤ L * C := by
  unfold wsum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_sum (fun p (_ : p ∈ Finset.range L) => hC (run δ x (w.take p)) ((w.drop p).take J))
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this

/-- For `n ≥ L + J`, the average over the words of length `n` is also `mexp`. -/
theorem avg_wsum (z : S) {L n : ℕ} (hn : L + J ≤ n) :
    avg n (fun v => wsum δ J φ z v L) = mexp δ J φ z L := by
  unfold mexp
  rw [← avg_take hn (fun v => wsum δ J φ z v L)]
  exact avg_congr (fun v _ => (wsum_take z v le_rfl).symm)

@[simp] theorem mexp_zero (x : S) : mexp δ J φ x 0 = 0 := by
  simp [mexp, avg_const]

theorem abs_mexp_le {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) (x : S) (L : ℕ) : |mexp δ J φ x L| ≤ L * C :=
  abs_avg_le_of (fun w _ => abs_wsum_le hC x w L)

/-- **The Markov property**: `mexp x (L + L') = mexp x L + 𝔼_u mexp (run x u) L'` (`u` a uniform word of length `L`). -/
theorem mexp_add (x : S) (L L' : ℕ) :
    mexp δ J φ x (L + L') = mexp δ J φ x L + avg L (fun u => mexp δ J φ (run δ x u) L') := by
  calc mexp δ J φ x (L + L')
      = avg (L + L' + J) (fun w => wsum δ J φ x w L +
          wsum δ J φ (run δ x (w.take L)) (w.drop L) L') := by
        unfold mexp
        exact avg_congr (fun w _ => wsum_add x w L L')
    _ = avg (L + L' + J) (fun w => wsum δ J φ x w L) +
          avg (L + L' + J) (fun w => wsum δ J φ (run δ x (w.take L)) (w.drop L) L') := avg_add _ _ _
    _ = mexp δ J φ x L + avg L (fun u => mexp δ J φ (run δ x u) L') := by
        congr 1
        · exact avg_wsum x (by omega)
        · rw [show L + L' + J = L + (L' + J) by omega, avg_append]
          refine avg_congr (fun u hu => ?_)
          rw [← avg_wsum (run δ x u) (le_refl (L' + J))]
          refine avg_congr (fun v _ => ?_)
          rw [List.take_left' hu, List.drop_left' hu]

/-- If `φ ≤ ψ` holds on the windows of length `J` over the class, then so does the inequality for `mexp`. -/
theorem mexp_mono {φ ψ : S → List Bool → ℝ} {q₀ : S}
    (h : ∀ x v, Reach δ q₀ x → v.length = J → φ x v ≤ ψ x v) {x : S} (hx : Reach δ q₀ x) (L : ℕ) :
    mexp δ J φ x L ≤ mexp δ J ψ x L := by
  unfold mexp
  refine avg_mono (fun w hw => Finset.sum_le_sum (fun p hp => h _ _ (hx.trans (reach_run x _)) ?_))
  have := Finset.mem_range.mp hp
  rw [List.length_take, List.length_drop, hw]
  omega

theorem mexp_add_fun (φ ψ : S → List Bool → ℝ) (x : S) (L : ℕ) :
    mexp δ J (fun y v => φ y v + ψ y v) x L = mexp δ J φ x L + mexp δ J ψ x L := by
  unfold mexp wsum
  rw [← avg_add]
  exact avg_congr (fun w _ => Finset.sum_add_distrib)

theorem mexp_mul_fun (c : ℝ) (φ : S → List Bool → ℝ) (x : S) (L : ℕ) :
    mexp δ J (fun y v => c * φ y v) x L = c * mexp δ J φ x L := by
  unfold mexp wsum
  rw [← avg_mul_left]
  exact avg_congr (fun w _ => (Finset.mul_sum _ _ _).symm)

end Wsum

/-! ## Doeblin and oscillations -/

section Osc

variable {S : Type*} [Fintype S] [DecidableEq S] {δ : S → Bool → S}

/-- **The Doeblin bound** (`Dfa2.count_words`): there is `L₀ ≥ 1` such that, for `n ≥ L₀` and every pair `x → z` in the class whose cyclic classes
differ by `n`, a uniform word of length `n` leads from `x` to `z` with probability at least `(1/2)^L₀`. -/
theorem doeblin {q₀ : S} (hrec : Recurrent δ q₀) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ n, L₀ ≤ n → ∀ x z, Reach δ q₀ x → Reach δ q₀ z →
      cls δ q₀ z = cls δ q₀ x + n → (1 / 2 : ℝ) ^ L₀ ≤ avg n (fun u => if run δ x u = z then 1 else 0) := by
  obtain ⟨L, hL⟩ := count_words hrec
  refine ⟨L + 1, by omega, fun n hn x z hx hz hcls => ?_⟩
  rw [avg_ind_eq_card]
  have h1 := hL n (by omega) x z hx hz hcls
  have h2 : ((2 : ℝ) ^ (n - L)) ≤
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun g => run δ x (List.ofFn g) = z)).card : ℝ) := by
    exact_mod_cast h1
  rw [le_div_iff₀ (by positivity)]
  have e : (2 : ℝ) ^ n = 2 ^ (n - L) * 2 ^ L := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have e2 : (1 / 2 : ℝ) ^ (L + 1) * (2 ^ (n - L) * 2 ^ L) = 2 ^ (n - L) / 2 := by
    rw [pow_succ, one_div_pow]
    field_simp
  rw [e, e2]
  have : (0 : ℝ) ≤ 2 ^ (n - L) := by positivity
  linarith

theorem half_pow_le {L₀ : ℕ} (h : 1 ≤ L₀) : (1 / 2 : ℝ) ^ L₀ ≤ 1 / 2 := by
  calc (1 / 2 : ℝ) ^ L₀ ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    _ = 1 / 2 := pow_one _

/-- **Contraction of oscillations**: for `x, y` in the same cyclic class, the averages of `g` after reading a uniform word of length `n ≥ L₀` differ by at
most `1 - 2(1/2)^L₀` times the oscillation of `g` on the target cyclic class. -/
theorem contract {q₀ : S} (hrec : Recurrent δ q₀) {L₀ : ℕ} (hL₀ : 1 ≤ L₀)
    (hD : ∀ n, L₀ ≤ n → ∀ x z, Reach δ q₀ x → Reach δ q₀ z →
      cls δ q₀ z = cls δ q₀ x + n → (1 / 2 : ℝ) ^ L₀ ≤ avg n (fun u => if run δ x u = z then 1 else 0))
    {n : ℕ} (hn : L₀ ≤ n) (g : S → ℝ) {K : ℝ}
    {x y : S} (hx : Reach δ q₀ x) (hy : Reach δ q₀ y) (hxy : cls δ q₀ x = cls δ q₀ y)
    (hK : ∀ z z', Reach δ q₀ z → Reach δ q₀ z' → cls δ q₀ z = cls δ q₀ x + n →
      cls δ q₀ z' = cls δ q₀ x + n → g z - g z' ≤ K) :
    avg n (fun u => g (run δ x u)) - avg n (fun u => g (run δ y u)) ≤ (1 - 2 * (1 / 2 : ℝ) ^ L₀) * K := by
  classical
  set T := Finset.univ.filter (fun z => Reach δ q₀ z ∧ cls δ q₀ z = cls δ q₀ x + n) with hT
  have hmemT : ∀ x' : S, Reach δ q₀ x' → cls δ q₀ x' = cls δ q₀ x → ∀ u : List Bool, u.length = n →
      run δ x' u ∈ T := by
    intro x' hx' hc u hu
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hx'.trans (reach_run x' u), by rw [cls_run hrec hx', hu, hc]⟩
  have hne : T.Nonempty := ⟨_, hmemT x hx rfl (List.replicate n false) (by simp)⟩
  obtain ⟨z₀, hz₀, hmin⟩ := T.exists_min_image g hne
  obtain ⟨z₁, hz₁, hmax⟩ := T.exists_max_image g hne
  have hz₀' := (Finset.mem_filter.mp hz₀).2
  have hz₁' := (Finset.mem_filter.mp hz₁).2
  have hgap : g z₁ - g z₀ ≤ K := hK z₁ z₀ hz₁'.1 hz₀'.1 hz₁'.2 hz₀'.2
  have hgap0 : 0 ≤ g z₁ - g z₀ := by linarith [hmin z₁ hz₁]
  have hup : avg n (fun u => g (run δ x u)) ≤
      g z₁ - (g z₁ - g z₀) * avg n (fun u => if run δ x u = z₀ then 1 else 0) := by
    have : avg n (fun u => g (run δ x u)) ≤
        avg n (fun u => g z₁ - (g z₁ - g z₀) * (if run δ x u = z₀ then 1 else 0)) := by
      refine avg_mono (fun u hu => ?_)
      by_cases h : run δ x u = z₀
      · simp [h]
      · simp only [h, ↓reduceIte, mul_zero, sub_zero]
        exact hmax _ (hmemT x hx rfl u hu)
    rwa [avg_sub, avg_const, avg_mul_left] at this
  have hlo : g z₀ + (g z₁ - g z₀) * avg n (fun u => if run δ y u = z₁ then 1 else 0) ≤
      avg n (fun u => g (run δ y u)) := by
    have : avg n (fun u => g z₀ + (g z₁ - g z₀) * (if run δ y u = z₁ then 1 else 0)) ≤
        avg n (fun u => g (run δ y u)) := by
      refine avg_mono (fun u hu => ?_)
      by_cases h : run δ y u = z₁
      · simp [h]
      · simp only [h, ↓reduceIte, mul_zero, add_zero]
        exact hmin _ (hmemT y hy hxy.symm u hu)
    rwa [avg_add, avg_const, avg_mul_left] at this
  have hx₀ := hD n hn x z₀ hx hz₀'.1 hz₀'.2
  have hy₁ := hD n hn y z₁ hy hz₁'.1 (by rw [hz₁'.2, hxy])
  have hc := half_pow_le hL₀
  have m1 := mul_le_mul_of_nonneg_left hx₀ hgap0
  have m2 := mul_le_mul_of_nonneg_left hy₁ hgap0
  have m3 := mul_le_mul_of_nonneg_right hgap (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 / 2 : ℝ) ^ L₀)
  nlinarith

variable (J : ℕ) {φ : S → List Bool → ℝ}

/-- **Oscillation on one cyclic class**: the difference of `mexp` started from two states of the same cyclic class is bounded independently of `L`. -/
theorem osc_cls {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L x y, Reach δ q₀ x → Reach δ q₀ y → cls δ q₀ x = cls δ q₀ y →
      mexp δ J φ x L - mexp δ J φ y L ≤ K := by
  obtain ⟨L₀, hL₀, hD⟩ := doeblin hrec
  have hC0 : 0 ≤ C := nonneg_of_bound (q₀ := q₀) hC
  have hc := half_pow_le hL₀
  have hcpos : (0 : ℝ) < (1 / 2) ^ L₀ := by positivity
  refine ⟨L₀ * C / (1 / 2) ^ L₀, by positivity, ?_⟩
  have hbase : 2 * (L₀ * C) ≤ L₀ * C / (1 / 2 : ℝ) ^ L₀ := by
    rw [le_div_iff₀ hcpos]
    have : (0 : ℝ) ≤ L₀ * C := by positivity
    nlinarith
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro x y hx hy hxy
    by_cases hL : L < L₀
    · have h1 := abs_le.mp (abs_mexp_le (δ := δ) (J := J) hC x L)
      have h2 := abs_le.mp (abs_mexp_le (δ := δ) (J := J) hC y L)
      have hL' : (L : ℝ) * C ≤ L₀ * C :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hL.le) hC0
      linarith
    · obtain ⟨L', rfl⟩ : ∃ L', L = L₀ + L' := ⟨L - L₀, by omega⟩
      rw [mexp_add, mexp_add]
      have hcon := contract hrec hL₀ hD (le_refl L₀) (fun z => mexp δ J φ z L') hx hy hxy
        (fun z z' hz hz' hcz hcz' => ih L' (by omega) z z' hz hz' (by rw [hcz, hcz']))
      have h1 := abs_le.mp (abs_mexp_le (δ := δ) (J := J) hC x L₀)
      have h2 := abs_le.mp (abs_mexp_le (δ := δ) (J := J) hC y L₀)
      have hK : 2 * (L₀ * C) + (1 - 2 * (1 / 2 : ℝ) ^ L₀) * (L₀ * C / (1 / 2) ^ L₀) =
          L₀ * C / (1 / 2) ^ L₀ := by
        field_simp
        ring
      linarith

/-- **Oscillation on the class**: the difference of `mexp` started from any two states of the class is bounded independently of `L` (the length that
aligns the cyclic classes is less than the period). -/
theorem osc_all {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L x y, Reach δ q₀ x → Reach δ q₀ y →
      |mexp δ J φ x L - mexp δ J φ y L| ≤ K := by
  obtain ⟨K₁, hK₁, h1⟩ := osc_cls J hrec hC
  have hC0 : 0 ≤ C := nonneg_of_bound (q₀ := q₀) hC
  have : NeZero (period δ q₀) := ⟨(period_pos δ q₀).ne'⟩
  have habs : ∀ L x y, Reach δ q₀ x → Reach δ q₀ y → cls δ q₀ x = cls δ q₀ y →
      |mexp δ J φ x L - mexp δ J φ y L| ≤ K₁ := by
    intro L x y hx hy hxy
    refine abs_le.mpr ⟨?_, h1 L x y hx hy hxy⟩
    have := h1 L y x hy hx hxy.symm
    linarith
  refine ⟨K₁ + 2 * period δ q₀ * C, by positivity, ?_⟩
  intro L x y hx hy
  set ℓ := (cls δ q₀ y - cls δ q₀ x).val with hℓdef
  have hℓ : cls δ q₀ x + ℓ = cls δ q₀ y := by
    rw [hℓdef, ZMod.natCast_zmod_val]
    ring
  have hℓP : (ℓ : ℝ) ≤ period δ q₀ := by exact_mod_cast (ZMod.val_lt _).le
  by_cases hL : ℓ ≤ L
  · obtain ⟨L', rfl⟩ : ∃ L', L = ℓ + L' := ⟨L - ℓ, by omega⟩
    have ex := mexp_add (δ := δ) (J := J) (φ := φ) x ℓ L'
    have ey := mexp_add (δ := δ) (J := J) (φ := φ) y L' ℓ
    rw [Nat.add_comm L' ℓ] at ey
    have hmid : |avg ℓ (fun u => mexp δ J φ (run δ x u) L') - mexp δ J φ y L'| ≤ K₁ :=
      abs_avg_sub_le (fun u hu => habs L' _ _ (hx.trans (reach_run x u)) hy
        (by rw [cls_run hrec hx, hu, hℓ]))
    have hA := abs_le.mp (abs_mexp_le (δ := δ) (J := J) hC x ℓ)
    have hB := abs_le.mp (abs_avg_le_of (n := L')
      (G := fun u => mexp δ J φ (run δ y u) ℓ) (fun u _ => abs_mexp_le hC _ ℓ))
    have hm := abs_le.mp hmid
    have hlC : (ℓ : ℝ) * C ≤ period δ q₀ * C := mul_le_mul_of_nonneg_right hℓP hC0
    rw [ex, ey]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  · have hA := abs_le.mp (abs_mexp_le (δ := δ) (J := J) hC x L)
    have hB := abs_le.mp (abs_mexp_le (δ := δ) (J := J) hC y L)
    have hlC : (L : ℝ) * C ≤ period δ q₀ * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show L ≤ period δ q₀ by
        have := ZMod.val_lt (cls δ q₀ y - cls δ q₀ x); omega)) hC0
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

end Osc

/-! ## Stationary means -/

section Mean

variable {S : Type*} [Fintype S] [DecidableEq S] {δ : S → Bool → S} (J : ℕ) {φ : S → List Bool → ℝ}

/-- Sequences with bounded difference have the same limit of averages. -/
theorem tendsto_div_of_abs_sub_le {f : ℕ → ℝ} {c K : ℝ} (h : ∀ L, |f L - c * L| ≤ K) :
    Tendsto (fun L : ℕ => f L / L) atTop (𝓝 c) := by
  have t1 : Tendsto (fun L : ℕ => c - K / (L : ℝ)) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).sub (tendsto_const_div_atTop_nhds_zero_nat K)
  have t2 : Tendsto (fun L : ℕ => c + K / (L : ℝ)) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).add (tendsto_const_div_atTop_nhds_zero_nat K)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' t1 t2 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    have e : c - K / L = (c * L - K) / L := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp (h L)).1]) hL'.le
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    have e : c + K / L = (c * L + K) / L := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp (h L)).2]) hL'.le

/-- **Existence of the stationary mean and uniform closeness**: if `q₀` is recurrent, then `mexp δ J φ q₀ L / L → statMean δ J φ q₀`, and
`|mexp δ J φ x L - statMean · L| ≤ K` for all starting states `x` of the class and all `L`. -/
theorem statMean_spec {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    Tendsto (fun L : ℕ => mexp δ J φ q₀ L / L) atTop (𝓝 (statMean δ J φ q₀)) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ L x, Reach δ q₀ x → |mexp δ J φ x L - statMean δ J φ q₀ * L| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := osc_all J hrec hC
  have hC0 : 0 ≤ C := nonneg_of_bound (q₀ := q₀) hC
  set a : ℕ → ℝ := fun L => mexp δ J φ q₀ L with ha
  have hadd : ∀ L L', |a (L + L') - a L - a L'| ≤ K := by
    intro L L'
    have e := mexp_add (δ := δ) (J := J) (φ := φ) q₀ L L'
    have h1 : |avg L (fun u => mexp δ J φ (run δ q₀ u) L') - a L'| ≤ K :=
      abs_avg_sub_le (fun u _ => hK L' _ _ ((Reach.refl q₀).trans (reach_run q₀ u)) (Reach.refl q₀))
    have e2 : a (L + L') - a L - a L' = avg L (fun u => mexp δ J φ (run δ q₀ u) L') - a L' := by
      simp only [ha]; rw [e]; ring
    rw [e2]; exact h1
  have hbd : ∀ L, |a L| ≤ L * C := fun L => abs_mexp_le hC q₀ L
  set u : ℕ → ℝ := fun L => a L + K with hu_def
  set v : ℕ → ℝ := fun L => K - a L with hv_def
  have hu : Subadditive u := fun m n => by
    have := (abs_le.mp (hadd m n)).2
    simp only [hu_def]; linarith
  have hv : Subadditive v := fun m n => by
    have := (abs_le.mp (hadd m n)).1
    simp only [hv_def]; linarith
  have hbdd : ∀ w : ℕ → ℝ, (∀ L, -(L * C) ≤ w L) → BddBelow (Set.range fun n => w n / n) := by
    intro w hw
    refine ⟨-C, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]; linarith
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [le_div_iff₀ hn']
      linarith [hw n]
  have hub := hbdd u (fun L => by simp only [hu_def]; linarith [(abs_le.mp (hbd L)).1])
  have hvb := hbdd v (fun L => by simp only [hv_def]; linarith [(abs_le.mp (hbd L)).2])
  have tu := hu.tendsto_lim hub
  have tv := hv.tendsto_lim hvb
  have tK : Tendsto (fun L : ℕ => K / (L : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat K
  have ta : Tendsto (fun L : ℕ => a L / L) atTop (𝓝 hu.lim) := by
    have := tu.sub tK
    rw [sub_zero] at this
    refine this.congr (fun L => ?_)
    simp only [hu_def]; ring
  have hQ : statMean δ J φ q₀ = hu.lim := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, ta⟩) ta
  have hvlim : hv.lim = -hu.lim := by
    have : Tendsto (fun L : ℕ => v L / L) atTop (𝓝 (0 - hu.lim)) :=
      (tK.sub ta).congr (fun L => by simp only [hv_def]; ring)
    rw [zero_sub] at this
    exact tendsto_nhds_unique tv this
  have hnear : ∀ L, |a L - statMean δ J φ q₀ * L| ≤ K := by
    intro L
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp only [ha, mexp_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero]; exact hK0
    · have hL' : (0 : ℝ) < L := by exact_mod_cast hL
      have h1 := hu.lim_le_div hub (n := L) (by omega)
      have h2 := hv.lim_le_div hvb (n := L) (by omega)
      rw [hvlim, le_div_iff₀ hL'] at h2
      rw [le_div_iff₀ hL'] at h1
      rw [hQ]
      simp only [hu_def, hv_def] at h1 h2
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  refine ⟨by rw [hQ]; exact ta, 2 * K, by positivity, fun L x hx => ?_⟩
  have h1 := hK L x q₀ hx (Reach.refl q₀)
  have h2 := hnear L
  calc |mexp δ J φ x L - statMean δ J φ q₀ * L|
      = |(mexp δ J φ x L - a L) + (a L - statMean δ J φ q₀ * L)| := by ring_nf
    _ ≤ |mexp δ J φ x L - a L| + |a L - statMean δ J φ q₀ * L| := abs_add_le _ _
    _ ≤ 2 * K := by linarith

theorem tendsto_statMean {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    Tendsto (fun L : ℕ => mexp δ J φ q₀ L / L) atTop (𝓝 (statMean δ J φ q₀)) :=
  (statMean_spec J hrec hC).1

/-- **Uniform closeness**: `|mexp δ J φ x L - statMean · L| ≤ K` for all starting states of the class (with `K` independent of `L`). -/
theorem mexp_near {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L x, Reach δ q₀ x → |mexp δ J φ x L - statMean δ J φ q₀ * L| ≤ K :=
  (statMean_spec J hrec hC).2

theorem abs_statMean_le {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    |statMean δ J φ q₀| ≤ C := by
  have hC0 : 0 ≤ C := nonneg_of_bound (q₀ := q₀) hC
  refine le_of_tendsto' (tendsto_statMean J hrec hC).abs (fun L => ?_)
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simpa using hC0
  · have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    rw [abs_div, Nat.abs_cast, div_le_iff₀ hL']
    have := abs_mexp_le (δ := δ) (J := J) hC q₀ L
    linarith

/-- The stationary mean does not change when another state of the class is taken as the base point. -/
theorem statMean_eq_of_reach {q₀ q₁ : S} (hrec : Recurrent δ q₀) (h : Reach δ q₀ q₁) {C : ℝ}
    (hC : ∀ x v, |φ x v| ≤ C) : statMean δ J φ q₁ = statMean δ J φ q₀ := by
  obtain ⟨K, -, hK⟩ := mexp_near J hrec hC
  exact tendsto_nhds_unique (tendsto_statMean J (hrec.of_reach h) hC)
    (tendsto_div_of_abs_sub_le (fun L => hK L q₁ h))

/-- **Monotonicity**: if `φ ≤ ψ` on the windows of length `J` over the class, then `statMean φ ≤ statMean ψ`. -/
theorem statMean_mono {q₀ : S} (hrec : Recurrent δ q₀) {ψ : S → List Bool → ℝ} {C D : ℝ}
    (hC : ∀ x v, |φ x v| ≤ C) (hD : ∀ x v, |ψ x v| ≤ D)
    (h : ∀ x v, Reach δ q₀ x → v.length = J → φ x v ≤ ψ x v) :
    statMean δ J φ q₀ ≤ statMean δ J ψ q₀ :=
  le_of_tendsto_of_tendsto' (tendsto_statMean J hrec hC) (tendsto_statMean J hrec hD)
    (fun L => div_le_div_of_nonneg_right (mexp_mono h (Reach.refl q₀) L) (Nat.cast_nonneg L))

/-- Functions that agree on the windows of length `J` over the class have the same stationary mean. -/
theorem statMean_congr {q₀ : S} (hrec : Recurrent δ q₀) {ψ : S → List Bool → ℝ} {C D : ℝ}
    (hC : ∀ x v, |φ x v| ≤ C) (hD : ∀ x v, |ψ x v| ≤ D)
    (h : ∀ x v, Reach δ q₀ x → v.length = J → φ x v = ψ x v) :
    statMean δ J φ q₀ = statMean δ J ψ q₀ :=
  le_antisymm (statMean_mono J hrec hC hD (fun x v hx hv => (h x v hx hv).le))
    (statMean_mono J hrec hD hC (fun x v hx hv => (h x v hx hv).ge))

theorem statMean_nonneg {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    (hφ : ∀ x v, Reach δ q₀ x → v.length = J → 0 ≤ φ x v) : 0 ≤ statMean δ J φ q₀ := by
  refine ge_of_tendsto' (tendsto_statMean J hrec hC) (fun L => div_nonneg ?_ (Nat.cast_nonneg L))
  have := mexp_mono (φ := fun _ _ => (0 : ℝ)) (ψ := φ) hφ (Reach.refl q₀) L
  have e : mexp δ J (fun _ _ => (0 : ℝ)) q₀ L = 0 := by simp [mexp, wsum, avg_const]
  linarith

/-- **Additivity**. -/
theorem statMean_add {q₀ : S} (hrec : Recurrent δ q₀) {ψ : S → List Bool → ℝ} {C D : ℝ}
    (hC : ∀ x v, |φ x v| ≤ C) (hD : ∀ x v, |ψ x v| ≤ D) :
    statMean δ J (fun x v => φ x v + ψ x v) q₀ = statMean δ J φ q₀ + statMean δ J ψ q₀ := by
  have hCD : ∀ x v, |φ x v + ψ x v| ≤ C + D := fun x v => (abs_add_le _ _).trans (add_le_add (hC x v) (hD x v))
  refine tendsto_nhds_unique (tendsto_statMean J hrec hCD) ?_
  refine ((tendsto_statMean J hrec hC).add (tendsto_statMean J hrec hD)).congr (fun L => ?_)
  rw [mexp_add_fun, add_div]

/-- **Homogeneity**. -/
theorem statMean_mul {q₀ : S} (hrec : Recurrent δ q₀) (c : ℝ) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C) :
    statMean δ J (fun x v => c * φ x v) q₀ = c * statMean δ J φ q₀ := by
  have hcC : ∀ x v, |c * φ x v| ≤ |c| * C := fun x v => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x v) (abs_nonneg c)
  refine tendsto_nhds_unique (tendsto_statMean J hrec hcC) ?_
  refine ((tendsto_statMean J hrec hC).const_mul c).congr (fun L => ?_)
  rw [mexp_mul_fun, mul_div_assoc]

omit [Fintype S] [DecidableEq S] in
/-- **Lengthening the window**: for `J ≤ J'`, a function that reads only the first `J` digits of a window of `J'` digits has the original stationary mean. -/
theorem statMean_take {J' : ℕ} (hJ : J ≤ J') (q₀ : S) :
    statMean δ J' (fun x v => φ x (v.take J)) q₀ = statMean δ J φ q₀ := by
  have e : ∀ x L, mexp δ J' (fun x v => φ x (v.take J)) x L = mexp δ J φ x L := by
    intro x L
    have e1 : ∀ w : List Bool, wsum δ J' (fun x v => φ x (v.take J)) x w L = wsum δ J φ x w L := by
      intro w
      unfold wsum
      refine Finset.sum_congr rfl (fun p _ => ?_)
      beta_reduce
      rw [List.take_take, Nat.min_eq_left hJ]
    unfold mexp
    simp_rw [e1]
    exact avg_wsum x (by omega)
  unfold statMean
  simp_rw [e]

/-- **Positivity** (Lemma 12.14; it replaces "a stationary distribution is positive on all states" of an earlier argument): if `φ ≥ 0` on the windows of length `J`
over the class, and `φ x₁ v₁ > 0` for a state `x₁` of the class and a window `v₁` of length `J`, then `statMean > 0`. -/
theorem statMean_pos {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    (hφ : ∀ x v, Reach δ q₀ x → v.length = J → 0 ≤ φ x v)
    {x₁ : S} {v₁ : List Bool} (hx₁ : Reach δ q₀ x₁) (hv₁ : v₁.length = J) (hpos : 0 < φ x₁ v₁) :
    0 < statMean δ J φ q₀ := by
  classical
  have hpath : ∀ z, Reach δ q₀ z → Reach δ z x₁ := fun z hz => (hrec z hz).trans hx₁
  let ℓ : S → ℕ := fun z => if h : Reach δ z x₁ then (Classical.choose h).length else 0
  set K := Finset.univ.sup ℓ + 1 with hKdef
  have hℓK : ∀ z, ℓ z < K := fun z => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ z))
  set c := (1 / 2 : ℝ) ^ (K + J) * φ x₁ v₁ with hcdef
  have hc : 0 < c := by positivity
  have hsum0 : ∀ z, Reach δ q₀ z → ∀ w : List Bool, w.length = K + J → 0 ≤ wsum δ J φ z w K := by
    intro z hz w hw
    refine Finset.sum_nonneg (fun p hp => hφ _ _ (hz.trans (reach_run z _)) ?_)
    have := Finset.mem_range.mp hp
    rw [List.length_take, List.length_drop, hw]
    omega
  have hstep : ∀ z, Reach δ q₀ z → c ≤ mexp δ J φ z K := by
    intro z hz
    have hr := hpath z hz
    have hu : run δ z (Classical.choose hr) = x₁ := Classical.choose_spec hr
    have hlt : (Classical.choose hr).length < K := by
      have := hℓK z
      simp only [ℓ, hr, ↓reduceDIte] at this
      exact this
    set u := Classical.choose hr with hudef
    have h1 : avg (K + J) (fun w => φ x₁ v₁ * (if w.take (u ++ v₁).length = u ++ v₁ then 1 else 0)) ≤
        mexp δ J φ z K := by
      unfold mexp
      refine avg_mono (fun w hw => ?_)
      by_cases hw' : w.take (u ++ v₁).length = u ++ v₁
      · simp only [hw', ↓reduceIte, mul_one]
        have hlen : (u ++ v₁).length = u.length + J := by rw [List.length_append, hv₁]
        rw [hlen, List.take_add] at hw'
        have ht : w.take u.length = u := by
          have := congrArg (List.take u.length) hw'
          rwa [List.take_left' (by rw [List.length_take]; omega),
            List.take_left' rfl] at this
        have hd : (w.drop u.length).take J = v₁ := by
          rw [ht] at hw'
          exact List.append_cancel_left hw'
        have hterm : φ (run δ z (w.take u.length)) ((w.drop u.length).take J) = φ x₁ v₁ := by
          rw [ht, hd, hu]
        rw [← hterm]
        unfold wsum
        refine Finset.single_le_sum (f := fun p => φ (run δ z (w.take p)) ((w.drop p).take J))
          (fun p hp => hφ _ _ (hz.trans (reach_run z _)) ?_) (Finset.mem_range.mpr hlt)
        have := Finset.mem_range.mp hp
        rw [List.length_take, List.length_drop, hw]
        omega
      · simp only [hw', ↓reduceIte, mul_zero]
        exact hsum0 z hz w hw
    rw [avg_mul_left, avg_ind_take (u ++ v₁) (by rw [List.length_append, hv₁]; omega)] at h1
    refine le_trans ?_ h1
    rw [hcdef, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
    rw [List.length_append, hv₁]
    omega
  have hmul : ∀ n : ℕ, n * c ≤ mexp δ J φ q₀ (n * K) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul, mexp_add]
      have h2 : c ≤ avg (n * K) (fun u => mexp δ J φ (run δ q₀ u) K) := by
        have := avg_mono (n := n * K) (G := fun _ => c) (H := fun u => mexp δ J φ (run δ q₀ u) K)
          (fun u _ => hstep _ ((Reach.refl q₀).trans (reach_run q₀ u)))
        rwa [avg_const] at this
      push_cast
      linarith
  obtain ⟨K', -, hK'⟩ := mexp_near J hrec hC
  by_contra hQ
  push Not at hQ
  obtain ⟨n, hn⟩ := exists_nat_gt (K' / c)
  have h1 := (abs_le.mp (hK' (n * K) q₀ (Reach.refl q₀))).2
  have h2 := hmul n
  have h3 : statMean δ J φ q₀ * ((n * K : ℕ) : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hQ (Nat.cast_nonneg _)
  rw [div_lt_iff₀ hc] at hn
  linarith

/-- **Corollary** (Lemma 12.14, in the form used for degeneration in Lemma 12.22): if `φ ≥ 0` on the class and `statMean = 0`, then `φ = 0` at every state of the class and
every window of length `J`. -/
theorem eq_zero_of_statMean_eq_zero {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    (hφ : ∀ x v, Reach δ q₀ x → v.length = J → 0 ≤ φ x v) (h0 : statMean δ J φ q₀ = 0)
    {x : S} (hx : Reach δ q₀ x) {v : List Bool} (hv : v.length = J) : φ x v = 0 := by
  by_contra hne
  have := statMean_pos J hrec hC hφ hx hv (lt_of_le_of_ne (hφ x v hx hv) (Ne.symm hne))
  linarith

/-- The stationary mean of the zero function is 0. -/
theorem statMean_zero {q₀ : S} (hrec : Recurrent δ q₀) :
    statMean δ J (fun _ _ => (0 : ℝ)) q₀ = 0 := by
  have h0 : ∀ (x : S) (v : List Bool), |(fun _ _ => (0 : ℝ)) x v| ≤ 0 := fun _ _ => by simp
  refine tendsto_nhds_unique (tendsto_statMean J hrec h0) ?_
  have e : (fun L : ℕ => mexp δ J (fun _ _ => (0 : ℝ)) q₀ L / L) = fun _ => 0 := by
    funext L
    simp [mexp, wsum, avg_const]
  rw [e]
  exact tendsto_const_nhds

/-- **`stat_mean_pos`** (Lemma 12.14, as an equivalence): if `φ ≥ 0` on the windows of length `J` over the class, then
`0 < statMean` ⟺ `φ > 0` at some state of the class and some window of length `J`. -/
theorem stat_mean_pos {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    (hφ : ∀ x v, Reach δ q₀ x → v.length = J → 0 ≤ φ x v) :
    0 < statMean δ J φ q₀ ↔ ∃ x v, Reach δ q₀ x ∧ v.length = J ∧ 0 < φ x v := by
  constructor
  · intro hQ
    by_contra hne
    push Not at hne
    have hle := statMean_mono J hrec hC (ψ := fun _ _ => (0 : ℝ)) (D := 0) (fun _ _ => by simp)
      (fun x v hx hv => hne x v hx hv)
    rw [statMean_zero J hrec] at hle
    linarith
  · rintro ⟨x, v, hx, hv, hpos⟩
    exact statMean_pos J hrec hC hφ hx hv hpos

/-- **`stat_mean_eq_zero`** (Lemma 12.14, the form used for degeneration, as an equivalence): if `φ ≥ 0` on the class, then
`statMean = 0` ⟺ `φ = 0` at every state of the class and every window of length `J`. -/
theorem stat_mean_eq_zero {q₀ : S} (hrec : Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    (hφ : ∀ x v, Reach δ q₀ x → v.length = J → 0 ≤ φ x v) :
    statMean δ J φ q₀ = 0 ↔ ∀ x v, Reach δ q₀ x → v.length = J → φ x v = 0 := by
  constructor
  · intro h0 x v hx hv
    exact eq_zero_of_statMean_eq_zero J hrec hC hφ h0 hx hv
  · intro h
    have := statMean_congr J hrec hC (ψ := fun _ _ => (0 : ℝ)) (D := 0) (fun _ _ => by simp) h
    rw [this, statMean_zero J hrec]

end Mean

end Collatz.Arctic.NatQ5.W3d

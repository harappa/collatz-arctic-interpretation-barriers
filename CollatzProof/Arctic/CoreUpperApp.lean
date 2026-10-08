/-
Lemma 6.5 of the paper applied to values (assembly of Theorem 6.8): the value `V = vecAfter u A w ⬝ᵥ c` of a word `pre ++ y₁ ++ u* ++ z`
is at most `(α_z + C₁ε)T + Cu`, using the rate `α_z(cfgOf y₁ X)` of the configuration at the configuration time `T = |pre ++ y₁ ++ u*|`
(`X` is the state of the support DFA after `pre`; this is the last step of the upper bound at `x₀` in the proof of Theorem 6.8:
a path that reaches the exit passes, at the configuration time, through an index that exits by `z`).
-/
import CollatzProof.Arctic.Upper
import CollatzProof.Arctic.CoreConfig

namespace Collatz.Arctic

open MinIdeal Matrix Classical

variable {D : ℕ}

/-- The rate of an index `b` that reaches the exit by `z` is at most the rate `α_z(I)` of the configuration. -/
lemma rhoB_le_alphaZ {E : BRel (Fin D)} (hE : E * E = E) (A : Interp D) (c : Fin D → Arc)
    (z : Word) (I : Set (Cls E hE)) (b : Fin D) (hb : ∃ j, ev A z b j ≠ 0 ∧ c j ≠ 0) :
    Upper.rhoB hE A I b ≤ alphaZ hE A c z I := by
  have hfin : Finite (Cls E hE) := inferInstanceAs (Finite (Quotient (clsSetoid hE)))
  have hbdd : BddAbove (visibleRates hE A c z I) := by
    refine ((Set.finite_range (classRate hE A)).subset ?_).bddAbove
    rintro r ⟨j, -, -, -, -, -, rfl⟩
    exact ⟨j, rfl⟩
  have hnn : 0 ≤ alphaZ hE A c z I :=
    Real.sSup_nonneg (by rintro r ⟨j, -, -, -, -, -, rfl⟩; exact rate_nonneg _ _)
  unfold Upper.rhoB
  by_cases hne : ({r | ∃ j ∈ I, (∃ p ∈ I, j ≤ p ∧ beta hE p b) ∧ r = classRate hE A j} : Set ℝ).Nonempty
  · apply csSup_le_csSup hbdd hne
    rintro r ⟨j, hj, ⟨p, hp, hjp, hpb⟩, rfl⟩
    obtain ⟨k, hk, hc⟩ := hb
    exact ⟨j, hj, p, hp, hjp, ⟨b, hpb, k, hk, hc⟩, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact hnn

/-- Upper bound for a finite value that has an upper bound in the natural numbers (a maximum that reads `-∞` as 0). -/
lemma fin_le_natOr0_sum {ι : Type*} [Fintype ι] (f : ι → Arc) (i : ι) (v : ℕ) (h : f i = Arc.fin v) :
    v ≤ natOr0 (∑ k, f k) := by
  have h1 : f i ≤ ∑ k, f k := Arc.le_sum_of_mem f (Finset.mem_univ i)
  have := natOr0_mono h1
  rwa [h, natOr0_fin] at this

/-- **Lemma 6.5 applied to values.** -/
theorem upper_value (A : Interp D) (u c : Fin D → Arc) {K : Set (BRel (Fin D))}
    (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) {E : BRel (Fin D)} (hEK : E ∈ K) (hE : E * E = E)
    (us : Word) (hus : IsDigits us) (hEus : suppRel (ev A us) = E) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∃ δ : ℚ, 0 < δ ∧ ∀ z : Word, ∃ Cu : ℝ,
      ∀ (pre y₁ : Word) (P : List Upper.Seg),
        IsDigits (pre ++ y₁ ++ us ++ z) → Upper.GoodPartition (pre ++ y₁ ++ us ++ z) P ε J δ →
        (pre ++ y₁ ++ us ++ z).length ≤ 2 * (pre ++ y₁ ++ us).length →
        ∀ V : ℕ, vecAfter u A (pre ++ y₁ ++ us ++ z) ⬝ᵥ c = Arc.fin V →
          (V : ℝ) ≤ (alphaZ hE A c z (cfgOf A hE y₁ (suppF (vecAfter u A pre))) + C₁ * ε) *
            (pre ++ y₁ ++ us).length + Cu := by
  obtain ⟨C₁, hC₁, hup⟩ := Upper.lemma_56_11_1 A u hK hEK hE us hus hEus
  refine ⟨C₁, hC₁, fun ε hε => ?_⟩
  obtain ⟨J, δ, hδ, Cu₀, hup'⟩ := hup ε hε
  refine ⟨J, δ, hδ, fun z => ⟨Cu₀ + natOr0 (∑ i, ∑ j, ev A z i j) + natOr0 (∑ j, c j), ?_⟩⟩
  intro pre y₁ P hdig hP hlen V hV
  set w₁ := pre ++ y₁ ++ us with hw₁
  set w := pre ++ y₁ ++ us ++ z with hw
  have hT : w₁.length ≤ w.length := by simp [hw, hw₁]
  have hww : w = w₁ ++ z := by simp [hw, hw₁]
  have hw₁' : w₁ = (pre ++ y₁) ++ us := rfl
  have hlen1 : w₁.length - us.length = (pre ++ y₁).length := by
    rw [hw₁', List.length_append]; omega
  have htake : w.take w₁.length = w₁ := by rw [hww, List.take_left']; rfl
  have htake' : w.take (w₁.length - us.length) = pre ++ y₁ := by
    rw [hlen1, hww, hw₁', List.append_assoc, List.take_left']; rfl
  have hwin : window w (w₁.length - us.length) us.length = us := by
    unfold window
    rw [hlen1, hww, hw₁', List.append_assoc, List.drop_left, List.take_left']; rfl
  -- the index `b` attaining the value (at the configuration time) and the exit `j`
  have hV' := hV
  rw [hww, vecAfter_append] at hV'
  change ∑ j, (∑ b, vecAfter u A w₁ b * ev A z b j) * c j = Arc.fin V at hV'
  have hne : (Finset.univ : Finset (Fin D)).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    rw [h0, Finset.sum_empty] at hV'
    exact absurd (congrArg Arc.val hV') (by simp)
  obtain ⟨j, -, hj⟩ := Arc.exists_eq_sum hne (fun j => (∑ b, vecAfter u A w₁ b * ev A z b j) * c j)
  rw [← hj] at hV'
  have hfj : Arc.val ((∑ b, vecAfter u A w₁ b * ev A z b j) * c j) ≠ ⊥ := by rw [hV']; simp
  obtain ⟨b, -, hb⟩ := Arc.exists_eq_sum hne (fun b => vecAfter u A w₁ b * ev A z b j)
  have hL := Arc.ne_bot_left hfj
  have hcj := Arc.ne_bot_right hfj
  rw [← hb] at hL hV'
  have hvb := Arc.ne_bot_left hL
  have hez := Arc.ne_bot_right hL
  obtain ⟨x, hx⟩ := (Arc.val_ne_bot_iff _).mp hvb
  obtain ⟨y, hy⟩ := (Arc.val_ne_bot_iff _).mp hez
  obtain ⟨q, hq⟩ := (Arc.val_ne_bot_iff _).mp hcj
  rw [hx, hy, hq, Arc.fin_mul_fin, Arc.fin_mul_fin] at hV'
  have hVeq : V = x + y + q := by
    have := congrArg Arc.val hV'
    simp only [Arc.val_fin] at this
    exact_mod_cast this.symm
  -- upper bound for the configuration time
  have hxb := hup' w P w₁.length hdig hP hlen hT (by rw [hw₁', List.length_append]; omega) hwin b x (by rw [htake]; exact hx)
  rw [htake'] at hxb
  rw [hitSet_vecAfter_eq_cfgOf] at hxb
  have hρ := rhoB_le_alphaZ hE A c z (cfgOf A hE y₁ (suppF (vecAfter u A pre))) b
    ⟨j, fun h0 => by rw [h0] at hy; exact absurd (congrArg Arc.val hy) (by simp),
      fun h0 => by rw [h0] at hq; exact absurd (congrArg Arc.val hq) (by simp)⟩
  have hy' : y ≤ natOr0 (∑ i, ∑ j, ev A z i j) := by
    have h1 := fin_le_natOr0_sum (fun j' => ev A z b j') j y hy
    have h2 : (∑ j', ev A z b j') ≤ ∑ i, ∑ j', ev A z i j' :=
      Arc.le_sum_of_mem (fun i => ∑ j', ev A z i j') (Finset.mem_univ b)
    exact h1.trans (natOr0_mono h2)
  have hq' : q ≤ natOr0 (∑ j, c j) := fin_le_natOr0_sum c j q hq
  have hTnn : (0 : ℝ) ≤ w₁.length := Nat.cast_nonneg _
  have : (Upper.rhoB hE A (cfgOf A hE y₁ (suppF (vecAfter u A pre))) b + C₁ * ε) * w₁.length ≤
      (alphaZ hE A c z (cfgOf A hE y₁ (suppF (vecAfter u A pre))) + C₁ * ε) * w₁.length :=
    mul_le_mul_of_nonneg_right (by linarith) hTnn
  rw [hVeq]
  push_cast
  have hy'' : (y : ℝ) ≤ natOr0 (∑ i, ∑ j, ev A z i j) := by exact_mod_cast hy'
  have hq'' : (q : ℝ) ≤ natOr0 (∑ j, c j) := by exact_mod_cast hq'
  linarith

end Collatz.Arctic

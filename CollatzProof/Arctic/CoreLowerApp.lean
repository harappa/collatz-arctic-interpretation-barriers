/-
Lemma 6.6 of the paper applied to values (assembly of Theorem 6.8), and existence of a digit word `u*` of type `E`.
* `lower_value`: the value `V` of a word `w₀ ++ u* ++ z` with the property `LowerAt` is at least `(α_z(I) - ε)N - Cst`
  (`I` is the set of classes hit by the support after `w₀`; this is the last sentence of Lemma 6.6: from the indices of `β_p` that reach the exit by `z`
  one reaches `c` with finite weight).
* `exists_ustar`: every element of the monoid `Mon (B0 A) (B1 A)` is the type of a digit word.
-/
import CollatzProof.Arctic.Lower
import CollatzProof.Arctic.CoreConfig

namespace Collatz.Arctic

open MinIdeal Matrix Classical

variable {D : ℕ}

/-- `Bool` to a digit letter (the inverse of `toBool`). -/
def ofBool (b : Bool) : Letter := if b then Letter.t else Letter.f

lemma toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b <;> simp [ofBool, toBool]

lemma map_toBool_ofBool (w : List Bool) : (w.map ofBool).map toBool = w := by
  simp [List.map_map, Function.comp_def, toBool_ofBool]

lemma isDigits_ofBool (w : List Bool) : IsDigits (w.map ofBool) := by
  intro s hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  cases b <;> simp [ofBool]

/-- Every element of the monoid is the type of a word. -/
theorem exists_typ_of_mem {Q : Type*} {B₀ B₁ X : BRel Q} (hX : X ∈ Mon B₀ B₁) :
    ∃ w : List Bool, typ B₀ B₁ w = X := by
  induction hX using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨[false], by simp [typ, letter]⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨[true], by simp [typ, letter]⟩
  | one => exact ⟨[], rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hy
    exact ⟨w ++ w', typ_append w w'⟩

/-- An element `E` of the monoid is the type of a digit word `u*`. -/
theorem exists_ustar (A : Interp D) {E : BRel (Fin D)} (hE : E ∈ Mon (B0 A) (B1 A)) :
    ∃ us : Word, IsDigits us ∧ suppRel (ev A us) = E := by
  obtain ⟨w, hw⟩ := exists_typ_of_mem hE
  refine ⟨w.map ofBool, isDigits_ofBool w, ?_⟩
  rw [suppRel_ev_digits A _ (isDigits_ofBool w), map_toBool_ofBool, hw]

/-- **Lemma 6.6 applied to values.** -/
theorem lower_value (u c : Fin D → Arc) (A : Interp D) {E : BRel (Fin D)} (hE : E * E = E)
    (us z w₀ : Word) (ε Cst : ℝ) (hε : 0 < ε) (hCst : 0 ≤ Cst) (hEus : suppRel (ev A us) = E)
    (hlow : Lower.LowerAt u A hE us z ε Cst (w₀ ++ us ++ z)) (V : ℕ)
    (hV : vecAfter u A (w₀ ++ us ++ z) ⬝ᵥ c = Arc.fin V) :
    (alphaZ hE A c z (hitSet hE (suppV (vecAfter u A w₀))) - ε) * (w₀ ++ us ++ z).length - Cst ≤ V := by
  set I := hitSet hE (suppV (vecAfter u A w₀)) with hI
  have hfin : Finite (Cls E hE) := inferInstanceAs (Finite (Quotient (clsSetoid hE)))
  have hlen1 : (w₀ ++ us ++ z).length - z.length - us.length = w₀.length := by simp; omega
  have hlen2 : (w₀ ++ us ++ z).length - z.length = (w₀ ++ us).length := by simp; omega
  have ht1 : (w₀ ++ us ++ z).take ((w₀ ++ us ++ z).length - z.length - us.length) = w₀ := by
    rw [hlen1, List.append_assoc, List.take_left']; rfl
  have ht2 : (w₀ ++ us ++ z).take ((w₀ ++ us ++ z).length - z.length) = w₀ ++ us := by
    rw [hlen2, List.take_left']; rfl
  unfold Lower.LowerAt at hlow
  rw [ht1, ht2] at hlow
  have hN : (0 : ℝ) ≤ (w₀ ++ us ++ z).length := Nat.cast_nonneg _
  by_cases hne : (visibleRates hE A c z I).Nonempty
  · have hvfin : (visibleRates hE A c z I).Finite :=
      (Set.finite_range (classRate hE A)).subset (by rintro r ⟨j, -, -, -, -, -, rfl⟩; exact ⟨j, rfl⟩)
    obtain ⟨j, hj, p, hp, hjp, ⟨k, hk, j', hez, hc⟩, hr⟩ := hne.csSup_mem hvfin
    -- `k` lies in the support at time `T`
    have hkS : k ∈ suppV (vecAfter u A (w₀ ++ us)) := by
      rw [suppV_vecAfter, suppRel_ev_append, hEus, ← act_mul, ← suppV_vecAfter,
        act_E_eq_betaUnion hE]
      exact ⟨p, hp, hk⟩
    obtain ⟨v, hv⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp hkS)
    have hlow' := hlow p hp j hj hjp k hk v hv
    -- `V ≥ v`
    obtain ⟨a, ha⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp hez)
    obtain ⟨q, hq⟩ := (Arc.val_ne_bot_iff _).mp ((Arc.ne_zero_iff_val _).mp hc)
    have hle : Arc.fin (v + a + q) ≤ Arc.fin V := by
      rw [← hV, vecAfter_append]
      change Arc.fin (v + a + q) ≤ ∑ j, (∑ b, vecAfter u A (w₀ ++ us) b * ev A z b j) * c j
      calc Arc.fin (v + a + q) = (vecAfter u A (w₀ ++ us) k * ev A z k j') * c j' := by
            rw [hv, ha, hq, Arc.fin_mul_fin, Arc.fin_mul_fin]
        _ ≤ (∑ b, vecAfter u A (w₀ ++ us) b * ev A z b j') * c j' :=
            Arc.mul_le_mul_of_le (Arc.le_sum_of_mem (fun b => vecAfter u A (w₀ ++ us) b * ev A z b j')
              (Finset.mem_univ k)) le_rfl
        _ ≤ _ := Arc.le_sum_of_mem (fun j => (∑ b, vecAfter u A (w₀ ++ us) b * ev A z b j) * c j)
              (Finset.mem_univ j')
    have hvV : v ≤ V := by have := Arc.fin_le_fin.mp hle; omega
    have : alphaZ hE A c z I = classRate hE A j := by
      unfold alphaZ; exact hr
    rw [this]
    have : (v : ℝ) ≤ V := by exact_mod_cast hvV
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold alphaZ
    rw [hne, Real.sSup_empty]
    have : (0 : ℝ) ≤ V := Nat.cast_nonneg _
    nlinarith

end Collatz.Arctic

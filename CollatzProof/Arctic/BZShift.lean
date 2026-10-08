/-
The translation below zero (`𝔸_ℤ`; Lemma 5.3 of the paper, carried out inside the proof of `barrier_of_auto_arcZ` and not stated separately).

* Lemmas on values in `ArcZ`, the semiring homomorphism `ArcZ.ofArcHom` of the embedding `𝔸_ℕ → 𝔸_ℤ`, the negative part `ArcZ.nb`, and `ArcZ.toArc`.
* `barrier_of_auto_arcZ`: an automaton `(u, A, c)` with entries in `ℤ ∪ {−∞}` whose values are natural numbers and decrease along steps of `T` by the number of
  uses of a strictly oriented rule contradicts `AutoCore`. After a translation by the sum `K` of the negative parts of the finite entries of the digit matrices (`K_u`, `K_c` for `u`, `c`),
  the values of the resulting automaton over `Arc` are `V(n) + K·lenT n + K_u + K_c` (all paths have length `lenT n`).
  From `V(T n) ≤ V(n)` one obtains the hypothesis of `AutoCore` with slope `κ = K`.
-/
import CollatzProof.Arctic.DPCanon
import CollatzProof.Arctic.AutoStatement

namespace Collatz.Arctic

open Matrix

namespace ArcZ

lemma ne_zero_iff (a : ArcZ) : a ≠ 0 ↔ val a ≠ ⊥ :=
  ⟨fun h hv => h (ext (by simpa using hv)), fun h h0 => h (by rw [h0]; rfl)⟩

lemma exists_fin_of_ne_zero {a : ArcZ} (ha : a ≠ 0) : ∃ z : ℤ, a = fin z := by
  obtain ⟨z, hz⟩ := WithBot.ne_bot_iff_exists.mp ((ne_zero_iff a).mp ha)
  exact ⟨z, ext (by rw [val_fin]; exact hz.symm)⟩

lemma fin_ne_zero (z : ℤ) : fin z ≠ 0 := by rw [ne_zero_iff]; simp

lemma fin_mul_fin (x y : ℤ) : fin x * fin y = fin (x + y) := ext (by simp)

lemma fin_add_fin (x y : ℤ) : fin x + fin y = fin (max x y) := ext (by simp)

lemma fin_le_fin {x y : ℤ} : fin x ≤ fin y ↔ x ≤ y := by rw [le_iff_val]; simp

lemma fin_lt_fin {x y : ℤ} : fin x < fin y ↔ x < y := by
  show val (fin x) < val (fin y) ↔ x < y
  simp

lemma fin_inj {x y : ℤ} (h : fin x = fin y) : x = y := by
  have := congrArg val h
  simpa using this

/-- In the arctic semiring, `l ≫ r` implies `r ⊗ 1 ≤ l`. -/
lemma gg_mul_fin_one {l r : ArcZ} (h : GG l r) : r * fin 1 ≤ l := by
  rcases h with hlt | ⟨-, hr⟩
  · by_cases hr0 : r = 0
    · rw [hr0, zero_mul, le_iff_val]; simp
    · obtain ⟨x, rfl⟩ := exists_fin_of_ne_zero hr0
      have hl0 : l ≠ 0 := by
        intro hl; rw [hl, ← not_le] at hlt; exact hlt (by rw [le_iff_val]; simp)
      obtain ⟨y, rfl⟩ := exists_fin_of_ne_zero hl0
      rw [fin_mul_fin, fin_le_fin]
      have := fin_lt_fin.mp hlt
      omega
  · rw [hr, zero_mul, le_iff_val]; simp

/-- `x^k = k·x` (arctic multiplication is addition). -/
lemma fin_pow (x : ℤ) (k : ℕ) : fin x ^ k = fin (k * x) := by
  induction k with
  | zero => simp; rfl
  | succ k ih => rw [pow_succ, ih, fin_mul_fin]; congr 1; push_cast; ring

/-- If `0 ≤ a` (finite and nonnegative), then `a` is the value of a natural number. -/
lemma exists_nat_of_le {a : ArcZ} (h : fin 0 ≤ a) : ∃ z : ℕ, a = fin z := by
  have ha : a ≠ 0 := by
    intro h0; rw [h0, le_iff_val] at h; simp at h
  obtain ⟨w, rfl⟩ := exists_fin_of_ne_zero ha
  rw [fin_le_fin] at h
  exact ⟨w.toNat, by rw [Int.toNat_of_nonneg h]⟩

/-- The size of the negative part (`(-z)⁺` for a finite value `z`, and 0 for −∞). -/
def nb (a : ArcZ) : ℕ := (-(WithBot.unbotD 0 (val a))).toNat

lemma nb_fin (z : ℤ) : nb (fin z) = (-z).toNat := rfl

/-- From `ArcZ` to `Arc` (nonnegative values are read as natural numbers; negative values are not used). -/
def toArc (a : ArcZ) : Arc := (WithBot.map Int.toNat (val a) : WithBot ℕ)

lemma ofArc_fin (n : ℕ) : ofArc (Arc.fin n) = fin n := rfl

lemma ofArc_zero : ofArc 0 = 0 := rfl

lemma arc_cases (a : Arc) : a = 0 ∨ ∃ n : ℕ, a = Arc.fin n := by
  by_cases h : a = 0
  · exact Or.inl h
  · exact Or.inr (Arc.exists_fin_of_ne_zero h)

/-- The embedding `𝔸_ℕ → 𝔸_ℤ` is a semiring homomorphism. -/
def ofArcHom : Arc →+* ArcZ where
  toFun := ofArc
  map_one' := rfl
  map_mul' a b := by
    rcases arc_cases a with rfl | ⟨m, rfl⟩
    · simp [ofArc_zero]
    rcases arc_cases b with rfl | ⟨n, rfl⟩
    · simp [ofArc_zero]
    rw [Arc.fin_mul_fin, ofArc_fin, ofArc_fin, ofArc_fin, fin_mul_fin]
    push_cast; rfl
  map_zero' := rfl
  map_add' a b := by
    rcases arc_cases a with rfl | ⟨m, rfl⟩
    · simp [ofArc_zero]
    rcases arc_cases b with rfl | ⟨n, rfl⟩
    · simp [ofArc_zero]
    have : Arc.fin m + Arc.fin n = Arc.fin (max m n) :=
      Arc.ext (by simp only [Arc.val_add, Arc.val_fin]; exact (WithBot.coe_max m n).symm)
    rw [this, ofArc_fin, ofArc_fin, ofArc_fin, fin_add_fin]
    push_cast; rfl

lemma ofArcHom_apply (a : Arc) : ofArcHom a = ofArc a := rfl

/-- If the image under the embedding is a natural number, the original value is the same natural number. -/
lemma ofArc_eq_fin {x : Arc} {k : ℕ} (h : ofArc x = fin k) : x = Arc.fin k := by
  rcases arc_cases x with rfl | ⟨m, rfl⟩
  · exact absurd h.symm (fin_ne_zero _)
  · rw [ofArc_fin] at h
    have := fin_inj h
    rw [show m = k by exact_mod_cast this]

/-- If the negative part is at most `K`, the value translated by `K` lies in `Arc`. -/
lemma ofArc_toArc_shift (K : ℕ) (a : ArcZ) (h : nb a ≤ K) :
    ofArc (toArc (fin K * a)) = fin K * a := by
  by_cases ha : a = 0
  · rw [ha, mul_zero]; rfl
  obtain ⟨z, rfl⟩ := exists_fin_of_ne_zero ha
  rw [fin_mul_fin]
  rw [nb_fin] at h
  have hz : 0 ≤ (K : ℤ) + z := by omega
  show fin (((K + z).toNat : ℕ) : ℤ) = fin (K + z)
  rw [Int.toNat_of_nonneg hz]

end ArcZ

/-- Multiplying all digit matrices by `a` multiplies the interpretation of a string by `a^{length}`. -/
lemma prod_map_smul {D : ℕ} (a : ArcZ) (B : Letter → Matrix (Fin D) (Fin D) ArcZ) :
    ∀ w : Word, (w.map (fun s => a • B s)).prod = a ^ w.length • (w.map B).prod := by
  intro w
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, smul_mul_smul_comm,
      List.length_cons, pow_succ']

/-- The value of an automaton over `ArcZ` (the `𝔸_ℤ` version of `autoVal`). -/
def autoValZ {D : ℕ} (u : Fin D → ArcZ) (A : Letter → Matrix (Fin D) (Fin D) ArcZ)
    (c : Fin D → ArcZ) (n : ℕ) : ArcZ :=
  u ⬝ᵥ (evR A (binTail n) *ᵥ c)

/-- **Barrier by translation** (the translation of Lemma 5.3 is carried out in this proof): an automaton with entries in `ℤ ∪ {−∞}` whose values are natural numbers and which satisfies the estimate along steps of `T`
(decrease by the number of uses of a strictly oriented rule) contradicts `AutoCore` (with slope `κ = K`). -/
theorem barrier_of_auto_arcZ (hcore : AutoCore) {D : ℕ} (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ) (σ : Rule) (hσ : σ ∈ rulesST)
    (hnn : ∀ n, ∃ z : ℕ, autoValZ u A c n = ArcZ.fin z)
    (hstep : ∀ n, 2 ≤ n → autoValZ u A c (T n) * ArcZ.fin 1 ^ (uses σ n) ≤ autoValZ u A c n) :
    False := by
  classical
  -- the width of the translation
  set K : ℕ := ∑ i, ∑ j, (ArcZ.nb (A Letter.f i j) + ArcZ.nb (A Letter.t i j)) with hK
  set Ku : ℕ := ∑ i, ArcZ.nb (u i) with hKu
  set Kc : ℕ := ∑ i, ArcZ.nb (c i) with hKc
  have hKA : ∀ s, s = Letter.f ∨ s = Letter.t → ∀ i j, ArcZ.nb (A s i j) ≤ K := by
    intro s hs i j
    have h1 : ArcZ.nb (A s i j) ≤ ArcZ.nb (A Letter.f i j) + ArcZ.nb (A Letter.t i j) := by
      rcases hs with rfl | rfl <;> omega
    have h2 : ArcZ.nb (A Letter.f i j) + ArcZ.nb (A Letter.t i j) ≤
        ∑ j', (ArcZ.nb (A Letter.f i j') + ArcZ.nb (A Letter.t i j')) :=
      Finset.single_le_sum (f := fun j' => ArcZ.nb (A Letter.f i j') + ArcZ.nb (A Letter.t i j'))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h3 : ∑ j', (ArcZ.nb (A Letter.f i j') + ArcZ.nb (A Letter.t i j')) ≤ K :=
      Finset.single_le_sum
        (f := fun i' => ∑ j', (ArcZ.nb (A Letter.f i' j') + ArcZ.nb (A Letter.t i' j')))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hKu' : ∀ i, ArcZ.nb (u i) ≤ Ku := fun i =>
    Finset.single_le_sum (f := fun i' => ArcZ.nb (u i')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hKc' : ∀ i, ArcZ.nb (c i) ≤ Kc := fun i =>
    Finset.single_le_sum (f := fun i' => ArcZ.nb (c i')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  -- the translated automaton over `Arc`
  let u' : Fin D → Arc := fun i => ArcZ.toArc (ArcZ.fin Ku * u i)
  let A' : Interp D := fun s => Matrix.of fun i j => ArcZ.toArc (ArcZ.fin K * A s i j)
  let c' : Fin D → Arc := fun i => ArcZ.toArc (ArcZ.fin Kc * c i)
  have hu' : (ArcZ.ofArcHom ∘ u') = ArcZ.fin Ku • u := by
    funext i; exact ArcZ.ofArc_toArc_shift Ku (u i) (hKu' i)
  have hc' : (ArcZ.ofArcHom ∘ c') = ArcZ.fin Kc • c := by
    funext i; exact ArcZ.ofArc_toArc_shift Kc (c i) (hKc' i)
  have hA' : ∀ s, s = Letter.f ∨ s = Letter.t → (A' s).map ArcZ.ofArcHom = ArcZ.fin K • A s := by
    intro s hs; ext i j
    exact ArcZ.ofArc_toArc_shift K (A s i j) (hKA s hs i j)
  -- key: the translated value is `V(n) + K_u + K·lenT n + K_c` (all paths have length `lenT n`)
  have hkey : ∀ n, ArcZ.ofArcHom (autoVal u' A' c' n) =
      ArcZ.fin ((Ku + K * lenT n + Kc : ℕ) : ℤ) * autoValZ u A c n := by
    intro n
    have hprod :
        (ev A' (binTail n)).map ArcZ.ofArcHom = ArcZ.fin K ^ lenT n • evR A (binTail n) := by
      unfold ev
      rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_map]
      rw [List.map_congr_left (g := fun s => ArcZ.fin K • A s)
        (fun s hs => by simpa using hA' s (binTail_letters n s hs))]
      exact prod_map_smul _ _ _
    unfold autoVal
    rw [RingHom.map_dotProduct, hu']
    have hmv : (ArcZ.ofArcHom ∘ (ev A' (binTail n) *ᵥ c')) =
        (ev A' (binTail n)).map ArcZ.ofArcHom *ᵥ (ArcZ.ofArcHom ∘ c') := by
      funext i; exact RingHom.map_mulVec _ _ _ i
    rw [hmv, hprod, hc', Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      dotProduct_smul, smul_dotProduct, ArcZ.fin_pow]
    simp only [smul_eq_mul, autoValZ, ← mul_assoc, ArcZ.fin_mul_fin]
    congr 2
    push_cast; ring
  have hval : ∀ n (z : ℕ), autoValZ u A c n = ArcZ.fin z →
      autoVal u' A' c' n = Arc.fin (Ku + K * lenT n + Kc + z) := by
    intro n z hz
    apply ArcZ.ofArc_eq_fin
    have := hkey n
    rw [hz, ArcZ.fin_mul_fin] at this
    rw [← ArcZ.ofArcHom_apply, this]
    push_cast; rfl
  -- the estimate for one step of `T` (in natural numbers)
  have hdrop : ∀ n, 2 ≤ n → ∀ a b : ℕ, autoValZ u A c n = ArcZ.fin a →
      autoValZ u A c (T n) = ArcZ.fin b → b + uses σ n ≤ a := by
    intro n hn a b ha hb
    have := hstep n hn
    rw [ha, hb, ArcZ.fin_pow, ArcZ.fin_mul_fin, ArcZ.fin_le_fin] at this
    omega
  -- apply `AutoCore` with slope `κ = K` (hypotheses: the values are finite and do not increase along steps of `T` by more than the slope `K`)
  obtain ⟨n, -, m, hm, hlt⟩ := hcore D u' A' c' K
    (by
      intro n _
      obtain ⟨z, hz⟩ := hnn n
      rw [hval n z hz]
      exact (Arc.ne_zero_iff _).mpr (by rw [Arc.val_fin]; exact WithBot.coe_ne_bot))
    (by
      intro n hn a b ha hb
      obtain ⟨z, hz⟩ := hnn n
      obtain ⟨z', hz'⟩ := hnn (T n)
      have h1 := hval n z hz
      have h2 := hval (T n) z' hz'
      rw [ha] at h1
      rw [hb] at h2
      have h1 := Arc.fin_inj h1
      have h2 := Arc.fin_inj h2
      have := hdrop n hn z z' hz hz'
      subst h1 h2
      omega)
    σ hσ 0
  -- contradiction between the conclusion `V(n) < number of uses` and the estimate `V(T^m n) + number of uses ≤ V(n)` along the orbit
  obtain ⟨z, hz⟩ := hnn n
  obtain ⟨z', hz'⟩ := hnn (T^[m] n)
  have horb := orbit_chain (fun n => autoValZ u A c n) (ArcZ.fin 1) σ hstep m n hm
  rw [hz, hz', ArcZ.fin_pow, ArcZ.fin_mul_fin, ArcZ.fin_le_fin] at horb
  rw [hval n z hz, Arc.fin_lt_fin] at hlt
  omega

end Collatz.Arctic

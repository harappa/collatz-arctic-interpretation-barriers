/-
The setting of the lineages (a step of the proof of `MinRate` in the general case: Theorem B.3, Step 3). We build the
classes of Lemma 6.2 and the lineages from the support of the digit matrices restricted to `C`.

* `LinSetup A C`: an idempotent `E` of the minimal ideal of the support monoid `Mon (B0 R) (B1 R)` (`R = restrictI C A`), a
  nonempty digit word `u` of type `E`, and the triviality (antichain) of the order of the classes. `hsp_exists_linSetup`: it exists
  if `C` is strongly connected (the antichain is `hsp_antichain`, the proof of `MinIdeal.antichain` rewritten to use only strong connectivity between the points of `C_E ⊆ C`).
* Composition of the permutations `π_X` (`Transport.piX`), `hsp_piX_comp`: `π_{X E Y} = π_Y ∘ π_X`.
* The set `realized` of permutations realized by words: closed under composition, identity and inverse, and transitive on the classes (strong connectivity).
  **Averaging lemma** `hsp_card_fiber`: the number of realized permutations `g` with `g k = j` does not depend on `j`.
-/
import CollatzProof.Arctic.HSPSp
import CollatzProof.Arctic.LowerPath

namespace Collatz.Arctic

open MinIdeal Matrix

variable {D : ℕ}

/-! ### Words of the support monoid -/

/-- An element of the monoid is the type of a digit word. -/
lemma hsp_exists_word (A : Interp D) {X : BRel (Fin D)} (hX : X ∈ Mon (B0 A) (B1 A)) :
    ∃ w : Word, IsDigits w ∧ suppRel (ev A w) = X := by
  induction hX using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · refine ⟨[Letter.f], fun s hs => by simp at hs; exact Or.inl hs, ?_⟩
      simp [ev, B0]
    · rw [Set.mem_singleton_iff] at hx; subst hx
      refine ⟨[Letter.t], fun s hs => by simp at hs; exact Or.inr hs, ?_⟩
      simp [ev, B1]
  | one => exact ⟨[], fun s hs => absurd hs List.not_mem_nil, by simp [ev, suppRel_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w ++ w', hsp_isDigits_append hw hw', suppRel_ev_append A w w'⟩

lemma hsp_suppRel_replicate (A : Interp D) (v : Word) :
    ∀ m : ℕ, suppRel (ev A (List.flatten (List.replicate m v))) = suppRel (ev A v) ^ m
  | 0 => by simp [ev, suppRel_one]
  | m + 1 => by
    rw [List.replicate_succ', List.flatten_append, suppRel_ev_append, hsp_suppRel_replicate A v m,
      pow_succ]
    simp

/-- For a nonempty word, the starting index of a finite entry of the restricted product lies in `C`. -/
lemma hsp_mem_of_ev_ne {A : Interp D} {C : Finset (Fin D)} {w : Word} (hw : w ≠ []) {x y : Fin D}
    (h : ev (restrictI C A) w x y ≠ 0) : x ∈ C := by
  obtain ⟨s, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  rw [ev_cons, Matrix.mul_apply, Arc.sum_ne_zero_iff] at h
  obtain ⟨k, -, hk⟩ := h
  rw [Arc.mul_ne_zero_iff] at hk
  unfold restrictI at hk
  by_contra hx
  exact hk.1 (by simp [hx])

/-! ### Antichain (from strong connectivity between the points of `C_E`) -/

/-- The form of `MinIdeal.antichain` that uses only connectivity between the points of `C_E`. -/
theorem hsp_antichain [Finite (Fin D)] {E : BRel (Fin D)} (hE : E * E = E)
    {M : Submonoid (BRel (Fin D))} (hgrp : ∀ X ∈ M, InH E (E * X * E))
    (hconn : ∀ x y, E x x → E y y → ∃ U ∈ M, U x y) :
    ∀ i j : Cls E hE, i ≤ j → i = j := by
  rintro ⟨pa⟩ ⟨pb⟩ hab
  apply le_antisymm hab
  obtain ⟨qa, ha⟩ := pa
  obtain ⟨qb, hb⟩ := pb
  have hab' : E qa qb := hab
  show E qb qa
  obtain ⟨U, hUM, hU⟩ := hconn qb qa hb ha
  have hR := hgrp U hUM
  have hba : (E * U * E) qb qa :=
    (BRel.mul_apply _ _ _ _).2 ⟨qa, (BRel.mul_apply _ _ _ _).2 ⟨qb, hb, hU⟩, ha⟩
  have hbb : (E * U * E) qb qb := by
    rw [← hR.mul_right hE]; exact (BRel.mul_apply _ _ _ _).2 ⟨qa, hba, hab'⟩
  have hpow : ∀ n, ((E * U * E) ^ (n + 1)) qb qa := by
    intro n
    induction n with
    | zero => simpa using hba
    | succ n ih => rw [pow_succ']; exact (BRel.mul_apply _ _ _ _).2 ⟨qb, hbb, ih⟩
  obtain ⟨m, hm, hmE⟩ := hR.exists_pow_eq hE
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
  have := hpow n
  rw [Nat.zero_add] at hmE
  rwa [hmE] at this

/-! ### The setting of the lineages -/

/-- The setting of the lineages: an idempotent `E` of the minimal ideal of the support monoid of the digit matrices restricted to `C`, a nonempty digit word `u` of type `E`,
and the triviality of the order of the classes. -/
structure LinSetup (A : Interp D) (C : Finset (Fin D)) where
  E : BRel (Fin D)
  hE : E * E = E
  hEM : E ∈ Mon (B0 (restrictI C A)) (B1 (restrictI C A))
  hgrp : ∀ X ∈ Mon (B0 (restrictI C A)) (B1 (restrictI C A)), InH E (E * X * E)
  u : Word
  hu : IsDigits u
  hu0 : u ≠ []
  huE : suppRel (ev (restrictI C A) u) = E
  hanti : ∀ i j : Cls E hE, i ≤ j → i = j

/-- **Existence of the setting of the lineages** (`C` strongly connected). -/
theorem hsp_exists_linSetup {A : Interp D} {C : Finset (Fin D)} (hSC : StrongConnIn A C) :
    Nonempty (LinSetup A C) := by
  set R := restrictI C A with hRdef
  obtain ⟨K, hK, E, hEK, hE⟩ := exists_minIdeal_idem (B0 R) (B1 R)
  have hEM : E ∈ Mon (B0 R) (B1 R) := hK.1.2.1 hEK
  have hgrp : ∀ X ∈ Mon (B0 R) (B1 R), InH E (E * X * E) := fun X hX =>
    inH_of_minIdeal hK hEK hE hX
  -- a word `us` of type `E`; make it nonempty by taking a power of `v := us f us`
  obtain ⟨us, hus, husE⟩ := hsp_exists_word R hEM
  have hfM : B0 R ∈ Mon (B0 R) (B1 R) := Submonoid.subset_closure (by simp)
  obtain ⟨m, hm, hmE⟩ := (hgrp (B0 R) hfM).exists_pow_eq hE
  set v : Word := us ++ [Letter.f] ++ us with hv
  have hvE : suppRel (ev R v) = E * B0 R * E := by
    rw [hv, suppRel_ev_append, suppRel_ev_append, husE]
    congr 2
    simp [ev, B0]
  set u : Word := List.flatten (List.replicate m v) with hudef
  have huE : suppRel (ev R u) = E := by rw [hudef, hsp_suppRel_replicate, hvE, hmE]
  have hu : IsDigits u := by
    intro s hs
    rw [hudef, List.mem_flatten] at hs
    obtain ⟨l, hl, hsl⟩ := hs
    rw [List.eq_of_mem_replicate hl, hv] at hsl
    rcases List.mem_append.mp hsl with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hus s h
      · simp at h; exact Or.inl h
    · exact hus s h
  have hu0 : u ≠ [] := by
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_lt hm
    simp [hudef, List.replicate_succ, hv]
  -- antichain
  have hCE : ∀ x, E x x → x ∈ C := fun x hx => by
    have : ev R u x x ≠ 0 := by
      have h := congrFun (congrFun huE x) x
      rw [← h] at hx; exact hx
    exact hsp_mem_of_ev_ne hu0 this
  have hconn : ∀ x y, E x x → E y y → ∃ U ∈ Mon (B0 R) (B1 R), U x y := by
    intro x y hx hy
    obtain ⟨w, hw, hxy⟩ := hSC x (hCE x hx) y (hCE y hy)
    exact ⟨suppRel (ev R w), suppRel_ev_mem R w hw, hxy⟩
  exact ⟨⟨E, hE, hEM, hgrp, u, hu, hu0, huE, hsp_antichain hE hgrp hconn⟩⟩

/-! ### Composition of permutations -/

/-- The classes are finite (`Fintype` by choice). -/
noncomputable instance hspFintypeCls {Q : Type*} [Finite Q] (E : BRel Q) (hE : E * E = E) :
    Fintype (Cls E hE) :=
  @Fintype.ofFinite _ (inferInstanceAs (Finite (Quotient (clsSetoid hE))))

noncomputable instance hspDecEqCls {Q : Type*} (E : BRel Q) (hE : E * E = E) :
    DecidableEq (Cls E hE) := Classical.decEq _

section Perm

variable {A : Interp D} {C : Finset (Fin D)} (S : LinSetup A C)

/-- Equal rows give equal rows of products. -/
lemma hsp_row_mul {X Y T : BRel (Fin D)} {q q' : Fin D} (h : X q = T q') :
    (X * Y) q = (T * Y) q' := by
  funext b
  apply propext
  simp only [BRel.mul_apply]
  rw [h]

lemma hsp_E_mul_E (Z : BRel (Fin D)) : S.E * (S.E * Z) = S.E * Z := by
  rw [← mul_assoc, S.hE]

/-- **Composition of permutations**: `π_{X E Y} = π_Y ∘ π_X`. -/
theorem hsp_piX_comp {X Y : BRel (Fin D)} (hX : X ∈ Mon (B0 (restrictI C A)) (B1 (restrictI C A)))
    (hY : Y ∈ Mon (B0 (restrictI C A)) (B1 (restrictI C A))) (i : Cls S.E S.hE) :
    piX S.hE (X * S.E * Y) i = piX S.hE Y (piX S.hE X i) := by
  have hXEY : X * S.E * Y ∈ Mon (B0 (restrictI C A)) (B1 (restrictI C A)) :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hX S.hEM) hY
  have key := piX_unique S.hE (S.hgrp _ hXEY)
    (π := fun i => piX S.hE Y (piX S.hE X i)) (fun q hq => ?_)
  · exact (congrFun key i).symm
  have e : S.E * (X * S.E * Y) * S.E = (S.E * X * S.E) * (S.E * Y * S.E) := by
    simp only [mul_assoc, hsp_E_mul_E]
  rw [e]
  obtain ⟨q'', hq'', hcl⟩ := cls_surj S.hE (piX S.hE X (cls S.hE q hq))
  have h1 : (S.E * X * S.E) q = S.E q'' := by
    rw [piX_spec S.hE (S.hgrp X hX) q hq, ← hcl, beta_cls]
  rw [hsp_row_mul h1]
  have e2 : S.E * (S.E * Y * S.E) = S.E * Y * S.E := by simp only [mul_assoc, hsp_E_mul_E]
  rw [e2, piX_spec S.hE (S.hgrp Y hY) q'' hq'', hcl]

/-- `π_E` is the identity. -/
lemma hsp_piX_E (i : Cls S.E S.hE) : piX S.hE S.E i = i := by
  have key := piX_unique S.hE (S.hgrp _ S.hEM) (π := id) (fun q hq => by
    simp only [S.hE, id, beta_cls])
  exact (congrFun key i).symm

lemma hsp_typ_mem {w : Word} (hw : IsDigits w) :
    suppRel (ev (restrictI C A) w) ∈ Mon (B0 (restrictI C A)) (B1 (restrictI C A)) :=
  suppRel_ev_mem _ w hw

/-- The permutation of the word `x u y` is `π_y ∘ π_x`. -/
lemma hsp_piX_word {x y : Word} (hx : IsDigits x) (hy : IsDigits y) (i : Cls S.E S.hE) :
    piX S.hE (suppRel (ev (restrictI C A) (x ++ S.u ++ y))) i =
      piX S.hE (suppRel (ev (restrictI C A) y)) (piX S.hE (suppRel (ev (restrictI C A) x)) i) := by
  rw [suppRel_ev_append, suppRel_ev_append, S.huE]
  exact hsp_piX_comp S (hsp_typ_mem hx) (hsp_typ_mem hy) i

/-! ### Permutations realized by words -/

/-- A permutation of the classes realized by a word. -/
def realized (g : Equiv.Perm (Cls S.E S.hE)) : Prop :=
  ∃ y : Word, IsDigits y ∧ ∀ i, g i = piX S.hE (suppRel (ev (restrictI C A) y)) i

lemma hsp_realized_one : realized S 1 :=
  ⟨S.u, S.hu, fun i => by rw [S.huE, hsp_piX_E]; rfl⟩

lemma hsp_realized_mul {g h : Equiv.Perm (Cls S.E S.hE)} (hg : realized S g) (hh : realized S h) :
    realized S (h * g) := by
  obtain ⟨y, hy, hyg⟩ := hg
  obtain ⟨y', hy', hyh⟩ := hh
  refine ⟨y ++ S.u ++ y', hsp_isDigits_append (hsp_isDigits_append hy S.hu) hy', fun i => ?_⟩
  rw [hsp_piX_word S hy hy', Equiv.Perm.mul_apply, hyg, hyh]

lemma hsp_realized_pow {g : Equiv.Perm (Cls S.E S.hE)} (hg : realized S g) :
    ∀ n : ℕ, realized S (g ^ n)
  | 0 => by rw [pow_zero]; exact hsp_realized_one S
  | n + 1 => by rw [pow_succ']; exact hsp_realized_mul S (hsp_realized_pow hg n) hg

lemma hsp_realized_inv {g : Equiv.Perm (Cls S.E S.hE)} (hg : realized S g) : realized S g⁻¹ := by
  have hpos := orderOf_pos g
  have h1 : g * g ^ (orderOf g - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [inv_eq_of_mul_eq_one_right h1]
  exact hsp_realized_pow S hg _

/-- Representatives of the classes lie in `C`. -/
lemma hsp_mem_C_of_E {q : Fin D} (hq : S.E q q) : q ∈ C := by
  have : ev (restrictI C A) S.u q q ≠ 0 := by
    have h := congrFun (congrFun S.huE q) q
    rw [← h] at hq; exact hq
  exact hsp_mem_of_ev_ne S.hu0 this

/-- **Transitivity** (strong connectivity): any two classes are mapped to each other by a realized permutation. -/
theorem hsp_realized_trans (hSC : StrongConnIn A C) (i j : Cls S.E S.hE) :
    ∃ g, realized S g ∧ g i = j := by
  obtain ⟨qi, hqi, rfl⟩ := cls_surj S.hE i
  obtain ⟨qj, hqj, rfl⟩ := cls_surj S.hE j
  obtain ⟨y, hy, hyne⟩ := hSC qi (hsp_mem_C_of_E S hqi) qj (hsp_mem_C_of_E S hqj)
  set Y := suppRel (ev (restrictI C A) y) with hYdef
  have hYM := hsp_typ_mem (A := A) (C := C) hy
  have hEYE : (S.E * Y * S.E) qi qj :=
    (BRel.mul_apply _ _ _ _).2 ⟨qj, (BRel.mul_apply _ _ _ _).2 ⟨qi, hqi, hyne⟩, hqj⟩
  rw [piX_spec S.hE (S.hgrp Y hYM) qi hqi] at hEYE
  have hcl := (beta_mem_C_of_antichain S.hE S.hanti _ qj hqj).1 hEYE
  exact ⟨(piX S.hE Y).toEquiv, ⟨y, hy, fun k => rfl⟩, hcl.symm⟩

/-- The finite set of realized permutations. -/
noncomputable def realSet : Finset (Equiv.Perm (Cls S.E S.hE)) := by
  classical exact Finset.univ.filter (realized S)

lemma hsp_mem_realSet {g : Equiv.Perm (Cls S.E S.hE)} : g ∈ realSet S ↔ realized S g := by
  classical
  unfold realSet
  simp

/-- **Averaging lemma**: the number of realized permutations `g` with `g k = j` does not depend on `j`. -/
theorem hsp_card_fiber (hSC : StrongConnIn A C) (k j : Cls S.E S.hE) :
    ((realSet S).filter (fun g => g k = j)).card = ((realSet S).filter (fun g => g k = k)).card := by
  obtain ⟨g₀, hg₀, hg₀k⟩ := hsp_realized_trans S hSC k j
  symm
  refine Finset.card_nbij' (fun g => g₀ * g) (fun g => g₀⁻¹ * g) ?_ ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_filter, hsp_mem_realSet] at hg ⊢
    exact ⟨hsp_realized_mul S hg.1 hg₀, by rw [Equiv.Perm.mul_apply, hg.2, hg₀k]⟩
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_filter, hsp_mem_realSet] at hg ⊢
    refine ⟨hsp_realized_mul S hg.1 (hsp_realized_inv S hg₀), ?_⟩
    rw [Equiv.Perm.mul_apply, hg.2, ← hg₀k]
    simp
  · intro g _
    simp only [inv_mul_cancel_left]
  · intro g _
    simp only [mul_inv_cancel_left]

end Perm

end Collatz.Arctic

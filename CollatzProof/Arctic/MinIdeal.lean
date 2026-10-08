/-
Lean proof of Lemma 6.2 (i)–(iv). The parts on general monoids and on the monoid of relations are in `MinIdealBase.lean`.
The overview is at the beginning of `MinIdealBase.lean`.
-/
import CollatzProof.Arctic.MinIdealBase

namespace Collatz.Arctic.MinIdeal

open BRel

/-! ## 3. Lemma 6.2 (i)(ii): factorization through `C_E` and classes -/

section Idem

variable {Q : Type*} {E : BRel Q}

theorem trans_of_idem (hE : E * E = E) {a b c : Q} (h1 : E a b) (h2 : E b c) : E a c := by
  rw [← hE]; exact (mul_apply E E a c).2 ⟨b, h1, h2⟩

theorem split_of_idem (hE : E * E = E) {a b : Q} (h : E a b) : ∃ c, E a c ∧ E c b := by
  rw [← hE] at h; exact (mul_apply E E a b).1 h

/-- **Lemma 6.2 (i)**: every edge `a → b` of `E` factors as `a → c → b` through some `c ∈ C_E` (`E c c`)
(the sequence obtained by taking the next `c'` from `E c b` is finite, hence repeats, and transitivity gives `E c c`). -/
theorem factor [Finite Q] (hE : E * E = E) {a b : Q} (h : E a b) :
    ∃ c, E c c ∧ E a c ∧ E c b := by
  have hnext : ∀ c : {c : Q // E a c ∧ E c b}, ∃ c' : {c : Q // E a c ∧ E c b}, E c.1 c'.1 := by
    rintro ⟨c, hac, hcb⟩
    obtain ⟨c', h1, h2⟩ := split_of_idem hE hcb
    exact ⟨⟨c', trans_of_idem hE hac h1, h2⟩, h1⟩
  choose nx hnx using hnext
  obtain ⟨c0, h1, h2⟩ := split_of_idem hE h
  let sq : ℕ → {c : Q // E a c ∧ E c b} := fun n => nx^[n] ⟨c0, h1, h2⟩
  have hs : ∀ n, sq (n + 1) = nx (sq n) := fun n => Function.iterate_succ_apply' nx n _
  have hchain : ∀ i k, E (sq i).1 (sq (i + k + 1)).1 := by
    intro i k
    induction k with
    | zero => rw [Nat.add_zero, hs]; exact hnx _
    | succ k ih =>
      rw [show i + (k + 1) + 1 = (i + k + 1) + 1 by omega, hs]
      exact trans_of_idem hE ih (hnx _)
  have key : ∀ i j, i < j → sq i = sq j → ∃ c, E c c ∧ E a c ∧ E c b := by
    intro i j hij heq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨(sq i).1, ?_, (sq i).2.1, (sq i).2.2⟩
    have := hchain i k
    rwa [← heq] at this
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite sq
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt heq
  · exact key j i hlt heq.symm

/-- The equivalence on `C_E` (the preorder `E` in both directions). -/
def clsSetoid (hE : E * E = E) : Setoid {k : Q // E k k} where
  r p p' := E p.1 p'.1 ∧ E p'.1 p.1
  iseqv := ⟨fun p => ⟨p.2, p.2⟩, fun h => ⟨h.2, h.1⟩,
    fun h1 h2 => ⟨trans_of_idem hE h1.1 h2.1, trans_of_idem hE h2.2 h1.2⟩⟩

/-- Classes (the equivalence classes of the preorder `E` on `C_E`; `Q_1, …, Q_r` in the paper). -/
def Cls (E : BRel Q) (hE : E * E = E) : Type _ := Quotient (clsSetoid hE)

/-- The class of an index `k ∈ C_E`. -/
def cls (hE : E * E = E) (k : Q) (hk : E k k) : Cls E hE := Quotient.mk (clsSetoid hE) ⟨k, hk⟩

/-- The order of the classes: `[k] ≤ [k'] ↔ E k k'`. -/
def clsLe (hE : E * E = E) : Cls E hE → Cls E hE → Prop :=
  Quotient.lift₂ (s₁ := clsSetoid hE) (s₂ := clsSetoid hE) (fun p p' => E p.1 p'.1) (by
    rintro p₁ q₁ p₂ q₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    exact propext ⟨fun h => trans_of_idem hE (trans_of_idem hE h₁' h) h₂,
      fun h => trans_of_idem hE (trans_of_idem hE h₁ h) h₂'⟩)

instance instPartialOrderCls (hE : E * E = E) : PartialOrder (Cls E hE) where
  le := clsLe hE
  le_refl := by rintro ⟨p⟩; exact p.2
  le_trans := by rintro ⟨p⟩ ⟨p'⟩ ⟨p''⟩ h h'; exact trans_of_idem hE h h'
  le_antisymm := by rintro ⟨p⟩ ⟨p'⟩ h h'; exact Quotient.sound ⟨h, h'⟩

theorem cls_le_cls (hE : E * E = E) {k k' : Q} (hk : E k k) (hk' : E k' k') :
    cls hE k hk ≤ cls hE k' hk' ↔ E k k' := Iff.rfl

theorem cls_eq_cls (hE : E * E = E) {k k' : Q} (hk : E k k) (hk' : E k' k') :
    cls hE k hk = cls hE k' hk' ↔ E k k' ∧ E k' k :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem cls_surj (hE : E * E = E) (i : Cls E hE) : ∃ k hk, cls hE k hk = i := by
  obtain ⟨p⟩ := i; exact ⟨p.1, p.2, rfl⟩

/-- The row `β_i` of a class (`E_q = β_i` for `q ∈ Q_i`; well-definedness is "rows are constant on classes"). -/
def beta (hE : E * E = E) : Cls E hE → Q → Prop :=
  Quotient.lift (s := clsSetoid hE) (fun p => E p.1) (by
    rintro p p' ⟨h, h'⟩
    funext b
    exact propext ⟨fun hb => trans_of_idem hE h' hb, fun hb => trans_of_idem hE h hb⟩)

theorem beta_cls (hE : E * E = E) (k : Q) (hk : E k k) : beta hE (cls hE k hk) = E k := rfl

/-- **Lemma 6.2 (ii), rows are constant on classes**: indices of the same class have equal rows. -/
theorem row_eq_of_cls_eq (hE : E * E = E) {k k' : Q} (hk : E k k) (hk' : E k' k')
    (h : cls hE k hk = cls hE k' hk') : E k = E k' := by
  rw [← beta_cls hE k hk, h, beta_cls]

/-- `s` hits the class `i`: `E s k` for some index `k` of `i`. -/
def Hits (hE : E * E = E) (s : Q) (i : Cls E hE) : Prop := ∃ k hk, cls hE k hk = i ∧ E s k

/-- **Lemma 6.2 (ii), a row is the union of the β of the classes hit**: `E_s = ⋃_{s hits i} β_i`. -/
theorem row_eq_union [Finite Q] (hE : E * E = E) (s b : Q) :
    E s b ↔ ∃ i, Hits hE s i ∧ beta hE i b := by
  constructor
  · intro h
    obtain ⟨c, hc, hsc, hcb⟩ := factor hE h
    exact ⟨cls hE c hc, ⟨c, hc, rfl, hsc⟩, hcb⟩
  · rintro ⟨i, ⟨k, hk, rfl, hsk⟩, hb⟩
    exact trans_of_idem hE hsk hb

/-- **Lemma 6.2 (ii), `β_i ∩ C_E` is the union of the classes `≥ i`**: `k ∈ C_E` lies in `β_i` iff `[k]` is at least `i`. -/
theorem beta_mem_C (hE : E * E = E) (i : Cls E hE) (k : Q) (hk : E k k) :
    beta hE i k ↔ i ≤ cls hE k hk := by
  obtain ⟨p⟩ := i; exact Iff.rfl

/-- Inclusion of rows of classes reverses the order: `β_j ⊆ β_i ↔ i ≤ j`. -/
theorem beta_subset_iff (hE : E * E = E) (i j : Cls E hE) :
    (∀ b, beta hE j b → beta hE i b) ↔ i ≤ j := by
  obtain ⟨p⟩ := i
  obtain ⟨p'⟩ := j
  constructor
  · intro h; exact h p'.1 p'.2
  · intro h b hb; exact trans_of_idem hE h hb

theorem beta_injective (hE : E * E = E) : Function.Injective (beta hE) := by
  intro i j h
  apply le_antisymm
  · exact (beta_subset_iff hE i j).1 (fun b hb => h ▸ hb)
  · exact (beta_subset_iff hE j i).1 (fun b hb => h.symm ▸ hb)

/-- The row of a class is nonempty (it contains the indices of the class). -/
theorem beta_nonempty (hE : E * E = E) (i : Cls E hE) : ∃ b, beta hE i b := by
  obtain ⟨p⟩ := i; exact ⟨p.1, p.2⟩

/-- If `E` is not the empty relation, there is a class (the assumption that `M` does not contain zero is used only here). -/
theorem nonempty_cls [Finite Q] (hE : E * E = E) (h : ∃ a b, E a b) : Nonempty (Cls E hE) := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨c, hc, -, -⟩ := factor hE hab
  exact ⟨cls hE c hc⟩

end Idem

/-! ## 4. Lemma 6.2 (iii): elements of `𝒢_E` permute the classes by order automorphisms -/

section Perm

variable {Q : Type*} {E : BRel Q}

/-- An element `R` of `𝒢_E` and its inverse `R'`. -/
structure HElem (E : BRel Q) where
  R : BRel Q
  R' : BRel Q
  hR : E * R * E = R
  hR' : E * R' * E = R'
  mul_inv : R * R' = E
  inv_mul : R' * R = E

/-- The inverse side. -/
def HElem.symm (h : HElem E) : HElem E := ⟨h.R', h.R, h.hR', h.hR, h.inv_mul, h.mul_inv⟩

theorem HElem.ofInH {R : BRel Q} (h : InH E R) : ∃ g : HElem E, g.R = R := by
  obtain ⟨hR, R', hR', h1, h2⟩ := h
  exact ⟨⟨R, R', hR, hR', h1, h2⟩, rfl⟩

theorem HElem.inH (g : HElem E) : InH E g.R := ⟨g.hR, g.R', g.hR', g.mul_inv, g.inv_mul⟩

theorem HElem.mul_left (hE : E * E = E) (g : HElem E) : E * g.R = g.R := g.inH.mul_left hE

theorem HElem.mul_right (hE : E * E = E) (g : HElem E) : g.R * E = g.R := g.inH.mul_right hE

/-- Witness: if `E q q`, there is `k` with `R q k ∧ R' k q` (`E q q = (R R')_{qq}`). -/
theorem HElem.exists_wit (g : HElem E) {q : Q} (hq : E q q) : ∃ k, g.R q k ∧ g.R' k q := by
  rw [← g.mul_inv] at hq; exact (mul_apply g.R g.R' q q).1 hq

/-- The witness lies in `C_E` (`(R' R)_{kk} = E_{kk}`). -/
theorem HElem.wit_mem (g : HElem E) {q k : Q} (h1 : g.R q k) (h2 : g.R' k q) : E k k := by
  rw [← g.inv_mul]; exact (mul_apply g.R' g.R k k).2 ⟨q, h2, h1⟩

/-- The row of the witness: if `R q k ∧ R' k q`, then `R_q = E_k`. -/
theorem HElem.row_of_wit (hE : E * E = E) (g : HElem E) {q k : Q} (h1 : g.R q k)
    (h2 : g.R' k q) : g.R q = E k := by
  funext b
  apply propext
  constructor
  · intro h; rw [← g.inv_mul]; exact (mul_apply g.R' g.R k b).2 ⟨q, h2, h⟩
  · intro h; rw [← g.mul_right hE]; exact (mul_apply g.R E q b).2 ⟨k, h1, h⟩

/-- If `E q q'`, then `R_q ⊇ R_{q'}` (`E R = R`). -/
theorem HElem.row_mono (hE : E * E = E) (g : HElem E) {q q' : Q} (h : E q q') (b : Q)
    (hb : g.R q' b) : g.R q b := by
  rw [← g.mul_left hE]; exact (mul_apply E g.R q b).2 ⟨q', h, hb⟩

/-- The map on representatives (the class of the witness). -/
noncomputable def HElem.piRep (hE : E * E = E) (g : HElem E) (p : {k : Q // E k k}) : Cls E hE :=
  cls hE (g.exists_wit p.2).choose
    (g.wit_mem (g.exists_wit p.2).choose_spec.1 (g.exists_wit p.2).choose_spec.2)

theorem HElem.beta_piRep (hE : E * E = E) (g : HElem E) (p : {k : Q // E k k}) :
    beta hE (g.piRep hE p) = g.R p.1 :=
  (g.row_of_wit hE (g.exists_wit p.2).choose_spec.1 (g.exists_wit p.2).choose_spec.2).symm

/-- The map `π_R` on classes (determined by `R_q = β_{π_R [q]}`). -/
noncomputable def HElem.pi (hE : E * E = E) (g : HElem E) : Cls E hE → Cls E hE :=
  Quotient.lift (s := clsSetoid hE) (g.piRep hE) (by
    rintro p p' ⟨h, h'⟩
    apply beta_injective hE
    rw [g.beta_piRep, g.beta_piRep]
    funext b
    exact propext ⟨g.row_mono hE h' b, g.row_mono hE h b⟩)

/-- `R_q = β_{π_R [q]}`. -/
theorem HElem.row_pi (hE : E * E = E) (g : HElem E) (q : Q) (hq : E q q) :
    g.R q = beta hE (g.pi hE (cls hE q hq)) :=
  (g.beta_piRep hE ⟨q, hq⟩).symm

/-- Characterization of `π_R`: if `β_j = R_q`, then `π_R [q] = j`. -/
theorem HElem.pi_eq_of_beta (hE : E * E = E) (g : HElem E) {q : Q} (hq : E q q) {j : Cls E hE}
    (h : beta hE j = g.R q) : g.pi hE (cls hE q hq) = j :=
  beta_injective hE (by rw [← g.row_pi hE q hq, h])

theorem HElem.pi_mono (hE : E * E = E) (g : HElem E) : Monotone (g.pi hE) := by
  rintro ⟨p⟩ ⟨p'⟩ h
  have h' : E p.1 p'.1 := h
  apply (beta_subset_iff hE _ _).1
  intro b hb
  change beta hE (g.pi hE (cls hE p'.1 p'.2)) b at hb
  change beta hE (g.pi hE (cls hE p.1 p.2)) b
  rw [← g.row_pi hE p.1 p.2]
  rw [← g.row_pi hE p'.1 p'.2] at hb
  exact g.row_mono hE h' b hb

/-- `π_{R'} ∘ π_R = id`: if `R q k ∧ R' k q`, then `R'_k = E_q`. -/
theorem HElem.pi_symm_pi (hE : E * E = E) (g : HElem E) (i : Cls E hE) :
    g.symm.pi hE (g.pi hE i) = i := by
  obtain ⟨p⟩ := i
  obtain ⟨k, h1, h2⟩ := g.exists_wit p.2
  have hk : E k k := g.wit_mem h1 h2
  have hpi : g.pi hE (cls hE p.1 p.2) = cls hE k hk :=
    g.pi_eq_of_beta hE p.2 (by rw [beta_cls]; exact (g.row_of_wit hE h1 h2).symm)
  change g.symm.pi hE (g.pi hE (cls hE p.1 p.2)) = cls hE p.1 p.2
  rw [hpi]
  exact g.symm.pi_eq_of_beta hE hk (by rw [beta_cls]; exact (g.symm.row_of_wit hE h2 h1).symm)

/-- The order automorphism `π_R` of **Lemma 6.2 (iii)**. -/
noncomputable def HElem.piIso (hE : E * E = E) (g : HElem E) : Cls E hE ≃o Cls E hE where
  toFun := g.pi hE
  invFun := g.symm.pi hE
  left_inv := g.pi_symm_pi hE
  right_inv := g.symm.pi_symm_pi hE
  map_rel_iff' := by
    intro i j
    constructor
    · intro h
      have := g.symm.pi_mono hE (show g.pi hE i ≤ g.pi hE j from h)
      rwa [g.pi_symm_pi hE, g.pi_symm_pi hE] at this
    · intro h; exact g.pi_mono hE h

/-- **Lemma 6.2 (iii)**: for `R ∈ 𝒢_E` there is an order automorphism `π_R` of the classes such that
`R_q = β_{π_R(i)}` for `q ∈ Q_i`. `π_R` is unique with this property. -/
theorem perm_of_inH (hE : E * E = E) {R : BRel Q} (hR : InH E R) :
    ∃ π : Cls E hE ≃o Cls E hE, ∀ q (hq : E q q), R q = beta hE (π (cls hE q hq)) := by
  obtain ⟨g, rfl⟩ := HElem.ofInH hR
  exact ⟨g.piIso hE, g.row_pi hE⟩

theorem perm_unique (hE : E * E = E) {R : BRel Q} {π σ : Cls E hE → Cls E hE}
    (hπ : ∀ q (hq : E q q), R q = beta hE (π (cls hE q hq)))
    (hσ : ∀ q (hq : E q q), R q = beta hE (σ (cls hE q hq))) : π = σ := by
  funext i
  obtain ⟨q, hq, rfl⟩ := cls_surj hE i
  exact beta_injective hE ((hπ q hq).symm.trans (hσ q hq))

end Perm

/-! ## 5. Lemma 6.2 (iv): under strong connectivity the order of the classes is trivial -/

section Antichain

variable {Q : Type*} {E : BRel Q}

/-- **The core of Lemma 6.2 (iv)**: if elements of `M` join any two points (`∀ x y, ∃ U ∈ M, U x y`)
and `E X E ∈ 𝒢_E` for `X ∈ M`, then no two classes are comparable
(if `Q_a ≤ Q_b`, take `U` from `Q_b` to `Q_a`; then `R := E U E` has `R_{q_b q_a} = R_{q_b q_b} = 1`,
and `R^m = E` gives `E_{q_b q_a} = 1`). -/
theorem antichain [Finite Q] (hE : E * E = E) {M : Submonoid (BRel Q)}
    (hgrp : ∀ X ∈ M, InH E (E * X * E)) (hconn : ∀ x y, ∃ U ∈ M, U x y) :
    ∀ i j : Cls E hE, i ≤ j → i = j := by
  rintro ⟨pa⟩ ⟨pb⟩ hab
  apply le_antisymm hab
  obtain ⟨qa, ha⟩ := pa
  obtain ⟨qb, hb⟩ := pb
  have hab' : E qa qb := hab
  show E qb qa
  obtain ⟨U, hUM, hU⟩ := hconn qb qa
  have hR := hgrp U hUM
  have hba : (E * U * E) qb qa :=
    (mul_apply _ _ _ _).2 ⟨qa, (mul_apply _ _ _ _).2 ⟨qb, hb, hU⟩, ha⟩
  have hbb : (E * U * E) qb qb := by
    rw [← hR.mul_right hE]; exact (mul_apply _ _ _ _).2 ⟨qa, hba, hab'⟩
  have hpow : ∀ n, ((E * U * E) ^ (n + 1)) qb qa := by
    intro n
    induction n with
    | zero => simpa using hba
    | succ n ih => rw [pow_succ']; exact (mul_apply _ _ _ _).2 ⟨qb, hbb, ih⟩
  obtain ⟨m, hm, hmE⟩ := hR.exists_pow_eq hE
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
  have := hpow n
  rw [Nat.zero_add] at hmE
  rwa [hmE] at this

/-- Paths in the graph of the union `B₀ ∨ B₁` of the letter types are realized by elements of the monoid generated by `B₀, B₁`. -/
theorem exists_mem_closure_of_reflTransGen {B₀ B₁ : BRel Q} {x y : Q}
    (h : Relation.ReflTransGen (fun a b => B₀ a b ∨ B₁ a b) x y) :
    ∃ U ∈ Submonoid.closure ({B₀, B₁} : Set (BRel Q)), U x y := by
  induction h with
  | refl => exact ⟨1, Submonoid.one_mem _, (one_apply x x).2 rfl⟩
  | tail _ hyz ih =>
    obtain ⟨U, hU, hxy⟩ := ih
    rcases hyz with h0 | h1
    · exact ⟨U * B₀, Submonoid.mul_mem _ hU (Submonoid.subset_closure (by simp)),
        (mul_apply _ _ _ _).2 ⟨_, hxy, h0⟩⟩
    · exact ⟨U * B₁, Submonoid.mul_mem _ hU (Submonoid.subset_closure (by simp)),
        (mul_apply _ _ _ _).2 ⟨_, hxy, h1⟩⟩

/-- **Lemma 6.2 (iv)**: if the graph of `B₀ ∨ B₁` is strongly connected, the order of the classes is trivial. -/
theorem antichain_of_strongConn [Finite Q] (hE : E * E = E) {B₀ B₁ : BRel Q}
    (hgrp : ∀ X ∈ Submonoid.closure ({B₀, B₁} : Set (BRel Q)), InH E (E * X * E))
    (hsc : ∀ x y, Relation.ReflTransGen (fun a b => B₀ a b ∨ B₁ a b) x y) :
    ∀ i j : Cls E hE, i ≤ j → i = j :=
  antichain hE hgrp (fun x y => exists_mem_closure_of_reflTransGen (hsc x y))

/-- Corollary of (iv): if the order is trivial, `E` on `C_E` is the direct sum of all-one blocks, and `β_i ∩ C_E = Q_i`. -/
theorem beta_mem_C_of_antichain (hE : E * E = E) (hanti : ∀ i j : Cls E hE, i ≤ j → i = j)
    (i : Cls E hE) (k : Q) (hk : E k k) : beta hE i k ↔ cls hE k hk = i := by
  rw [beta_mem_C hE i k hk]
  exact ⟨fun h => (hanti _ _ h).symm, fun h => h ▸ le_rfl⟩

end Antichain

/-! ## 6. Summary: Lemma 6.2 -/

section Summary

variable {Q : Type*}

/-- **Lemma 6.2 (structure of the idempotents)**. For an idempotent `E` of the minimal ideal `K` of the monoid `M` generated by
relations `B₀, B₁` on a finite `Q`:
* (iii, group) `E X E ∈ 𝒢_E` for `X ∈ M` (an element of the group with identity `E`).
* (i) Every edge of `E` factors through `C_E`.
* (ii) Rows of the same class are equal, `E_s` is the union of the `β_i` over the classes hit by `s`, and `β_i ∩ C_E` is the union of the classes `≥ i`.
* (iii) For `R = E X E ∈ 𝒢_E` there is an order automorphism `π_R` of the classes with `R_q = β_{π_R [q]}`.
* (iv) If the graph of `B₀ ∨ B₁` is strongly connected, the order of the classes is trivial and `β_i ∩ C_E = Q_i`.
The assumption that `M` does not contain zero (the empty relation) is not needed. -/
theorem lemma_56_5_1 [Finite Q] (B₀ B₁ : BRel Q) {K : Set (BRel Q)}
    (hK : IsMinIdeal (Submonoid.closure ({B₀, B₁} : Set (BRel Q))) K) {E : BRel Q}
    (hEK : E ∈ K) (hE : E * E = E) :
    (∀ X ∈ Submonoid.closure ({B₀, B₁} : Set (BRel Q)), InH E (E * X * E)) ∧
    (∀ a b, E a b → ∃ c, E c c ∧ E a c ∧ E c b) ∧
    (∀ k k' (hk : E k k) (hk' : E k' k'), cls hE k hk = cls hE k' hk' → E k = E k') ∧
    (∀ s b, E s b ↔ ∃ i, Hits hE s i ∧ beta hE i b) ∧
    (∀ i k (hk : E k k), beta hE i k ↔ i ≤ cls hE k hk) ∧
    (∀ X ∈ Submonoid.closure ({B₀, B₁} : Set (BRel Q)),
      ∃ π : Cls E hE ≃o Cls E hE, ∀ q (hq : E q q), (E * X * E) q = beta hE (π (cls hE q hq))) ∧
    ((∀ x y, Relation.ReflTransGen (fun a b => B₀ a b ∨ B₁ a b) x y) →
      (∀ i j : Cls E hE, i ≤ j → i = j) ∧
      (∀ i k (hk : E k k), beta hE i k ↔ cls hE k hk = i)) := by
  have hgrp : ∀ X ∈ Submonoid.closure ({B₀, B₁} : Set (BRel Q)), InH E (E * X * E) :=
    fun X hX => inH_of_minIdeal hK hEK hE hX
  refine ⟨hgrp, fun a b h => factor hE h, fun k k' hk hk' h => row_eq_of_cls_eq hE hk hk' h,
    row_eq_union hE, beta_mem_C hE, fun X hX => perm_of_inH hE (hgrp X hX), fun hsc => ?_⟩
  have hanti := antichain_of_strongConn hE hgrp hsc
  exact ⟨hanti, beta_mem_C_of_antichain hE hanti⟩

/-- A minimal ideal and an idempotent in it exist. -/
theorem exists_minIdeal_idem [Finite Q] (B₀ B₁ : BRel Q) :
    ∃ K, IsMinIdeal (Submonoid.closure ({B₀, B₁} : Set (BRel Q))) K ∧ ∃ E ∈ K, E * E = E := by
  obtain ⟨K, hK⟩ := exists_minIdeal (Submonoid.closure ({B₀, B₁} : Set (BRel Q)))
  exact ⟨K, hK, exists_idem_mem hK.1⟩

end Summary

/-! ## 7. Sanity check: without strong connectivity the conclusion of (iv) fails -/

section Example

/-- `≤` on `Fin 2` (there is an edge `0 → 1` but no edge `1 → 0`; the graph is not strongly connected). -/
def leRel : BRel (Fin 2) := fun a b => a ≤ b

theorem leRel_idem : leRel * leRel = leRel :=
  BRel.ext fun a b => by
    rw [mul_apply]
    exact ⟨fun ⟨_, h1, h2⟩ => le_trans h1 h2, fun h => ⟨a, le_refl a, h⟩⟩

theorem leRel_mul_mem {y : BRel (Fin 2)}
    (hy : y ∈ Submonoid.closure ({leRel, leRel} : Set (BRel (Fin 2)))) :
    leRel * y = leRel ∧ y * leRel = leRel := by
  induction hy using Submonoid.closure_induction with
  | mem x hx =>
    have hx' : x = leRel := by simpa using hx
    subst hx'; exact ⟨leRel_idem, leRel_idem⟩
  | one => exact ⟨mul_one _, one_mul _⟩
  | mul x y _ _ hx hy => exact ⟨by rw [← mul_assoc, hx.1, hy.1], by rw [mul_assoc, hy.2, hx.2]⟩

/-- The minimal ideal of the monoid of `B₀ = B₁ = ≤` is `{≤}`. -/
theorem leRel_minIdeal :
    IsMinIdeal (Submonoid.closure ({leRel, leRel} : Set (BRel (Fin 2)))) {leRel} := by
  have hmem : leRel ∈ Submonoid.closure ({leRel, leRel} : Set (BRel (Fin 2))) :=
    Submonoid.subset_closure (by simp)
  refine ⟨⟨⟨leRel, rfl⟩, by simp, ?_⟩, ?_⟩
  · rintro x hx y rfl
    exact ⟨(leRel_mul_mem hx).2, (leRel_mul_mem hx).1⟩
  · rintro I ⟨⟨y, hy⟩, hIM, hIc⟩ z rfl
    have := (hIc leRel hmem y hy).1
    rwa [(leRel_mul_mem (hIM hy)).1] at this

/-- In this example the order of the classes of the idempotent `≤` of the minimal ideal is not trivial (`[0] < [1]`). -/
theorem leRel_not_antichain :
    ∃ i j : Cls leRel leRel_idem, i ≤ j ∧ i ≠ j :=
  ⟨cls leRel_idem 0 (le_refl _), cls leRel_idem 1 (le_refl _),
    (cls_le_cls leRel_idem _ _).2 (show (0 : Fin 2) ≤ 1 by decide),
    fun h => absurd ((cls_eq_cls leRel_idem _ _).1 h).2 (show ¬ ((1 : Fin 2) ≤ 0) by decide)⟩

end Example

end Collatz.Arctic.MinIdeal

#print axioms Collatz.Arctic.MinIdeal.lemma_56_5_1
#print axioms Collatz.Arctic.MinIdeal.exists_minIdeal_idem
#print axioms Collatz.Arctic.MinIdeal.leRel_not_antichain

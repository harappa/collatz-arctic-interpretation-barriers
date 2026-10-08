/-
# Natural-number matrix interpretations ($\mathcal T$): adding an isolated index changes neither (H2^prod) nor the monotonicity of the lift (internal review)

`addLoop` of `AutoCore.lean` (an isolated index `none`: only a self-loop of weight 1, with entries 0 in `u` and `v`) makes (G2) free
(`autoValueCore_iff_noG2`; Theorem 10.11). Here we show that the two premises of the core statement `W3CoreStmt` (Theorem 10.10) are not changed by `addLoop` either.

* `h2Prod_addLoop_iff`: `H2Prod (addLoop A) ↔ H2Prod A`.
* `autoMono3_liftT_addLoop_iff`: `AutoMono3 (liftT (addLoop A)) ↔ AutoMono3 (liftT A)` (the values agree on all words,
  `aval_liftT_addLoop`).
* Together: `w3Premises_addLoop_iff`.

**Route**: a general lemma on embeddings (§1, `AutoEmb`). If a map `e : P → P'` preserves the products of words, `u` and `v`, the paths from the image of `e` to the outside
of the image have weight 0, and `u` vanishes outside the image, then relevant indices, strongly connected components, internal edges and 0/1 all correspond under `e`, and
that all components are 0/1 is equivalent on both sides (`AutoEmb.comp_zeroOne_iff`). In `liftT (addLoop A)` the indices `(none, r)` have `u` equal to 0 and cannot be
reached from `(some i, r)`, so they are not relevant. §2 shows that `(i, r) ↦ (some i, r)` satisfies these conditions (`addLoop_emb`).

Not used in the proof of `allBarriers_final`. Outside the closure of the main theorems.
-/
import CollatzProof.Arctic.Nat.AutoCore

namespace Collatz.Arctic.NatQ5.W4a

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix

set_option linter.unusedSectionVars false

/-! ## §1 The general form of embeddings -/

section Emb

variable {P P' : Type*} [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']

/-- **Embeddings of automata**: `e : P → P'` preserves the products of words, `u` and `v`; the paths from the image of `e` to the outside of the image have weight 0, and `u` vanishes outside the image. -/
structure AutoEmb (L : ValAuto P) (L' : ValAuto P') (e : P → P') : Prop where
  dxn : ∀ w x y, Rigid.DxN L'.B w (e x) (e y) = Rigid.DxN L.B w x y
  out : ∀ w x z, (∀ y, e y ≠ z) → Rigid.DxN L'.B w (e x) z = 0
  u : ∀ x, L'.u (e x) = L.u x
  u0 : ∀ z, (∀ y, e y ≠ z) → L'.u z = 0
  v : ∀ x, L'.v (e x) = L.v x

namespace AutoEmb

variable {L : ValAuto P} {L' : ValAuto P'} {e : P → P'}

theorem conn_iff (h : AutoEmb L L' e) (x y : P) : Conn L' (e x) (e y) ↔ Conn L x y := by
  constructor
  · rintro ⟨w, hw⟩; exact ⟨w, by rwa [h.dxn] at hw⟩
  · rintro ⟨w, hw⟩; exact ⟨w, by rwa [h.dxn]⟩

/-- Indices reachable from the image lie in the image. -/
theorem mem_range_of_conn (h : AutoEmb L L' e) {x : P} {z : P'} (hc : Conn L' (e x) z) : ∃ y, e y = z := by
  by_contra hn
  push Not at hn
  obtain ⟨w, hw⟩ := hc
  rw [h.out w x z hn] at hw
  omega

/-- Indices with positive `u` lie in the image. -/
theorem mem_range_of_u (h : AutoEmb L L' e) {i : P'} (hi : 1 ≤ L'.u i) : ∃ y, e y = i := by
  by_contra hn
  push Not at hn
  rw [h.u0 i hn] at hi
  omega

theorem reach_iff (h : AutoEmb L L' e) (x : P) : Reach L' (e x) ↔ Reach L x := by
  constructor
  · rintro ⟨i, hi, hc⟩
    obtain ⟨y, rfl⟩ := h.mem_range_of_u hi
    exact ⟨y, by rwa [h.u] at hi, (h.conn_iff y x).1 hc⟩
  · rintro ⟨i, hi, hc⟩
    exact ⟨e i, by rwa [h.u], (h.conn_iff i x).2 hc⟩

theorem coReach_iff (h : AutoEmb L L' e) (x : P) : CoReach L' (e x) ↔ CoReach L x := by
  constructor
  · rintro ⟨j, hc, hj⟩
    obtain ⟨y, rfl⟩ := h.mem_range_of_conn hc
    exact ⟨y, (h.conn_iff x y).1 hc, by rwa [h.v] at hj⟩
  · rintro ⟨j, hc, hj⟩
    exact ⟨e j, (h.conn_iff x j).2 hc, by rwa [h.v]⟩

theorem rel_iff (h : AutoEmb L L' e) (x : P) : Rel L' (e x) ↔ Rel L x :=
  and_congr (h.reach_iff x) (h.coReach_iff x)

/-- Relevant indices lie in the image. -/
theorem mem_range_of_rel (h : AutoEmb L L' e) {z : P'} (hz : Rel L' z) : ∃ x, e x = z := by
  obtain ⟨⟨i, hi, hc⟩, -⟩ := hz
  obtain ⟨y, rfl⟩ := h.mem_range_of_u hi
  exact h.mem_range_of_conn hc

/-- Strongly connected components correspond under the image. -/
theorem mem_sccOf_iff (h : AutoEmb L L' e) (q : P) (z : P') :
    z ∈ sccOf L' (e q) ↔ ∃ x ∈ sccOf L q, e x = z := by
  rw [mem_sccOf]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨x, rfl⟩ := h.mem_range_of_conn h1
    exact ⟨x, (mem_sccOf L).2 ⟨(h.conn_iff q x).1 h1, (h.conn_iff x q).1 h2⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [mem_sccOf] at hx
    exact ⟨(h.conn_iff q x).2 hx.1, (h.conn_iff x q).2 hx.2⟩

theorem B_apply (h : AutoEmb L L' e) (b : Fin 2) (x y : P) : L'.B b (e x) (e y) = L.B b x y := by
  have := h.dxn [b] x y
  simpa [DxN_cons'] using this

theorem hasEdge_iff (h : AutoEmb L L' e) (q : P) : HasEdge L' (sccOf L' (e q)) ↔ HasEdge L (sccOf L q) := by
  constructor
  · rintro ⟨x', hx', y', hy', b, hb⟩
    obtain ⟨x, hx, rfl⟩ := (h.mem_sccOf_iff q x').1 hx'
    obtain ⟨y, hy, rfl⟩ := (h.mem_sccOf_iff q y').1 hy'
    exact ⟨x, hx, y, hy, b, by rwa [h.B_apply] at hb⟩
  · rintro ⟨x, hx, y, hy, b, hb⟩
    exact ⟨e x, (h.mem_sccOf_iff q _).2 ⟨x, hx, rfl⟩, e y, (h.mem_sccOf_iff q _).2 ⟨y, hy, rfl⟩, b,
      by rwa [h.B_apply]⟩

theorem zeroOne_iff (h : AutoEmb L L' e) (q : P) : ZeroOne L' (sccOf L' (e q)) ↔ ZeroOne L (sccOf L q) := by
  constructor
  · intro hz w x y
    have := hz w ⟨e x.1, (h.mem_sccOf_iff q _).2 ⟨x.1, x.2, rfl⟩⟩ ⟨e y.1, (h.mem_sccOf_iff q _).2 ⟨y.1, y.2, rfl⟩⟩
    rw [DC_apply, h.dxn] at this
    rwa [DC_apply]
  · intro hz w x' y'
    obtain ⟨x, hx, hxe⟩ := (h.mem_sccOf_iff q x'.1).1 x'.2
    obtain ⟨y, hy, hye⟩ := (h.mem_sccOf_iff q y'.1).1 y'.2
    have := hz w ⟨x, hx⟩ ⟨y, hy⟩
    rw [DC_apply] at this
    rw [DC_apply, ← hxe, ← hye, h.dxn]
    exact this

/-- **That all components are 0/1 is equivalent on both sides of an embedding**. -/
theorem comp_zeroOne_iff (h : AutoEmb L L' e) :
    (∀ C, IsComp L' C → ZeroOne L' C) ↔ (∀ C, IsComp L C → ZeroOne L C) := by
  constructor
  · rintro hz C ⟨⟨q, hq, rfl⟩, hE⟩
    exact (h.zeroOne_iff q).1 (hz _ ⟨⟨e q, (h.rel_iff q).2 hq, rfl⟩, (h.hasEdge_iff q).2 hE⟩)
  · rintro hz C ⟨⟨q', hq', rfl⟩, hE⟩
    obtain ⟨q, rfl⟩ := h.mem_range_of_rel hq'
    exact (h.zeroOne_iff q).2 (hz _ ⟨⟨q, (h.rel_iff q).1 hq', rfl⟩, (h.hasEdge_iff q).1 hE⟩)

end AutoEmb

end Emb

/-! ## §2 The lift of `addLoop` -/

section AddLoop

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The embedding `(i, r) ↦ (some i, r)`. -/
def someE : Q × ZMod 3 → Option Q × ZMod 3 := fun p => (some p.1, p.2)

/-- In `addLoop A` the paths from an index `some i` to `none` have weight 0. -/
theorem DxN_addLoop_sn (A : ValAuto Q) (w : List (Fin 2)) (i : Q) :
    Rigid.DxN (addLoop A).B w (some i) none = 0 := by
  induction w generalizing i with
  | nil => simp
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_option]
    simp only [addLoop_B_sn, zero_mul, zero_add, ih, mul_zero, Finset.sum_const_zero]

/-- `liftT A` embeds into `liftT (addLoop A)` by `someE`. -/
theorem addLoop_emb (A : ValAuto Q) : AutoEmb (liftT A) (liftT (addLoop A)) someE where
  dxn w x y := by
    obtain ⟨i, r⟩ := x
    obtain ⟨j, r'⟩ := y
    show Rigid.DxN (liftB (addLoop A) 3) w (some i, r) (some j, r') = Rigid.DxN (liftB A 3) w (i, r) (j, r')
    rw [DxN_lift, DxN_lift, DxN_addLoop]
  out w x z hz := by
    obtain ⟨i, r⟩ := x
    obtain ⟨k, r'⟩ := z
    cases k with
    | none =>
      show Rigid.DxN (liftB (addLoop A) 3) w (some i, r) (none, r') = 0
      rw [DxN_lift, DxN_addLoop_sn, zero_mul]
    | some j => exact absurd rfl (hz (j, r'))
  u _ := rfl
  u0 z hz := by
    obtain ⟨k, r⟩ := z
    cases k with
    | none => show (addLoop A).u none * _ = 0; simp
    | some j => exact absurd rfl (hz (j, r))
  v _ := rfl

/-- **`H2Prod (addLoop A) ↔ H2Prod A`** (internal review). -/
theorem h2Prod_addLoop_iff (A : ValAuto Q) : H2Prod (addLoop A) ↔ H2Prod A :=
  (addLoop_emb A).comp_zeroOne_iff

/-- The values of the lift are not changed by `addLoop` (on all words). -/
theorem aval_liftT_addLoop (A : ValAuto Q) (ω : List (Fin 2)) :
    aval (liftT (addLoop A)) ω = aval (liftT A) ω := by
  unfold liftT
  rw [aval_lift, aval_lift, aval_addLoop]

/-- **`AutoMono3 (liftT (addLoop A)) ↔ AutoMono3 (liftT A)`** (internal review). -/
theorem autoMono3_liftT_addLoop_iff (A : ValAuto Q) : AutoMono3 (liftT (addLoop A)) ↔ AutoMono3 (liftT A) := by
  unfold AutoMono3
  simp only [aval_liftT_addLoop]

/-- The two premises of the core statement `W3CoreStmt` are not changed by `addLoop`. -/
theorem w3Premises_addLoop_iff (A : ValAuto Q) :
    (H2Prod (addLoop A) ∧ AutoMono3 (liftT (addLoop A))) ↔ (H2Prod A ∧ AutoMono3 (liftT A)) :=
  and_congr (h2Prod_addLoop_iff A) (autoMono3_liftT_addLoop_iff A)

end AddLoop

end Collatz.Arctic.NatQ5.W4a

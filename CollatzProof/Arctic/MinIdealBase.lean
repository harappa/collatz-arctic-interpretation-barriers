/-
Formalization of Lemma 6.2 (structure of the idempotents of the minimal ideal) in Lean. This file contains §1 and §2 (§3–§7 are in `MinIdeal.lean`).
It depends only on `import Mathlib`.

Setting: a finite set of indices `Q`, Boolean matrices (relations) `B₀, B₁` (`N̄₀, N̄₁` in the paper), the monoid `M` they generate (containing the identity),
the minimal ideal `K` of `M`, an idempotent `E` of `K`.

* §1 (general monoids): ideals `IsIdeal` of a submonoid, minimal ideals `IsMinIdeal`, elements `InH` of the maximal subgroup `𝒢_e` (`𝒢_E` in the paper).
  In the finite case a minimal ideal exists (`exists_minIdeal`) and contains idempotents (`exists_idem_mem`), and
  if `e ∈ K` is idempotent, then `e X e` (`X ∈ M`) is an element of the group with identity `e` (`inH_of_minIdeal`).
  Powers of a group element return to `e` (`InH.exists_pow_eq`).
* §2 (relations): `BRel Q := Q → Q → Prop`, product = composition, identity = equality.
* §3 (Lemma 6.2 (i)(ii)): `factor` (factorization through `C_E`), the classes `Cls E hE` (equivalence classes of the preorder on `C_E`, partially ordered),
  the rows `beta`, `row_eq_union`, `beta_mem_C`.
* §4 (Lemma 6.2 (iii)): for an element `R` of `𝒢_E` there is an order automorphism `piIso` of the classes with
  `R q = β (π [q])` (`perm_of_inH`).
* §5 (Lemma 6.2 (iv)): if the graph of `B₀ ∨ B₁` is strongly connected, the order of the classes is trivial (`antichain_of_strongConn`).
* §6: summary `lemma_56_5_1` (and the existence `exists_minIdeal_idem`).
* §7: sanity check. For `B₀ = B₁ = ≤` (`Fin 2`, not strongly connected) the minimal ideal is `{≤}` and the order of the classes is not trivial
  (`leRel_not_antichain`). This confirms that the strong connectivity hypothesis of (iv) is needed and that the definition of the order of the classes is not vacuous.

Remarks on the proof:
* The assumption that `M` does not contain zero (the empty relation) is needed in none of (i)–(iv) (if it does, `E = 0`, there are no classes,
  and the statements hold vacuously). It is used only to show that classes exist (`nonempty_cls`).
* The proof of (iii) uses a short argument, not one via antichains of minimal classes: from `E q q = (R R')_{qq}`
  take `k` with `R q k ∧ R' k q`; then `E k k` from `R' R = E`, and `R q = E k` (`row_of_wit`).
  Finiteness is not needed for (iii).
-/
import Mathlib


namespace Collatz.Arctic.MinIdeal

/-! ## 1. Minimal ideals of finite monoids (general monoids) -/

section General

variable {A : Type*} [Monoid A]

/-- A two-sided ideal of the submonoid `M`: a nonempty subset of `M` closed under multiplication by elements of `M` on both sides. -/
def IsIdeal (M : Submonoid A) (I : Set A) : Prop :=
  I.Nonempty ∧ I ⊆ M ∧ ∀ x ∈ M, ∀ y ∈ I, x * y ∈ I ∧ y * x ∈ I

/-- Minimal ideal: an ideal contained in every ideal. -/
def IsMinIdeal (M : Submonoid A) (K : Set A) : Prop :=
  IsIdeal M K ∧ ∀ I, IsIdeal M I → K ⊆ I

/-- An element of `𝒢_e`: `e r e = r`, and there is `r'` with `e r' e = r'`, `r r' = e = r' r`
(an element of the group with identity `e`). -/
def InH (e r : A) : Prop :=
  e * r * e = r ∧ ∃ r', e * r' * e = r' ∧ r * r' = e ∧ r' * r = e

theorem isIdeal_top (M : Submonoid A) : IsIdeal M (M : Set A) :=
  ⟨⟨1, M.one_mem⟩, le_rfl, fun _ hx _ hy => ⟨M.mul_mem hx hy, M.mul_mem hy hx⟩⟩

theorem IsIdeal.inter {M : Submonoid A} {I J : Set A} (hI : IsIdeal M I) (hJ : IsIdeal M J) :
    IsIdeal M (I ∩ J) := by
  obtain ⟨⟨i, hi⟩, hIM, hIc⟩ := hI
  obtain ⟨⟨j, hj⟩, hJM, hJc⟩ := hJ
  refine ⟨⟨i * j, (hIc j (hJM hj) i hi).2, (hJc i (hIM hi) j hj).1⟩, fun x hx => hIM hx.1, ?_⟩
  intro x hx y hy
  exact ⟨⟨(hIc x hx y hy.1).1, (hJc x hx y hy.2).1⟩, ⟨(hIc x hx y hy.1).2, (hJc x hx y hy.2).2⟩⟩

/-- A submonoid of a finite monoid has a minimal ideal (an ideal minimal for inclusion is contained in every ideal, since its
intersection with any ideal is an ideal). -/
theorem exists_minIdeal [Finite A] (M : Submonoid A) : ∃ K, IsMinIdeal M K := by
  obtain ⟨K, hK, hmin⟩ :=
    (wellFounded_lt (α := Set A)).has_min {I | IsIdeal M I} ⟨_, isIdeal_top M⟩
  refine ⟨K, hK, fun J hJ => ?_⟩
  by_contra hKJ
  exact hmin _ (hK.inter hJ) (lt_of_le_of_ne Set.inter_subset_left
    (fun h => hKJ (h.symm.subset.trans Set.inter_subset_right)))

theorem IsIdeal.pow_mem {M : Submonoid A} {I : Set A} (hI : IsIdeal M I) {x : A} (hx : x ∈ I) :
    ∀ n, x ^ (n + 1) ∈ I
  | 0 => by simpa using hx
  | n + 1 => by rw [pow_succ]; exact (hI.2.2 x (hI.2.1 hx) _ (hI.pow_mem hx n)).2

/-- An element of a finite monoid has an idempotent positive power. -/
theorem exists_idem_pow [Finite A] (x : A) : ∃ n, 0 < n ∧ x ^ n * x ^ n = x ^ n := by
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ (n + 1))
  have h' : x ^ (a + 1) = x ^ (b + 1) := h
  -- `p, k` with `x^(p+1) x^(k+1) = x^(p+1)`
  have key : ∃ p k, x ^ (p + 1) * x ^ (k + 1) = x ^ (p + 1) := by
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      exact ⟨a, k, by rw [← pow_add, show a + 1 + (k + 1) = a + k + 1 + 1 by omega, ← h']⟩
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      exact ⟨b, k, by rw [← pow_add, show b + 1 + (k + 1) = b + k + 1 + 1 by omega, h']⟩
  obtain ⟨p, k, hpk⟩ := key
  have hpow : ∀ t, x ^ (p + 1) * x ^ ((k + 1) * t) = x ^ (p + 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, pow_add x ((k + 1) * t) (k + 1), ← mul_assoc, ih, hpk]
  refine ⟨(k + 1) * (p + 1), by positivity, ?_⟩
  have e : (k + 1) * (p + 1) = k * (p + 1) + (p + 1) := by ring
  calc x ^ ((k + 1) * (p + 1)) * x ^ ((k + 1) * (p + 1))
      = x ^ (k * (p + 1)) * (x ^ (p + 1) * x ^ ((k + 1) * (p + 1))) := by
        nth_rewrite 1 [e]
        rw [pow_add, mul_assoc]
    _ = x ^ ((k + 1) * (p + 1)) := by rw [hpow, ← pow_add, ← e]

/-- An ideal of a finite monoid contains an idempotent. -/
theorem exists_idem_mem [Finite A] {M : Submonoid A} {I : Set A} (hI : IsIdeal M I) :
    ∃ e ∈ I, e * e = e := by
  obtain ⟨x, hx⟩ := hI.1
  obtain ⟨n, hn, hidem⟩ := exists_idem_pow x
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  exact ⟨x ^ (0 + m + 1), by simpa using hI.pow_mem hx m, hidem⟩

/-- In a finite monoid, a one-sided inverse inside the part with identity `e` is a two-sided inverse
(`z ↦ y z` is injective on `{z | e z = z}`, hence surjective). -/
theorem mul_eq_comm_of_finite [Finite A] {e x y : A} (he : e * e = e) (hx : x * e = x)
    (hy : e * y = y) (h : x * y = e) : y * x = e := by
  let f : {z : A // e * z = z} → {z : A // e * z = z} :=
    fun z => ⟨y * z.1, by rw [← mul_assoc, hy]⟩
  have hinj : Function.Injective f := by
    intro z₁ z₂ hz
    have h12 : y * z₁.1 = y * z₂.1 := congrArg Subtype.val hz
    apply Subtype.ext
    have h3 : x * (y * z₁.1) = x * (y * z₂.1) := by rw [h12]
    rw [← mul_assoc, ← mul_assoc, h, z₁.2, z₂.2] at h3
    exact h3
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨e, he⟩
  have hw' : y * w.1 = e := congrArg Subtype.val hw
  have hxw : x = w.1 := by
    calc x = x * e := hx.symm
      _ = x * (y * w.1) := by rw [hw']
      _ = e * w.1 := by rw [← mul_assoc, h]
      _ = w.1 := w.2
  rw [hxw, hw']

/-- For an idempotent `e` of the minimal ideal and `X ∈ M`, `e X e ∈ 𝒢_e`
(`e ∈ K = M (e X e) M` gives `e = a (e X e) b`; in the part with identity `e` one-sided inverses are two-sided). -/
theorem inH_of_minIdeal [Finite A] {M : Submonoid A} {K : Set A} (hK : IsMinIdeal M K) {e : A}
    (heK : e ∈ K) (he : e * e = e) {x : A} (hx : x ∈ M) : InH e (e * x * e) := by
  obtain ⟨⟨_, hKM, hKc⟩, hmin⟩ := hK
  have he' : ∀ z, e * (e * z) = e * z := fun z => by rw [← mul_assoc, he]
  have heM : e ∈ M := hKM heK
  have hrK : e * x * e ∈ K := (hKc e heM _ (hKc x hx e heK).2).2
  have hrM : e * x * e ∈ M := hKM hrK
  -- `I := M (e x e) M` is an ideal
  let I : Set A := {z | ∃ a ∈ M, ∃ b ∈ M, z = a * (e * x * e) * b}
  have hI : IsIdeal M I := by
    refine ⟨⟨e * x * e, 1, M.one_mem, 1, M.one_mem, by simp⟩, ?_, ?_⟩
    · rintro z ⟨a, ha, b, hb, rfl⟩
      exact M.mul_mem (M.mul_mem ha hrM) hb
    · rintro c hc z ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨c * a, M.mul_mem hc ha, b, hb, by simp [mul_assoc]⟩,
        ⟨a, ha, b * c, M.mul_mem hb hc, by simp [mul_assoc]⟩⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hmin I hI heK
  -- `α (e x e) β = e` with `α := e a e`, `β := e b e`
  have h1 : (e * a * e) * ((e * x * e) * (e * b * e)) = e := by
    calc (e * a * e) * ((e * x * e) * (e * b * e)) = e * (a * (e * x * e) * b) * e := by
          simp only [mul_assoc, he']
      _ = e := by rw [← hab, he, he]
  have h2 : ((e * a * e) * (e * x * e)) * (e * b * e) = e := by simpa only [mul_assoc] using h1
  have h3 := mul_eq_comm_of_finite he (by simp only [mul_assoc, he]) (by simp only [mul_assoc, he']) h1
  have h4 := mul_eq_comm_of_finite he (by simp only [mul_assoc, he]) (by simp only [mul_assoc, he']) h2
  refine ⟨by simp only [mul_assoc, he, he'], e * (b * e * a) * e, by simp only [mul_assoc, he, he'],
    ?_, ?_⟩
  · calc e * x * e * (e * (b * e * a) * e) = (e * x * e) * (e * b * e) * (e * a * e) := by
          simp only [mul_assoc, he']
      _ = e := h3
  · calc e * (b * e * a) * e * (e * x * e) = (e * b * e) * ((e * a * e) * (e * x * e)) := by
          simp only [mul_assoc, he']
      _ = e := h4

theorem InH.mul_left {e r : A} (he : e * e = e) (hr : InH e r) : e * r = r := by
  calc e * r = e * (e * r * e) := by rw [hr.1]
    _ = e * r * e := by rw [← mul_assoc, ← mul_assoc, he]
    _ = r := hr.1

theorem InH.mul_right {e r : A} (he : e * e = e) (hr : InH e r) : r * e = r := by
  calc r * e = e * r * e * e := by rw [hr.1]
    _ = e * r * (e * e) := by rw [mul_assoc]
    _ = r := by rw [he, hr.1]

/-- A positive power of an element of `𝒢_e` returns to `e` (finite monoid). -/
theorem InH.exists_pow_eq [Finite A] {e r : A} (he : e * e = e) (hr : InH e r) :
    ∃ m, 0 < m ∧ r ^ m = e := by
  have her : e * r = r := hr.mul_left he
  obtain ⟨_, r', _, _, hr'r⟩ := hr
  have herpow : ∀ n, e * r ^ (n + 1) = r ^ (n + 1) := by
    intro n; rw [pow_succ', ← mul_assoc, her]
  -- `r'^(n+1) r^(n+1) = e`
  have hinv : ∀ n, r' ^ (n + 1) * r ^ (n + 1) = e := by
    intro n
    induction n with
    | zero => simpa using hr'r
    | succ n ih =>
      calc r' ^ (n + 1 + 1) * r ^ (n + 1 + 1) = r' ^ (n + 1) * (r' * r) * r ^ (n + 1) := by
            rw [pow_succ r' (n + 1), pow_succ' r (n + 1)]; simp only [mul_assoc]
        _ = e := by rw [hr'r, mul_assoc, herpow, ih]
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => r ^ (n + 1))
  have h' : r ^ (a + 1) = r ^ (b + 1) := h
  have key : ∀ a k, r ^ (a + 1) = r ^ (a + k + 1 + 1) → r ^ (k + 1) = e := by
    intro a k hak
    calc r ^ (k + 1) = e * r ^ (k + 1) := (herpow k).symm
      _ = r' ^ (a + 1) * r ^ (a + 1) * r ^ (k + 1) := by rw [hinv]
      _ = r' ^ (a + 1) * r ^ (a + k + 1 + 1) := by
        rw [mul_assoc, ← pow_add, show a + 1 + (k + 1) = a + k + 1 + 1 by omega]
      _ = e := by rw [← hak, hinv]
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact ⟨k + 1, by omega, key a k h'⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact ⟨k + 1, by omega, key b k h'.symm⟩

end General

/-! ## 2. The monoid of relations (Boolean matrices) -/

/-- Relations on `Q` (Boolean matrices `Q × Q`). Product = composition, identity = equality. -/
def BRel (Q : Type*) := Q → Q → Prop

namespace BRel

variable {Q : Type*}

instance : Mul (BRel Q) := ⟨fun R S a b => ∃ c, R a c ∧ S c b⟩
instance : One (BRel Q) := ⟨fun a b => a = b⟩

theorem mul_apply (R S : BRel Q) (a b : Q) : (R * S) a b ↔ ∃ c, R a c ∧ S c b := Iff.rfl

theorem one_apply (a b : Q) : (1 : BRel Q) a b ↔ a = b := Iff.rfl

theorem ext {R S : BRel Q} (h : ∀ a b, R a b ↔ S a b) : R = S :=
  funext fun a => funext fun b => propext (h a b)

instance : Monoid (BRel Q) where
  mul_assoc R S T := ext fun a b => by
    simp only [mul_apply]
    constructor
    · rintro ⟨c, ⟨d, h1, h2⟩, h3⟩; exact ⟨d, h1, c, h2, h3⟩
    · rintro ⟨d, h1, c, h2, h3⟩; exact ⟨c, ⟨d, h1, h2⟩, h3⟩
  one_mul R := ext fun a b => by
    simp only [mul_apply, one_apply]
    constructor
    · rintro ⟨c, rfl, h⟩; exact h
    · intro h; exact ⟨a, rfl, h⟩
  mul_one R := ext fun a b => by
    simp only [mul_apply, one_apply]
    constructor
    · rintro ⟨c, h, rfl⟩; exact h
    · intro h; exact ⟨b, h, rfl⟩

instance [Finite Q] : Finite (BRel Q) := inferInstanceAs (Finite (Q → Q → Prop))

end BRel

end Collatz.Arctic.MinIdeal

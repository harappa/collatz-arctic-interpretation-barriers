/-
Algebraic parts of the arctic barrier in dependency pair form (Theorems 3.3 and 3.4 of the paper).

* `ArcticOrder`: the order properties shared by `Arc` (ℕ ∪ {−∞}) and `ArcZ` (ℤ ∪ {−∞}) (addition is max, multiplication is + and monotone).
  The estimates below are written for a general semiring `R` and used for both.
* `evR`: the interpretation of a string (the product of matrices; for `Arc` it agrees with `Defs.ev` by definition). The transpose of the interpretation of the reversed string
  (`evR_reverse_transpose`, used to rewrite values of the reversed system in the form reading from the top; Lemma 5.2).
* Homogeneous coordinates `hom f = [[M, c], [−∞, 0]]` (the `M̂_s` of Lemma 5.2): the composition of linear functions is the product
  (`hom_comp`), and the interpretation of a string is a product (`hom_evA`). The coefficientwise comparison `WeakA` and the first-row comparisons `WeakTop`, `StrictTop`
  become comparisons of entries in homogeneous coordinates.
* Lemmas on values in `Arc` (finiteness; `l ≫ r` implies `r ⊗ 1 ≤ l`).
-/
import CollatzProof.Arctic.Bridge
import CollatzProof.Arctic.DPStatement

namespace Collatz.Arctic

open Matrix

/-- Order properties of arctic semirings (addition is max, multiplication is +); the part shared by `Arc` and `ArcZ`. -/
class ArcticOrder (R : Type) [CommSemiring R] [LinearOrder R] : Prop where
  mul_mono : ∀ {a b c e : R}, a ≤ b → c ≤ e → a * c ≤ b * e
  add_mono : ∀ {a b c e : R}, a ≤ b → c ≤ e → a + c ≤ b + e
  le_add : ∀ a b : R, a ≤ a + b

instance : ArcticOrder Arc where
  mul_mono h1 h2 := Arc.mul_le_mul_of_le h1 h2
  add_mono h1 h2 := by
    rw [Arc.le_iff_val] at *
    simp only [Arc.val_add]
    exact max_le_max h1 h2
  le_add a b := by rw [Arc.le_iff_val]; simp

instance : ArcticOrder ArcZ where
  mul_mono h1 h2 := by
    rw [ArcZ.le_iff_val] at *
    simp only [ArcZ.val_mul]
    exact add_le_add h1 h2
  add_mono h1 h2 := by
    rw [ArcZ.le_iff_val] at *
    simp only [ArcZ.val_add]
    exact max_le_max h1 h2
  le_add a b := by rw [ArcZ.le_iff_val]; simp

section Order

variable {R : Type} [CommSemiring R] [LinearOrder R] [ArcticOrder R]

/-- Comparison of sums from termwise comparison (addition is max). -/
lemma ao_sum_mono {ι : Type*} (s : Finset ι) {f g : ι → R} (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ArcticOrder.add_mono (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A term is at most the sum (addition is max). -/
lemma ao_le_sum {ι : Type*} {s : Finset ι} (f : ι → R) {i : ι} (hi : i ∈ s) :
    f i ≤ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hi
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ArcticOrder.le_add _ _
    · exact (ih hi).trans (by rw [add_comm]; exact ArcticOrder.le_add _ _)

/-- The matrix product is monotone in the entrywise order. -/
lemma ao_mul_mono {D : ℕ} {A A' B B' : Matrix (Fin D) (Fin D) R}
    (hA : ∀ i j, A i j ≤ A' i j) (hB : ∀ i j, B i j ≤ B' i j) :
    ∀ i j, (A * B) i j ≤ (A' * B') i j := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ao_sum_mono _ (fun k _ => ArcticOrder.mul_mono (hA i k) (hB k j))

/-- The matrix-vector product is monotone in the entrywise order. -/
lemma ao_mulVec_mono {D : ℕ} {A A' : Matrix (Fin D) (Fin D) R} {v v' : Fin D → R}
    (hA : ∀ i j, A i j ≤ A' i j) (hv : ∀ i, v i ≤ v' i) : ∀ i, (A *ᵥ v) i ≤ (A' *ᵥ v') i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact ao_sum_mono _ (fun k _ => ArcticOrder.mul_mono (hA i k) (hv k))

end Order

section Alg

variable {R : Type} [CommSemiring R]

/-- The interpretation of a string (the product of matrices). For `Arc` it agrees with `Defs.ev` by definition. -/
def evR {D : ℕ} (A : Letter → Matrix (Fin D) (Fin D) R) (w : Word) : Matrix (Fin D) (Fin D) R :=
  (w.map A).prod

lemma evR_append {D : ℕ} (A : Letter → Matrix (Fin D) (Fin D) R) (u v : Word) :
    evR A (u ++ v) = evR A u * evR A v := by
  simp [evR, List.map_append, List.prod_append]

lemma evR_cons {D : ℕ} (A : Letter → Matrix (Fin D) (Fin D) R) (s : Letter) (w : Word) :
    evR A (s :: w) = A s * evR A w := by
  simp [evR]

lemma evR_nil {D : ℕ} (A : Letter → Matrix (Fin D) (Fin D) R) : evR A [] = 1 := by
  simp [evR]

/-- The transpose of the interpretation of the reversed string is the interpretation by the transposes (the form reading from the top). -/
lemma evR_reverse_transpose {D : ℕ} (A : Letter → Matrix (Fin D) (Fin D) R) (w : Word) :
    (evR A w.reverse)ᵀ = evR (fun s => (A s)ᵀ) w := by
  simp [evR, Matrix.transpose_list_prod, List.map_reverse, Function.comp_def]

/-- Homogeneous coordinates `ĥ(f) = [[M, c], [−∞, 0]]` (dimension `d + 1`; the last index is the homogeneous coordinate). -/
def hom {d : ℕ} (f : AffFun R d) : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => R) (Fin.lastCases (motive := fun _ => R) 1 (fun _ => 0) j)
      (fun i' => Fin.lastCases (motive := fun _ => R) (f.c i') (fun j' => f.M i' j') j) i

section Hom
variable {d : ℕ}

@[simp] lemma hom_cc (f : AffFun R d) (i j : Fin d) : hom f i.castSucc j.castSucc = f.M i j := by
  simp [hom]
@[simp] lemma hom_cl (f : AffFun R d) (i : Fin d) : hom f i.castSucc (Fin.last d) = f.c i := by
  simp [hom]
@[simp] lemma hom_lc (f : AffFun R d) (j : Fin d) : hom f (Fin.last d) j.castSucc = 0 := by
  simp [hom]
@[simp] lemma hom_ll (f : AffFun R d) : hom f (Fin.last d) (Fin.last d) = 1 := by
  simp [hom]

/-- The composition of linear functions is the product of their matrices in homogeneous coordinates. -/
lemma hom_comp (f g : AffFun R d) : hom (f.comp g) = hom f * hom g := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, AffFun.comp, Matrix.mulVec, dotProduct]

/-- The identity in homogeneous coordinates is the identity matrix. -/
lemma hom_id : hom (AffFun.id : AffFun R d) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [AffFun.id, Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

/-- In homogeneous coordinates, the interpretation of a string (a composition of linear functions) is the product of those of its letters. -/
lemma hom_evA (J : DLetter → AffFun R d) (L : List DLetter) :
    hom (evA J L) = (L.map (fun s => hom (J s))).prod := by
  induction L with
  | nil => simp [evA, hom_id]
  | cons s L ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    exact hom_comp _ _

/-- The last row in homogeneous coordinates is a unit vector, so the last component does not change. -/
lemma hom_mulVec_last (f : AffFun R d) (y : Fin (d + 1) → R) :
    (hom f *ᵥ y) (Fin.last d) = y (Fin.last d) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

end Hom

end Alg

section HomOrder

variable {R : Type} [CommSemiring R] [LinearOrder R] {d : ℕ}

/-- The coefficientwise weak comparison is the entrywise comparison in homogeneous coordinates. -/
lemma hom_le_of_weakA {f g : AffFun R d} (h : WeakA f g) : ∀ i j, hom g i j ≤ hom f i j := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [h.1, h.2]

/-- The first-row weak comparison is the entrywise comparison of the first rows in homogeneous coordinates. -/
lemma hom_top_le_of_weakTop (hd : 0 < d) {f g : AffFun R d} (h : WeakTop hd f g) :
    ∀ j, hom g (Fin.castSucc ⟨0, hd⟩) j ≤ hom f (Fin.castSucc ⟨0, hd⟩) j := by
  intro j
  induction j using Fin.lastCases with
  | last => simp only [hom_cl]; exact h.2
  | cast j => simp only [hom_cc]; exact h.1 j

/-- The first-row strict comparison is the entrywise `≫` of the first rows in homogeneous coordinates. -/
lemma hom_top_gg_of_strictTop (hd : 0 < d) {f g : AffFun R d} (h : StrictTop hd f g) :
    ∀ j, GG (hom f (Fin.castSucc ⟨0, hd⟩) j) (hom g (Fin.castSucc ⟨0, hd⟩) j) := by
  intro j
  induction j using Fin.lastCases with
  | last => simp only [hom_cl]; exact h.2
  | cast j => simp only [hom_cc]; exact h.1 j

end HomOrder

/-! ### Lemmas on values in `Arc` -/

namespace Arc

lemma ne_zero_iff (a : Arc) : a ≠ 0 ↔ val a ≠ ⊥ :=
  ⟨fun h hv => h (ext (by simpa using hv)), fun h h0 => h (by rw [h0]; rfl)⟩

lemma ne_zero_of_le {a b : Arc} (hab : a ≤ b) (ha : a ≠ 0) : b ≠ 0 := by
  rw [ne_zero_iff] at *
  intro hb
  rw [le_iff_val, hb] at hab
  exact ha (le_bot_iff.mp hab)

lemma mul_ne_zero' {a b : Arc} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  rw [ne_zero_iff] at *
  exact mul_ne_zero_of ha hb

lemma exists_fin_of_ne_zero {a : Arc} (ha : a ≠ 0) : ∃ n : ℕ, a = fin n :=
  (val_ne_bot_iff a).mp ((ne_zero_iff a).mp ha)

/-- In the arctic semiring, `l ≫ r` implies `r ⊗ 1 ≤ l` (`r + 1 ≤ l` if `r` is finite). -/
lemma gg_mul_fin_one {l r : Arc} (h : GG l r) : r * fin 1 ≤ l := by
  rcases h with hlt | ⟨-, hr⟩
  · by_cases hr0 : r = 0
    · rw [hr0, zero_mul, le_iff_val]; simp
    · obtain ⟨x, rfl⟩ := exists_fin_of_ne_zero hr0
      have hl0 : l ≠ 0 := by
        intro hl; rw [hl, ← not_le] at hlt; exact hlt (by rw [le_iff_val]; simp)
      obtain ⟨y, rfl⟩ := exists_fin_of_ne_zero hl0
      rw [fin_mul_fin, fin_le_fin]
      exact fin_lt_fin.mp hlt
  · rw [hr, zero_mul, le_iff_val]; simp

/-- `1^k = k` (arctic multiplication is addition). -/
lemma fin_one_pow (k : ℕ) : fin 1 ^ k = fin k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, fin_mul_fin]

lemma fin_inj {m n : ℕ} (h : fin m = fin n) : m = n := by
  have := congrArg val h
  simpa using this

end Arc

end Collatz.Arctic

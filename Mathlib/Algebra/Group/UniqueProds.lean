/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Data.Finset.Pointwise
import Mathlib.LinearAlgebra.Basis.VectorSpace

#align_import algebra.group.unique_prods from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

/-!
# Unique products and related notions

A group `G` has *unique products* if for any two non-empty finite subsets `A, B ⊂ G`, there is an
element `g ∈ A * B` that can be written uniquely as a product of an element of `A` and an element
of `B`.  We call the formalization this property `UniqueProds`.  Since the condition requires no
property of the group operation, we define it for a Type simply satisfying `Mul`.  We also
introduce the analogous "additive" companion, `UniqueSums`, and link the two so that `to_additive`
converts `UniqueProds` into `UniqueSums`.

A common way of *proving* that a group satisfies the `UniqueProds/Sums` property is by assuming
the existence of some kind of ordering on the group that is well-behaved with respect to the
group operation and showing that minima/maxima are the "unique products/sums".
However, the order is just a convenience and is not part of the `UniqueProds/Sums` setup.

Here you can see several examples of Types that have `UniqueSums/Prods`
(`inferInstance` uses `Covariant.to_uniqueProds_left` and `Covariant.to_uniqueSums_left`).
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Group.UniqueProds

example : UniqueSums ℕ   := inferInstance
example : UniqueSums ℕ+  := inferInstance
example : UniqueSums ℤ   := inferInstance
example : UniqueSums ℚ   := inferInstance
example : UniqueSums ℝ   := inferInstance
example : UniqueProds ℕ+ := inferInstance
```

## Use in `(Add)MonoidAlgebra`s

`UniqueProds/Sums` allow to decouple certain arguments about `(Add)MonoidAlgebra`s into an argument
about the grading type and then a generic statement of the form "look at the coefficient of the
'unique product/sum'".
The file `Algebra/MonoidAlgebra/NoZeroDivisors` contains several examples of this use.
-/

/-- Let `G` be a Type with multiplication, let `A B : Finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `UniqueMul A B a0 b0` asserts `a0 * b0` can be written in at
most one way as a product of an element of `A` and an element of `B`. -/
@[to_additive
      "Let `G` be a Type with addition, let `A B : Finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `UniqueAdd A B a0 b0` asserts `a0 + b0` can be written in at
most one way as a sum of an element from `A` and an element from `B`."]
def UniqueMul {G} [Mul G] (A B : Finset G) (a0 b0 : G) : Prop :=
  ∀ ⦃a b⦄, a ∈ A → b ∈ B → a * b = a0 * b0 → a = a0 ∧ b = b0
#align unique_mul UniqueMul
#align unique_add UniqueAdd

namespace UniqueMul

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

@[to_additive (attr := nontriviality, simp)]
theorem of_subsingleton [Subsingleton G] : UniqueMul A B a0 b0 := by simp [UniqueMul]

@[to_additive]
theorem of_card_le_one (hA : A.Nonempty) (hB : B.Nonempty) (hA1 : A.card ≤ 1) (hB1 : B.card ≤ 1) :
    ∃ a ∈ A, ∃ b ∈ B, UniqueMul A B a b := by
  rw [Finset.card_le_one_iff] at hA1 hB1
  obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
  exact ⟨a, ha, b, hb, fun _ _ ha' hb' _ => ⟨hA1 ha' ha, hB1 hb' hb⟩⟩

@[to_additive]
theorem mt (h : UniqueMul A B a0 b0) :
    ∀ ⦃a b⦄, a ∈ A → b ∈ B → a ≠ a0 ∨ b ≠ b0 → a * b ≠ a0 * b0 := fun _ _ ha hb k ↦ by
  contrapose! k
  exact h ha hb k
#align unique_mul.mt UniqueMul.mt

@[to_additive]
theorem subsingleton (h : UniqueMul A B a0 b0) :
    Subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
  ⟨fun ⟨⟨_a, _b⟩, ha, hb, ab⟩ ⟨⟨_a', _b'⟩, ha', hb', ab'⟩ ↦
    Subtype.ext <|
      Prod.ext ((h ha hb ab).1.trans (h ha' hb' ab').1.symm) <|
        (h ha hb ab).2.trans (h ha' hb' ab').2.symm⟩
#align unique_mul.subsingleton UniqueMul.subsingleton
#align unique_add.subsingleton UniqueAdd.subsingleton

@[to_additive]
theorem set_subsingleton (h : UniqueMul A B a0 b0) :
    Set.Subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := by
  rintro ⟨x1, y1⟩ (hx : x1 ∈ A ∧ y1 ∈ B ∧ x1 * y1 = a0 * b0) ⟨x2, y2⟩
    (hy : x2 ∈ A ∧ y2 ∈ B ∧ x2 * y2 = a0 * b0)
  rcases h hx.1 hx.2.1 hx.2.2 with ⟨rfl, rfl⟩
  rcases h hy.1 hy.2.1 hy.2.2 with ⟨rfl, rfl⟩
  rfl
#align unique_mul.set_subsingleton UniqueMul.set_subsingleton
#align unique_add.set_subsingleton UniqueAdd.set_subsingleton

-- Porting note: mathport warning: expanding binder collection
--  (ab «expr ∈ » [finset.product/multiset.product/set.prod/list.product](A, B)) -/
@[to_additive]
theorem iff_existsUnique (aA : a0 ∈ A) (bB : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = a0 * b0 :=
  ⟨fun _ ↦ ⟨(a0, b0), ⟨Finset.mem_product.mpr ⟨aA, bB⟩, rfl⟩, by simpa⟩,
    fun h ↦ h.elim
      (by
        rintro ⟨x1, x2⟩ _ J x y hx hy l
        rcases Prod.mk.inj_iff.mp (J (a0, b0) ⟨Finset.mk_mem_product aA bB, rfl⟩) with ⟨rfl, rfl⟩
        exact Prod.mk.inj_iff.mp (J (x, y) ⟨Finset.mk_mem_product hx hy, l⟩))⟩
#align unique_mul.iff_exists_unique UniqueMul.iff_existsUniqueₓ
#align unique_add.iff_exists_unique UniqueAdd.iff_existsUniqueₓ

open Finset in
@[to_additive]
theorem iff_card_le_one [DecidableEq G] (ha0 : a0 ∈ A) (hb0 : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ((A ×ˢ B).filter (fun p => p.1 * p.2 = a0 * b0)).card ≤ 1 := by
  simp_rw [card_le_one_iff, mem_filter, mem_product]
  refine ⟨fun h p1 p2 ⟨⟨ha1, hb1⟩, he1⟩ ⟨⟨ha2, hb2⟩, he2⟩ => ?_, fun h a b ha hb he => ?_⟩
  · have h1 := h ha1 hb1 he1; have h2 := h ha2 hb2 he2
    ext; rw [h1.1, h2.1]; rw [h1.2, h2.2]
  · exact Prod.ext_iff.1 (@h (a, b) (a0, b0) ⟨⟨ha, hb⟩, he⟩ ⟨⟨ha0, hb0⟩, rfl⟩)

-- Porting note: mathport warning: expanding binder collection
--  (ab «expr ∈ » [finset.product/multiset.product/set.prod/list.product](A, B)) -/
@[to_additive]
theorem exists_iff_exists_existsUnique :
    (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ UniqueMul A B a0 b0) ↔
      ∃ g : G, ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = g :=
  ⟨fun ⟨a0, b0, hA, hB, h⟩ ↦ ⟨_, (iff_existsUnique hA hB).mp h⟩, fun ⟨g, h⟩ ↦ by
    have h' := h
    rcases h' with ⟨⟨a, b⟩, ⟨hab, rfl, -⟩, -⟩
    cases' Finset.mem_product.mp hab with ha hb
    exact ⟨a, b, ha, hb, (iff_existsUnique ha hb).mpr h⟩⟩
#align unique_mul.exists_iff_exists_exists_unique UniqueMul.exists_iff_exists_existsUniqueₓ
#align unique_add.exists_iff_exists_exists_unique UniqueAdd.exists_iff_exists_existsUniqueₓ

/-- `UniqueMul` is preserved by inverse images under injective, multiplicative maps. -/
@[to_additive "`UniqueAdd` is preserved by inverse images under injective, additive maps."]
theorem mulHom_preimage (f : G →ₙ* H) (hf : Function.Injective f) (a0 b0 : G) {A B : Finset H}
    (u : UniqueMul A B (f a0) (f b0)) :
    UniqueMul (A.preimage f (Set.injOn_of_injective hf _))
      (B.preimage f (Set.injOn_of_injective hf _)) a0 b0 := by
  intro a b ha hb ab
  simp only [← hf.eq_iff, map_mul] at ab ⊢
  exact u (Finset.mem_preimage.mp ha) (Finset.mem_preimage.mp hb) ab
#align unique_mul.mul_hom_preimage UniqueMul.mulHom_preimage
#align unique_add.add_hom_preimage UniqueAdd.addHom_preimage

/-- `Unique_Mul` is preserved under multiplicative maps that are injective.

See `UniqueMul.mulHom_map_iff` for a version with swapped bundling. -/
@[to_additive
      "`UniqueAdd` is preserved under additive maps that are injective.

See `UniqueAdd.addHom_map_iff` for a version with swapped bundling."]
theorem mulHom_image_iff [DecidableEq H] (f : G →ₙ* H) (hf : Function.Injective f) :
    UniqueMul (A.image f) (B.image f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  simp_rw [UniqueMul, Finset.mem_image]
  refine' ⟨fun h a b ha hb ab ↦ _, fun h ↦ _⟩
  · rw [← hf.eq_iff, map_mul, map_mul] at ab
    have := h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ab
    exact ⟨hf this.1, hf this.2⟩
  · rintro _ _ ⟨a, aA, rfl⟩ ⟨b, bB, rfl⟩ ab
    simp only [← map_mul, hf.eq_iff] at ab ⊢
    exact h aA bB ab
#align unique_mul.mul_hom_image_iff UniqueMul.mulHom_image_iff
#align unique_add.add_hom_image_iff UniqueAdd.addHom_image_iff

/-- `UniqueMul` is preserved under embeddings that are multiplicative.

See `UniqueMul.mulHom_image_iff` for a version with swapped bundling. -/
@[to_additive
      "`UniqueAdd` is preserved under embeddings that are additive.

See `UniqueAdd.addHom_image_iff` for a version with swapped bundling."]
theorem mulHom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
    UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  classical
  convert @mulHom_image_iff G H _ _ A B a0 b0 _ ⟨f, mul⟩ f.2 using 2 <;>
    · ext
      simp only [Finset.mem_map, MulHom.coe_mk, Finset.mem_image]
#align unique_mul.mul_hom_map_iff UniqueMul.mulHom_map_iff
#align unique_add.add_hom_map_iff UniqueAdd.addHom_map_iff

section Opposites
open Finset MulOpposite

@[to_additive]
theorem of_mulOpposite
    (h : UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) :
    UniqueMul A B a0 b0 := by
  intros a b aA bB ab
  have := h (mem_map_of_mem _ bB) (mem_map_of_mem _ aA) (by simpa using congr_arg op ab)
  simpa [and_comm] using this

@[to_additive]
theorem to_mulOpposite (h : UniqueMul A B a0 b0) :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) := by
  refine of_mulOpposite (G := MulOpposite G) <| fun a b ha hb hab ↦ ?_
  simp only [mem_map, Function.Embedding.coeFn_mk, exists_exists_and_eq_and] at ha hb
  rcases ha with ⟨a, ha, rfl⟩
  rcases hb with ⟨b, hb, rfl⟩
  rw [op_inj, op_inj, op_inj, op_inj]
  apply h ha hb ?_
  apply_fun op ∘ op using op_injective.comp op_injective
  exact hab

@[to_additive]
theorem iff_mulOpposite :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) ↔
      UniqueMul A B a0 b0 :=
⟨of_mulOpposite, to_mulOpposite⟩

end Opposites
open Finset in
@[to_additive]
theorem of_image_filter [DecidableEq H]
    (f : G →ₙ* H) {A B : Finset G} {aG bG : G} {aH bH : H} (hae : f aG = aH) (hbe : f bG = bH)
    (huH : UniqueMul (A.image f) (B.image f) aH bH)
    (huG : UniqueMul (A.filter (f · = aH)) (B.filter (f · = bH)) aG bG) :
    UniqueMul A B aG bG := fun a b ha hb he => by
  specialize huH (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
  rw [← map_mul, he, map_mul, hae, hbe] at huH
  refine huG ?_ ?_ he <;> rw [mem_filter]
  exacts [⟨ha, (huH rfl).1⟩, ⟨hb, (huH rfl).2⟩]

end UniqueMul

/-- Let `G` be a Type with addition.  `UniqueSums G` asserts that any two non-empty
finite subsets of `G` have the `UniqueAdd` property, with respect to some element of their
sum `A + B`. -/
class UniqueSums (G) [Add G] : Prop where
/-- For `A B` two nonempty finite sets, there always exist `a0 ∈ A, b0 ∈ B` such that
`UniqueAdd A B a0 b0` -/
  uniqueAdd_of_nonempty :
    ∀ {A B : Finset G}, A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueAdd A B a0 b0
#align unique_sums UniqueSums

/-- Let `G` be a Type with multiplication.  `UniqueProds G` asserts that any two non-empty
finite subsets of `G` have the `UniqueMul` property, with respect to some element of their
product `A * B`. -/
class UniqueProds (G) [Mul G] : Prop where
/-- For `A B` two nonempty finite sets, there always exist `a0 ∈ A, b0 ∈ B` such that
`UniqueMul A B a0 b0` -/
  uniqueMul_of_nonempty :
    ∀ {A B : Finset G}, A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueMul A B a0 b0
#align unique_prods UniqueProds

attribute [to_additive] UniqueProds

/-- Let `G` be a Type with addition. `TwoUniqueSums G` asserts that any two non-empty
finite subsets of `G`, at least one of which is not a singleton, possesses at least two pairs
of elements satisfying the `UniqueAdd` property. -/
class TwoUniqueSums (G) [Add G] : Prop where
/-- For `A B` two finite sets whose product has cardinality at least 2,
  we can find at least two unique pairs. -/
  uniqueAdd_of_one_lt_card : ∀ {A B : Finset G}, 1 < A.card * B.card →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueAdd A B p1.1 p1.2 ∧ UniqueAdd A B p2.1 p2.2

/-- Let `G` be a Type with multiplication. `TwoUniqueProds G` asserts that any two non-empty
finite subsets of `G`, at least one of which is not a singleton, possesses at least two pairs
of elements satisfying the `UniqueMul` property. -/
class TwoUniqueProds (G) [Mul G] : Prop where
/-- For `A B` two finite sets whose product has cardinality at least 2,
  we can find at least two unique pairs. -/
  uniqueMul_of_one_lt_card : ∀ {A B : Finset G}, 1 < A.card * B.card →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueMul A B p1.1 p1.2 ∧ UniqueMul A B p2.1 p2.2

attribute [to_additive] TwoUniqueProds

@[to_additive]
lemma UniqueMul_of_TwoUniqueMul {G} [Mul G] {A B : Finset G} (h : 1 < A.card * B.card →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueMul A B p1.1 p1.2 ∧ UniqueMul A B p2.1 p2.2)
    (hA : A.Nonempty) (hB : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, UniqueMul A B a b := by
  by_cases hc : A.card ≤ 1 ∧ B.card ≤ 1
  · exact UniqueMul.of_card_le_one hA hB hc.1 hc.2
  simp_rw [not_and_or, not_le] at hc
  rw [← Finset.card_pos] at hA hB
  obtain ⟨p, hp, _, _, _, hu, _⟩ := h (Nat.one_lt_mul_iff.mpr ⟨hA, hB, hc⟩)
  rw [Finset.mem_product] at hp
  exact ⟨p.1, hp.1, p.2, hp.2, hu⟩

@[to_additive] instance TwoUniqueProds.toUniqueProds (G) [Mul G] [TwoUniqueProds G] :
    UniqueProds G where
  uniqueMul_of_nonempty := UniqueMul_of_TwoUniqueMul uniqueMul_of_one_lt_card

namespace Multiplicative

instance {M} [Add M] [UniqueSums M] : UniqueProds (Multiplicative M) where
  uniqueMul_of_nonempty := UniqueSums.uniqueAdd_of_nonempty (G := M)

instance {M} [Add M] [TwoUniqueSums M] : TwoUniqueProds (Multiplicative M) where
  uniqueMul_of_one_lt_card := TwoUniqueSums.uniqueAdd_of_one_lt_card (G := M)

end Multiplicative

namespace Additive

instance {M} [Mul M] [UniqueProds M] : UniqueSums (Additive M) where
  uniqueAdd_of_nonempty := UniqueProds.uniqueMul_of_nonempty (G := M)

instance {M} [Mul M] [TwoUniqueProds M] : TwoUniqueSums (Additive M) where
  uniqueAdd_of_one_lt_card := TwoUniqueProds.uniqueMul_of_one_lt_card (G := M)

end Additive

#noalign covariants.to_unique_prods
#noalign covariants.to_unique_sums

universe u v
variable (G : Type u) (H : Type v) [Mul G] [Mul H]

private abbrev I : Bool → Type max u v := Bool.rec (ULift.{v} G) (ULift.{u} H)
@[to_additive] private instance : ∀ b, Mul (I G H b) := Bool.rec ULift.mul ULift.mul
@[to_additive] private def Prod.upMulHom : G × H →ₙ* ∀ b, I G H b :=
  ⟨fun x => Bool.rec ⟨x.1⟩ ⟨x.2⟩, fun x y => by ext b; cases b <;> rfl⟩
@[to_additive] private def downMulHom : ULift G →ₙ* G := ⟨fun x => ULift.down x, fun _ _ => rfl⟩

variable {G H}

namespace UniqueProds

open Finset
@[to_additive]
theorem mulHom_image_of_injective (f : H →ₙ* G) (hf : Function.Injective f) (uG : UniqueProds G) :
    UniqueProds H where
  uniqueMul_of_nonempty {A B} A0 B0 := by
    classical
    obtain ⟨a0, ha0, b0, hb0, h⟩ := uG.uniqueMul_of_nonempty (A0.image f) (B0.image f)
    rcases mem_image.mp ha0 with ⟨a', ha', rfl⟩
    rcases mem_image.mp hb0 with ⟨b', hb', rfl⟩
    exact ⟨a', ha', b', hb', (UniqueMul.mulHom_image_iff f hf).mp h⟩

/-- `UniqueProd` is preserved under multiplicative equivalences. -/
@[to_additive "`UniqueSums` is preserved under additive equivalences."]
theorem mulHom_image_iff (f : G ≃* H) :
    UniqueProds G ↔ UniqueProds H :=
⟨mulHom_image_of_injective f.symm f.symm.injective, mulHom_image_of_injective f f.injective⟩

open Finset MulOpposite in
@[to_additive]
theorem of_mulOpposite (h : UniqueProds Gᵐᵒᵖ) : UniqueProds G where
  uniqueMul_of_nonempty hA hB :=
    let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
    let ⟨y, yB, x, xA, hxy⟩ := h.uniqueMul_of_nonempty (hB.map (f := f)) (hA.map (f := f))
    ⟨unop x, (mem_map' _).mp xA, unop y, (mem_map' _).mp yB, hxy.of_mulOpposite⟩

@[to_additive] instance [h : UniqueProds G] : UniqueProds Gᵐᵒᵖ :=
  of_mulOpposite <| (mulHom_image_iff <| MulEquiv.opOp G).mp h

open UniqueMul in
@[to_additive] instance {ι} (G : ι → Type*) [∀ i, Mul (G i)] [∀ i, UniqueProds (G i)] :
    UniqueProds (∀ i, G i) where
  uniqueMul_of_nonempty {A} := by
    classical
    let _ := isWellFounded_ssubset (α := ∀ i, G i) -- why need this?
    apply IsWellFounded.induction (· ⊂ ·) A; intro A ihA B hA
    apply IsWellFounded.induction (· ⊂ ·) B; intro B ihB hB
    by_cases hc : A.card ≤ 1 ∧ B.card ≤ 1
    · exact of_card_le_one hA hB hc.1 hc.2
    simp_rw [not_and_or, not_le] at hc
    obtain ⟨i, hc⟩ := exists_or.mpr (hc.imp exists_of_one_lt_card_pi exists_of_one_lt_card_pi)
    obtain ⟨ai, hA, bi, hB, hi⟩ := uniqueMul_of_nonempty (hA.image (· i)) (hB.image (· i))
    rw [mem_image, ← filter_nonempty_iff] at hA hB
    let A' := A.filter (· i = ai); let B' := B.filter (· i = bi)
    obtain ⟨a0, ha0, b0, hb0, hu⟩ : ∃ a0 ∈ A', ∃ b0 ∈ B', UniqueMul A' B' a0 b0
    · rcases hc with hc | hc; · exact ihA A' (hc.2 ai) hA hB
      by_cases hA' : A' = A; rw [hA']
      exacts [ihB B' (hc.2 bi) hB, ihA A' ((A.filter_subset _).ssubset_of_ne hA') hA hB]
    rw [mem_filter] at ha0 hb0
    exact ⟨a0, ha0.1, b0, hb0.1, of_image_filter (Pi.evalMulHom G i) ha0.2 hb0.2 hi hu⟩

open ULift in
instance [UniqueProds G] [UniqueProds H] : UniqueProds (G × H) := by
  have : ∀ b, UniqueProds (I G H b) := Bool.rec ?_ ?_
  · exact mulHom_image_of_injective (downMulHom H) down_injective ‹_›
  · refine mulHom_image_of_injective (Prod.upMulHom G H) (fun x y he => Prod.ext ?_ ?_)
      (instUniqueProdsForAllInstMul <| I G H) <;> apply up_injective
    exacts [congr_fun he false, congr_fun he true]
  · exact mulHom_image_of_injective (downMulHom G) down_injective ‹_›

end UniqueProds

instance {ι} (G : ι → Type*) [∀ i, AddZeroClass (G i)] [∀ i, UniqueSums (G i)] :
    UniqueSums (Π₀ i, G i) :=
  UniqueSums.addHom_image_of_injective
    DFinsupp.coeFnAddMonoidHom.toAddHom FunLike.coe_injective inferInstance

instance {ι G} [AddZeroClass G] [UniqueSums G] : UniqueSums (ι →₀ G) :=
  UniqueSums.addHom_image_of_injective
    Finsupp.coeFnAddHom.toAddHom FunLike.coe_injective inferInstance

namespace TwoUniqueProds

open Finset
@[to_additive]
theorem mulHom_image_of_injective (f : H →ₙ* G) (hf : Function.Injective f)
    (uG : TwoUniqueProds G) : TwoUniqueProds H where
  uniqueMul_of_one_lt_card {A B} hc := by
    classical
    simp_rw [← card_map ⟨f, hf⟩] at hc
    obtain ⟨⟨a1, b1⟩, h1, ⟨a2, b2⟩, h2, hne, hu1, hu2⟩ := uG.uniqueMul_of_one_lt_card hc
    simp only [mem_product, mem_map] at h1 h2 ⊢
    obtain ⟨⟨a1, ha1, rfl⟩, ⟨b1, hb1, rfl⟩⟩ := h1
    obtain ⟨⟨a2, ha2, rfl⟩, ⟨b2, hb2, rfl⟩⟩ := h2
    refine ⟨(a1, b1), ⟨ha1, hb1⟩, (a2, b2), ⟨ha2, hb2⟩, ?_, ?_, ?_⟩
    · rw [Ne, Prod.ext_iff] at hne ⊢; simp_rw [← hf.eq_iff]; exact hne
    all_goals apply (UniqueMul.mulHom_map_iff ⟨f, hf⟩ f.2).mp
    exacts [hu1, hu2]

/-- `TwoUniqueProd` is preserved under multiplicative equivalences. -/
@[to_additive "`TwoUniqueSums` is preserved under additive equivalences."]
theorem mulHom_image_iff (f : G ≃* H) : TwoUniqueProds G ↔ TwoUniqueProds H :=
⟨mulHom_image_of_injective f.symm f.symm.injective, mulHom_image_of_injective f f.injective⟩

open Finset in
@[to_additive] instance {ι} (G : ι → Type*) [∀ i, Mul (G i)] [∀ i, TwoUniqueProds (G i)] :
    TwoUniqueProds (∀ i, G i) where
  uniqueMul_of_one_lt_card {A} := by
    classical
    let _ := isWellFounded_ssubset (α := ∀ i, G i) -- why need this?
    apply IsWellFounded.induction (· ⊂ ·) A; intro A ihA B
    apply IsWellFounded.induction (· ⊂ ·) B; intro B ihB hc
    obtain ⟨hA, hB, hc⟩ := Nat.one_lt_mul_iff.mp hc
    rw [card_pos] at hA hB
    obtain ⟨i, hc⟩ := exists_or.mpr (hc.imp exists_of_one_lt_card_pi exists_of_one_lt_card_pi)
    obtain ⟨p1, h1, p2, h2, hne, hi1, hi2⟩ := uniqueMul_of_one_lt_card (Nat.one_lt_mul_iff.mpr
      ⟨card_pos.2 (hA.image _), card_pos.2 (hB.image _), hc.imp And.left And.left⟩)
    simp_rw [mem_product, mem_image, ← filter_nonempty_iff] at h1 h2
    replace h1 := UniqueMul_of_TwoUniqueMul ?_ h1.1 h1.2
    replace h2 := UniqueMul_of_TwoUniqueMul ?_ h2.1 h2.2
    · obtain ⟨a1, ha1, b1, hb1, hu1⟩ := h1
      obtain ⟨a2, ha2, b2, hb2, hu2⟩ := h2
      rw [mem_filter] at ha1 hb1 ha2 hb2
      simp_rw [mem_product]
      refine ⟨(a1, b1), ⟨ha1.1, hb1.1⟩, (a2, b2), ⟨ha2.1, hb2.1⟩, ?_,
        UniqueMul.of_image_filter (Pi.evalMulHom G i) ha1.2 hb1.2 hi1 hu1,
        UniqueMul.of_image_filter (Pi.evalMulHom G i) ha2.2 hb2.2 hi2 hu2⟩
      contrapose! hne; rw [Prod.mk.inj_iff] at hne ⊢
      rw [← ha1.2, ← hb1.2, ← ha2.2, ← hb2.2, hne.1, hne.2]; exact ⟨rfl, rfl⟩
    all_goals
      rcases hc with hc | hc; · exact ihA _ (hc.2 _)
      by_cases hA : A.filter (· i = _) = A; rw [hA]
      exacts [ihB _ (hc.2 _), ihA _ ((A.filter_subset _).ssubset_of_ne hA)]

open ULift in
instance [TwoUniqueProds G] [TwoUniqueProds H] : TwoUniqueProds (G × H) := by
  have : ∀ b, TwoUniqueProds (I G H b) := Bool.rec ?_ ?_
  · exact mulHom_image_of_injective (downMulHom H) down_injective ‹_›
  · refine mulHom_image_of_injective (Prod.upMulHom G H) (fun x y he => Prod.ext ?_ ?_)
      (instTwoUniqueProdsForAllInstMul <| I G H) <;> apply up_injective
    exacts [congr_fun he false, congr_fun he true]
  · exact mulHom_image_of_injective (downMulHom G) down_injective ‹_›

open Finset MulOpposite in
@[to_additive]
theorem of_mulOpposite (h : TwoUniqueProds Gᵐᵒᵖ) : TwoUniqueProds G where
  uniqueMul_of_one_lt_card hc := by
    let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
    rw [← card_map f, ← card_map f, mul_comm] at hc
    obtain ⟨p1, h1, p2, h2, hne, hu1, hu2⟩ := h.uniqueMul_of_one_lt_card hc
    simp_rw [mem_product] at h1 h2 ⊢
    refine ⟨(_, _), ⟨?_, ?_⟩, (_, _), ⟨?_, ?_⟩, ?_, hu1.of_mulOpposite, hu2.of_mulOpposite⟩
    pick_goal 5
    · contrapose! hne; rw [Prod.ext_iff] at hne ⊢
      exact ⟨unop_injective hne.2, unop_injective hne.1⟩
    all_goals apply (mem_map' f).mp
    exacts [h1.2, h1.1, h2.2, h2.1]

@[to_additive] instance [h : TwoUniqueProds G] : TwoUniqueProds Gᵐᵒᵖ :=
  of_mulOpposite <| (mulHom_image_iff <| MulEquiv.opOp G).mp h

open Finset in
-- see Note [lower instance priority]
/-- This instance asserts that if `G` has a right-cancellative multiplication, a linear order, and
  multiplication is strictly monotone w.r.t. the second argument, then `G` has `TwoUniqueProds`. -/
@[to_additive
  "This instance asserts that if `G` has a right-cancellative addition, a linear order,
  and addition is strictly monotone w.r.t. the second argument, then `G` has `TwoUniqueSums`." ]
instance (priority := 100) of_Covariant_right [IsRightCancelMul G]
    [LinearOrder G] [CovariantClass G G (· * ·) (· < ·)] :
    TwoUniqueProds G where
  uniqueMul_of_one_lt_card {A B} hc := by
    obtain ⟨hA, hB, -⟩ := Nat.one_lt_mul_iff.mp hc
    rw [card_pos] at hA hB
    rw [← card_product] at hc
    obtain ⟨a0, b0, ha0, hb0, he0⟩ := mem_mul.mp (max'_mem _ <| hA.mul hB)
    obtain ⟨a1, b1, ha1, hb1, he1⟩ := mem_mul.mp (min'_mem _ <| hA.mul hB)
    have : UniqueMul A B a0 b0
    · intro a b ha hb he
      obtain hl | rfl | hl := lt_trichotomy b b0
      · exact ((he0 ▸ he ▸ mul_lt_mul_left' hl a).not_le <| le_max' _ _ <| mul_mem_mul ha hb0).elim
      · exact ⟨mul_right_cancel he, rfl⟩
      · exact ((he0 ▸ mul_lt_mul_left' hl a0).not_le <| le_max' _ _ <| mul_mem_mul ha0 hb).elim
    refine ⟨(a0, b0), mem_product.2 ⟨ha0, hb0⟩, (a1, b1), mem_product.2 ⟨ha1, hb1⟩,
      fun he => ?_, this, fun a b ha hb he => ?_⟩
    · rw [UniqueMul.iff_card_le_one ha0 hb0, filter_eq_self.mpr (fun p hp => ?_)] at this
      · exact hc.not_le this
      rw [mem_product] at hp
      apply ((le_max' _ _ <| mul_mem_mul hp.1 hp.2).trans_eq he0.symm).antisymm
      rw [Prod.mk.inj_iff] at he; rw [he.1, he.2, he1]
      exact min'_le _ _ (mul_mem_mul hp.1 hp.2)
    · dsimp only at he ⊢; obtain hl | rfl | hl := lt_trichotomy b b1
      · exact ((he1 ▸ mul_lt_mul_left' hl a1).not_le <| min'_le _ _ <| mul_mem_mul ha1 hb).elim
      · exact ⟨mul_right_cancel he, rfl⟩
      · exact ((he1 ▸ he ▸ mul_lt_mul_left' hl a).not_le <| min'_le _ _ <| mul_mem_mul ha hb1).elim

open MulOpposite in
-- see Note [lower instance priority]
/-- This instance asserts that if `G` has a left-cancellative multiplication, a linear order, and
  multiplication is strictly monotone w.r.t. the first argument, then `G` has `TwoUniqueProds`. -/
@[to_additive
  "This instance asserts that if `G` has a left-cancellative addition, a linear order, and
  addition is strictly monotone w.r.t. the first argument, then `G` has `TwoUniqueSums`." ]
instance (priority := 100) of_Covariant_left [IsLeftCancelMul G]
    [LinearOrder G] [CovariantClass G G (Function.swap (· * ·)) (· < ·)] :
    TwoUniqueProds G :=
  let _ := LinearOrder.lift' (unop : Gᵐᵒᵖ → G) unop_injective
  let _ : CovariantClass Gᵐᵒᵖ Gᵐᵒᵖ (· * ·) (· < ·) :=
  { elim := fun _ _ _ bc => mul_lt_mul_right' (α := G) bc (unop _) }
  of_mulOpposite of_Covariant_right

end TwoUniqueProds

instance {ι} (G : ι → Type*) [∀ i, AddZeroClass (G i)] [∀ i, TwoUniqueSums (G i)] :
    TwoUniqueSums (Π₀ i, G i) :=
  TwoUniqueSums.addHom_image_of_injective
    DFinsupp.coeFnAddMonoidHom.toAddHom FunLike.coe_injective inferInstance

instance {ι G} [AddZeroClass G] [TwoUniqueSums G] : TwoUniqueSums (ι →₀ G) :=
  TwoUniqueSums.addHom_image_of_injective
    Finsupp.coeFnAddHom.toAddHom FunLike.coe_injective inferInstance

/-- Any `ℚ`-vector space has `TwoUniqueSums`, because it is isomorphic to some
  `(Basis.ofVectorSpaceIndex ℚ G) →₀ ℚ` by choosing a basis, and `ℚ` already has
  `TwoUniqueSums` because it's ordered. -/
instance [AddCommGroup G] [Module ℚ G] : TwoUniqueSums G :=
  TwoUniqueSums.addHom_image_of_injective _ (Basis.ofVectorSpace ℚ G).repr.injective inferInstance

/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.NonemptyFinLinOrd
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite
import Mathlib.Order.Category.LinOrd
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear
orders with monotone maps. This is the index category for simplicial objects.
-/


universe u v

open CategoryTheory CategoryTheory.Limits

/-- A typeclass for nonempty finite linear orders. -/
class NonemptyFinLinOrd (α : Type _) extends Fintype α, LinearOrder α where
  Nonempty : Nonempty α := by infer_instance
#align nonempty_fin_lin_ord NonemptyFinLinOrd

attribute [instance] NonemptyFinLinOrd.Nonempty

instance (priority := 100) NonemptyFinLinOrd.toBoundedOrder (α : Type _) [NonemptyFinLinOrd α] :
    BoundedOrder α :=
  Fintype.toBoundedOrder α
#align nonempty_fin_lin_ord.to_bounded_order NonemptyFinLinOrd.toBoundedOrder

instance PUnit.nonemptyFinLinOrd : NonemptyFinLinOrd PUnit where
#align punit.nonempty_fin_lin_ord PUnit.nonemptyFinLinOrd

instance Fin.nonemptyFinLinOrd (n : ℕ) : NonemptyFinLinOrd (Fin (n + 1)) where
#align fin.nonempty_fin_lin_ord Fin.nonemptyFinLinOrd

instance ULift.nonemptyFinLinOrd (α : Type u) [NonemptyFinLinOrd α] :
    NonemptyFinLinOrd (ULift.{v} α) :=
  { LinearOrder.lift' Equiv.ulift (Equiv.injective _) with }
#align ulift.nonempty_fin_lin_ord ULift.nonemptyFinLinOrd

instance (α : Type _) [NonemptyFinLinOrd α] : NonemptyFinLinOrd αᵒᵈ :=
  { OrderDual.fintype α with }

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrd :=
  Bundled NonemptyFinLinOrd
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd NonemptyFinLinOrd

namespace NonemptyFinLinOrd

instance : BundledHom.ParentProjection @NonemptyFinLinOrd.toLinearOrder :=
  ⟨⟩

deriving instance LargeCategory for NonemptyFinLinOrd

instance : ConcreteCategory NonemptyFinLinOrd :=
  BundledHom.concreteCategory _

instance : CoeSort NonemptyFinLinOrd (Type _) :=
  Bundled.coeSort

/-- Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass. -/
def of (α : Type _) [NonemptyFinLinOrd α] : NonemptyFinLinOrd :=
  Bundled.of α
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.of NonemptyFinLinOrd.of

@[simp]
theorem coe_of (α : Type _) [NonemptyFinLinOrd α] : ↥(of α) = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.coe_of NonemptyFinLinOrd.coe_of

instance : Inhabited NonemptyFinLinOrd :=
  ⟨of PUnit⟩

instance (α : NonemptyFinLinOrd) : NonemptyFinLinOrd α :=
  α.str

instance hasForgetToLinOrd : HasForget₂ NonemptyFinLinOrd LinOrd :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.has_forget_to_LinOrd NonemptyFinLinOrd.hasForgetToLinOrd

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom _ _)
  inv := (e.symm : OrderHom _ _)
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.iso.mk NonemptyFinLinOrd.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd where
  obj X := of Xᵒᵈ
  map := OrderHom.dual
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.dual NonemptyFinLinOrd.dual

/-- The equivalence between `FinPartOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : NonemptyFinLinOrd ≌ NonemptyFinLinOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) (fun _ => rfl)
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.dual_equiv NonemptyFinLinOrd.dualEquiv

-- porting note: this instance was not necessary in mathlib
instance {A B : NonemptyFinLinOrd.{u}} : OrderHomClass (A ⟶ B) A B where
  coe f := ⇑(show OrderHom A B from f)
  coe_injective' _ _ h := by
    ext x
    exact congr_fun h x
  map_rel f _ _ h := f.monotone h

theorem mono_iff_injective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f := by
  refine' ⟨_, ConcreteCategory.mono_of_injective f⟩
  intro
  intro a₁ a₂ h
  let X := NonemptyFinLinOrd.of (ULift (Fin 1))
  let g₁ : X ⟶ A := ⟨fun _ => a₁, fun _ _  _ => by rfl⟩
  let g₂ : X ⟶ A := ⟨fun _ => a₂, fun _ _  _ => by rfl⟩
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  have eq : g₁ ≫ f = g₂ ≫ f := by
    ext
    exact h
  rw [cancel_mono] at eq
  rw [eq]
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.mono_iff_injective NonemptyFinLinOrd.mono_iff_injective

-- porting note: added to ease the following proof
lemma forget_map_apply {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) (a : A) :
  (forget NonemptyFinLinOrd).map f a = (f : OrderHom A B).toFun a := rfl

theorem epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · intro
    dsimp only [Function.Surjective]
    by_contra' hf'
    rcases hf' with ⟨m, hm⟩
    let Y := NonemptyFinLinOrd.of (ULift (Fin 2))
    let p₁ : B ⟶ Y :=
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (lt_of_le_of_lt h h₂)
        · rfl⟩
    let p₂ : B ⟶ Y :=
      ⟨fun b => if b ≤ m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (h.trans h₂)
        · rfl⟩
    have h : p₁ m = p₂ m := by
      congr
      rw [← cancel_epi f]
      ext a
      simp only [forget_obj_eq_coe, coe_of, FunctorToTypes.map_comp_apply]
      simp only [forget_map_apply]
      split_ifs with h₁ h₂ h₂
      any_goals rfl
      · exfalso
        exact h₂ (le_of_lt h₁)
      · exfalso
        exact hm a (eq_of_le_of_not_lt h₂ h₁)
    simp [FunLike.coe] at h
  · intro h
    exact ConcreteCategory.epi_of_surjective f h
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.epi_iff_surjective NonemptyFinLinOrd.epi_iff_surjective

instance : SplitEpiCategory NonemptyFinLinOrd.{u} :=
  ⟨fun {X Y} f hf => by
    have H : ∀ y : Y, Nonempty (f ⁻¹' {y}) := by
      rw [epi_iff_surjective] at hf
      intro y
      exact Nonempty.intro ⟨(hf y).choose, (hf y).choose_spec⟩
    let φ : Y → X := fun y => (H y).some.1
    have hφ : ∀ y : Y, f (φ y) = y := fun y => (H y).some.2
    refine' IsSplitEpi.mk' ⟨⟨φ, _⟩, _⟩
    swap
    · ext b
      apply hφ
    · intro a b
      contrapose
      intro h
      simp only [not_le] at h⊢
      suffices b ≤ a by
        apply lt_of_le_of_ne this
        rintro rfl
        exfalso
        simp at h
      have H : f (φ b) ≤ f (φ a) := f.monotone (le_of_lt h)
      simpa only [hφ] using H⟩

instance : HasStrongEpiMonoFactorisations NonemptyFinLinOrd.{u} :=
  ⟨fun {X Y} f => by
    letI : NonemptyFinLinOrd (Set.image f ⊤) := ⟨by infer_instance⟩
    let I := NonemptyFinLinOrd.of (Set.image f ⊤)
    let e : X ⟶ I := ⟨fun x => ⟨f x, ⟨x, by tauto⟩⟩, fun x₁ x₂ h => f.monotone h⟩
    let m : I ⟶ Y := ⟨fun y => y.1, by tauto⟩
    haveI : Epi e := by
      rw [epi_iff_surjective]
      rintro ⟨_, y, h, rfl⟩
      exact ⟨y, rfl⟩
    haveI : StrongEpi e := strongEpi_of_epi e
    haveI : Mono m := ConcreteCategory.mono_of_injective _ (fun x y h => Subtype.ext h)
    exact ⟨⟨I, m, e, rfl⟩⟩⟩

end NonemptyFinLinOrd

theorem nonemptyFinLinOrd_dual_comp_forget_to_linOrdCat :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd LinOrd =
      forget₂ NonemptyFinLinOrd LinOrd ⋙ LinOrd.dual :=
  rfl
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd_dual_comp_forget_to_LinOrd nonemptyFinLinOrd_dual_comp_forget_to_linOrdCat

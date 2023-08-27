/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Module.basic
! leanprover-community/mathlib commit 829895f162a1f29d0133f4b3538f4cd1fb5bffd3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Elementwise
import Mathlib.LinearAlgebra.Basic
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The category of `R`-modules

`Module.{v} R` is the category of bundled `R`-modules with carrier in the universe `v`. We show
that it is preadditive and show that being an isomorphism, monomorphism and epimorphism is
equivalent to being a linear equivalence, an injective linear map and a surjective linear map,
respectively.

## Implementation details

To construct an object in the category of `R`-modules from a type `M` with an instance of the
`Module` typeclass, write `of R M`. There is a coercion in the other direction.

Similarly, there is a coercion from morphisms in `Module R` to linear maps.

Unfortunately, Lean is not smart enough to see that, given an object `M : Module R`, the expression
`of R M`, where we coerce `M` to the carrier type, is definitionally equal to `M` itself.
This means that to go the other direction, i.e., from linear maps/equivalences to (iso)morphisms
in the category of `R`-modules, we have to take care not to inadvertently end up with an
`of R M` where `M` is already an object. Hence, given `f : M →ₗ[R] N`,
* if `M N : Module R`, simply use `f`;
* if `M : Module R` and `N` is an unbundled `R`-module, use `↿f` or `asHomLeft f`;
* if `M` is an unbundled `R`-module and `N : Module R`, use `↾f` or `asHomRight f`;
* if `M` and `N` are unbundled `R`-modules, use `↟f` or `asHom f`.

Similarly, given `f : M ≃ₗ[R] N`, use `toModuleIso`, `toModuleIso'Left`, `toModuleIso'Right`
or `toModuleIso'`, respectively.

The arrow notations are localized, so you may have to `open_locale Module` to use them. Note that
the notation for `asHomLeft` clashes with the notation used to promote functions between types to
morphisms in the category `Type`, so to avoid confusion, it is probably a good idea to avoid having
the locales `Module` and `CategoryTheory.Type` open at the same time.

If you get an error when trying to apply a theorem and the `convert` tactic produces goals of the
form `M = of R M`, then you probably used an incorrect variant of `asHom` or `toModuleIso`.

-/


open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [Ring R]

/-- The category of R-modules and their morphisms.

 Note that in the case of `R = ℤ`, we can not
impose here that the `ℤ`-multiplication field from the module structure is defeq to the one coming
from the `isAddCommGroup` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
structure Mod where
  /-- the underlying type of an object in `Mod R` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
set_option linter.uppercaseLean3 false in
#align Module Mod

attribute [instance] Mod.isAddCommGroup Mod.isModule

namespace Mod

instance : CoeSort (Mod.{v} R) (Type v) :=
  ⟨Mod.carrier⟩

attribute [-instance] Ring.toNonAssocRing

instance Modegory : Category (Mod.{v} R) where
  Hom M N := M →ₗ[R] N
  id _ := LinearMap.id -- porting note: was `1`
  comp f g := g.comp f
  id_comp _ := LinearMap.id_comp _
  comp_id _ := LinearMap.comp_id _
  assoc f g h := @LinearMap.comp_assoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    RingHomCompTriple.ids RingHomCompTriple.ids RingHomCompTriple.ids f g h
set_option linter.uppercaseLean3 false in
#align Module.Module_category Mod.Modegory

-- porting note: was not necessary in mathlib
instance {M N : Mod.{v} R} : FunLike (M ⟶ N) M (fun _ => N) :=
  ⟨fun f => f.toFun, fun _ _ h => LinearMap.ext (congr_fun h)⟩

instance moduleConcreteCategory : ConcreteCategory.{v} (Mod.{v} R) where
  Forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => LinearMap.ext (fun x => by
    dsimp at h
    rw [h])⟩
set_option linter.uppercaseLean3 false in
#align Module.Module_concrete_category Mod.moduleConcreteCategory

-- porting note: added to ease automation
@[ext]
lemma hom_ext {M N : Mod.{v} R} (f₁ f₂ : M ⟶ N) (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  FunLike.ext _ _ h

instance hasForgetToAddCommGroup : HasForget₂ (Mod R) AddCommGroupCat where
  forget₂ :=
    { obj := fun M => AddCommGroupCat.of M
      map := fun f => LinearMap.toAddMonoidHom f }
set_option linter.uppercaseLean3 false in
#align Module.has_forget_to_AddCommGroup Mod.hasForgetToAddCommGroup

instance (M N : Mod R) : LinearMapClass (M ⟶ N) R M N :=
  { LinearMap.instSemilinearMapClassLinearMap with coe := fun f => f }

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type v) [AddCommGroup X] [Module R X] : Mod R :=
  ⟨X⟩
set_option linter.uppercaseLean3 false in
#align Module.of Mod.of

-- porting note: remove simp attribute because it makes the linter complain
theorem forget₂_obj (X : Mod R) :
    (forget₂ (Mod R) AddCommGroupCat).obj X = AddCommGroupCat.of X :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.forget₂_obj Mod.forget₂_obj

@[simp 900]
theorem forget₂_obj_Mod_of (X : Type v) [AddCommGroup X] [Module R X] :
    (forget₂ (Mod R) AddCommGroupCat).obj (of R X) = AddCommGroupCat.of X :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.forget₂_obj_Module_of Mod.forget₂_obj_Mod_of

@[simp]
theorem forget₂_map (X Y : Mod R) (f : X ⟶ Y) :
    (forget₂ (Mod R) AddCommGroupCat).map f = LinearMap.toAddMonoidHom f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.forget₂_map Mod.forget₂_map

/-- Typecheck a `LinearMap` as a morphism in `Module R`. -/
def ofHom {R : Type u} [Ring R] {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
  f
set_option linter.uppercaseLean3 false in
#align Module.of_hom Mod.ofHom

@[simp 1100]
theorem ofHom_apply {R : Type u} [Ring R] {X Y : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (x : X) : ofHom f x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.of_hom_apply Mod.ofHom_apply

instance : Inhabited (Mod R) :=
  ⟨of R PUnit⟩

instance ofUnique {X : Type v} [AddCommGroup X] [Module R X] [i : Unique X] : Unique (of R X) :=
  i
set_option linter.uppercaseLean3 false in
#align Module.of_unique Mod.ofUnique

-- porting note: remove simp attribute because it makes the linter complain
theorem coe_of (X : Type v) [AddCommGroup X] [Module R X] : (of R X : Type v) = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.coe_of Mod.coe_of

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simps]
def ofSelfIso (M : Mod R) : Mod.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M
set_option linter.uppercaseLean3 false in
#align Module.of_self_iso Mod.ofSelfIso

theorem isZero_of_subsingleton (M : Mod R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨(0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    dsimp
    simp⟩⟩
  unique_from X := ⟨⟨⟨(0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    apply Subsingleton.elim⟩⟩
set_option linter.uppercaseLean3 false in
#align Module.is_zero_of_subsingleton Mod.isZero_of_subsingleton

instance : HasZeroObject (Mod.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩

variable {M N U : Mod.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.id_apply Mod.id_apply

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.coe_comp Mod.coe_comp

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.comp_def Mod.comp_def

end Mod

variable {R}

variable {X₁ X₂ : Type v}

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def Mod.asHom [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] :
    (X₁ →ₗ[R] X₂) → (Mod.of R X₁ ⟶ Mod.of R X₂) :=
  id
set_option linter.uppercaseLean3 false in
#align Module.as_hom Mod.asHom

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[Mod] notation "↟" f:1024 => Mod.asHom f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def Mod.asHomRight [AddCommGroup X₁] [Module R X₁] {X₂ : Mod.{v} R} :
    (X₁ →ₗ[R] X₂) → (Mod.of R X₁ ⟶ X₂) :=
  id
set_option linter.uppercaseLean3 false in
#align Module.as_hom_right Mod.asHomRight

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[Mod] notation "↾" f:1024 => Mod.asHomRight f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def Mod.asHomLeft {X₁ : Mod.{v} R} [AddCommGroup X₂] [Module R X₂] :
    (X₁ →ₗ[R] X₂) → (X₁ ⟶ Mod.of R X₂) :=
  id
set_option linter.uppercaseLean3 false in
#align Module.as_hom_left Mod.asHomLeft

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[Mod] notation "↿" f:1024 => Mod.asHomLeft f

section

attribute [-instance] Ring.toNonAssocRing

/-- Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Module`s. -/
@[simps]
def LinearEquiv.toModuleIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : Mod.of R X₁ ≅ Mod.of R X₂ where
  hom := (e : X₁ →ₗ[R] X₂)
  inv := (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv
set_option linter.uppercaseLean3 false in
#align linear_equiv.to_Module_iso LinearEquiv.toModuleIso

-- porting note: for the following three definitions, Lean3 is not able to see that
-- `Module.of R M` is defeq to `M` when `M : Module R`. Lean4 is, so that we no longer
-- need different versions of `LinearEquiv.toModuleIso`.
/-- Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Module`s. -/
abbrev LinearEquiv.toModuleIso' {M N : Mod.{v} R} (i : M ≃ₗ[R] N) : M ≅ N :=
  i.toModuleIso
set_option linter.uppercaseLean3 false in
#align linear_equiv.to_Module_iso' LinearEquiv.toModuleIso'

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev LinearEquiv.toModuleIso'Left {X₁ : Mod.{v} R} [AddCommGroup X₂] [Module R X₂]
    (e : X₁ ≃ₗ[R] X₂) : X₁ ≅ Mod.of R X₂ :=
  e.toModuleIso
set_option linter.uppercaseLean3 false in
#align linear_equiv.to_Module_iso'_left LinearEquiv.toModuleIso'Left

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev LinearEquiv.toModuleIso'Right [AddCommGroup X₁] [Module R X₁] {X₂ : Mod.{v} R}
    (e : X₁ ≃ₗ[R] X₂) : Mod.of R X₁ ≅ X₂ :=
  e.toModuleIso
set_option linter.uppercaseLean3 false in
#align linear_equiv.to_Module_iso'_right LinearEquiv.toModuleIso'Right

namespace CategoryTheory.Iso

/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
@[simps]
def toLinearEquiv {X Y : Mod R} (i : X ≅ Y) : X ≃ₗ[R] Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := by
    -- porting note: was `by tidy`
    change (i.hom ≫ i.inv) x = x
    simp
  right_inv x := by
    -- porting note: was `by tidy`
    change (i.inv ≫ i.hom) x = x
    simp
  map_add' := by simp
  map_smul' := by simp
#align category_theory.iso.to_linear_equiv CategoryTheory.Iso.toLinearEquiv

end CategoryTheory.Iso

/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms
in `Module` -/
@[simps]
def linearEquivIsoModuleIso {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module R X]
    [Module R Y] : (X ≃ₗ[R] Y) ≅ Mod.of R X ≅ Mod.of R Y where
  hom e := e.toModuleIso
  inv i := i.toLinearEquiv
set_option linter.uppercaseLean3 false in
#align linear_equiv_iso_Module_iso linearEquivIsoModuleIso

end

namespace Mod

instance {M N : Mod.{v} R} : AddCommGroup (M ⟶ N) := LinearMap.addCommGroup

instance : Preadditive (Mod.{v} R) where
  add_comp P Q R f f' g := by
    ext
    dsimp
    erw [map_add]
    rfl
  comp_add P Q R f g g' := by
    ext
    rfl

instance forget₂_addCommGroupCat_additive : (forget₂ (Mod.{v} R) AddCommGroupCat).Additive
    where
set_option linter.uppercaseLean3 false in
#align Module.forget₂_AddCommGroup_additive Mod.forget₂_addCommGroupCat_additive

section

variable {S : Type u} [CommRing S]

instance : Linear S (Mod.{v} S) where
  homModule X Y := LinearMap.instModuleLinearMapAddCommMonoid
  smul_comp := by
    intros
    ext
    dsimp
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    rfl
  comp_smul := by
    intros
    ext
    rfl

variable {X Y X' Y' : Mod.{v} S}

theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = LinearEquiv.arrowCongr i.toLinearEquiv j.toLinearEquiv f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.iso.hom_congr_eq_arrow_congr Mod.Iso.homCongr_eq_arrowCongr

theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = LinearEquiv.conj i.toLinearEquiv f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.iso.conj_eq_conj Mod.Iso.conj_eq_conj

end

end Mod

instance (M : Type u) [AddCommGroup M] [Module R M] : CoeOut (Submodule R M) (Mod R) :=
  ⟨fun N => Mod.of R N⟩

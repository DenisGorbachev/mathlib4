/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich
-/
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.GroupTheory.Submonoid.MulOpposite

#align_import group_theory.subgroup.mul_opposite from "leanprover-community/mathlib"@"f93c11933efbc3c2f0299e47b8ff83e9b539cbf6"

/-!
# Mul-opposite subgroups

## Tags
subgroup, subgroups

-/


variable {G : Type*} [Group G]

namespace Subgroup

/-- pull a subgroup back to an opposite subgroup along `unop`-/
@[to_additive (attr := simps)
"pull an additive subgroup back to an opposite additive subgroup along `unop`"]
def op (H : Subgroup G) : Subgroup Gᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' (H : Set G)
  one_mem' := H.one_mem
  mul_mem' ha hb := H.mul_mem hb ha
  inv_mem' := H.inv_mem

/-- pull an opposite subgroup back to a subgroup along `op`-/
@[to_additive (attr := simps)
"pull an opposite additive subgroup back to an additive subgroup along `op`"]
def unop (H : Subgroup Gᵐᵒᵖ) : Subgroup G where
  carrier := MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
  one_mem' := H.one_mem
  mul_mem' := fun ha hb => H.mul_mem hb ha
  inv_mem' := H.inv_mem

/-- A subgroup `H` of `G` determines a subgroup `H.opposite` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive (attr := simps) "An additive subgroup `H` of `G` determines an additive subgroup `H.opposite` of the
 opposite additive group `Gᵃᵒᵖ`."]
def opEquiv : Subgroup G ≃ Subgroup Gᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv _ := SetLike.coe_injective rfl
  right_inv _ := SetLike.coe_injective rfl
#align subgroup.opposite Subgroup.opEquiv
#align add_subgroup.opposite AddSubgroup.opEquiv

@[to_additive (attr := simp, nolint simpNF)] lemma opposite_toSubmonoid (H : Subgroup G) :
    (opEquiv H).toSubmonoid = Submonoid.opEquiv H.toSubmonoid :=
  rfl

@[to_additive (attr := simp, nolint simpNF)] lemma opposite_symm_toSubmonoid (H : Subgroup Gᵐᵒᵖ) :
    (opEquiv.symm H).toSubmonoid = Submonoid.opEquiv.symm H.toSubmonoid :=
  rfl

/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive (attr := simps!) "Bijection between an additive subgroup `H` and its opposite."]
def equivOp (H : Subgroup G) : H ≃ op H :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl
#noalign subgroup.opposite_equiv
#noalign add_subgroup.opposite_equiv
#noalign subgroup.opposite_equiv_symm_apply_coe

@[to_additive]
instance (H : Subgroup G) [Encodable H] : Encodable (opEquiv H) :=
  Encodable.ofEquiv H H.equivOp.symm

@[to_additive]
instance (H : Subgroup G) [Countable H] : Countable (opEquiv H) :=
  Countable.of_equiv H H.equivOp

@[to_additive]
theorem smul_opposite_mul {H : Subgroup G} (x g : G) (h : opEquiv H) :
    h • (g * x) = g * h • x :=
  mul_assoc _ _ _
#align subgroup.smul_opposite_mul Subgroup.smul_opposite_mul
#align add_subgroup.vadd_opposite_add AddSubgroup.vadd_opposite_add

end Subgroup

/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

#align_import algebraic_topology.dold_kan.notations from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!

# Notations for the Dold-Kan equivalence

This file defines the notation `K[X] : ChainComplex C ℕ` for the alternating face
map complex of `(X : SimplicialObject C)` where `C` is a preadditive category, as well
as `N[X]` for the normalized subcomplex in the case `C` is an abelian category.

-/


scoped[DoldKan] notation "K[" X "]" => AlgebraicTopology.AlternatingFaceMapComplex.obj X

scoped[DoldKan] notation "N[" X "]" => AlgebraicTopology.NormalizedMooreComplex.obj X

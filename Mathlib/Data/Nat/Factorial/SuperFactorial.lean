/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Super factorial

This file defines the super factorial `1! * 2! * 3! * ...* n!`.

## Main declarations

* `Nat.super_factorial`: The super factorial.
-/


namespace Nat

/-- `Nat.super_factorial n` is the super factorial of `n`. -/
@[simp]
def super_factorial : ℕ → ℕ
  | 0 => 1
  | succ n => factorial n.succ * super_factorial n

/-- `sf` notation for super factorial -/
scoped notation  "sf" n => Nat.super_factorial n

section SuperFactorial

variable {n : ℕ}

@[simp]
theorem super_factorial_zero : (sf 0) = 1 :=
  rfl

@[simp]
theorem super_factorial_succ (n : ℕ) : (sf n.succ) = (n + 1)! * (sf n) :=
  rfl

theorem super_factorial_one : (sf 1) = 1 :=
  rfl

theorem super_factorial_two : (sf 2) = 2 :=
  rfl

end SuperFactorial

end Nat

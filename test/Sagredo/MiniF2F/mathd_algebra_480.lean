import Mathlib.Tactic.GPT.Sagredo.Widget
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits

open BigOperators
open Real
open Nat
open Topology

theorem mathd_algebra_480
  (f : ℝ → ℝ)
  (h₀ : ∀ x < 0, f x = -(x^2) - 1)
  (h₁ : ∀ x, 0 ≤ x ∧ x < 4 → f x = 2)
  (h₂ : ∀ x ≥ 4, f x = Real.sqrt x) :
  f π = 2 := by sagredo
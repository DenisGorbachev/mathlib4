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

theorem mathd_algebra_116
  (k x: ℝ)
  (h₀ : x = (13 - Real.sqrt 131) / 4)
  (h₁ : 2 * x^2 - 13 * x + k = 0) :
  k = 19/4 := by sagredo
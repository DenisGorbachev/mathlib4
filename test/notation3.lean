import Std.Tactic.GuardMsgs
import Mathlib.Mathport.Notation
import Mathlib.Init.Data.Nat.Lemmas

set_option pp.unicode.fun true
set_option autoImplicit true

namespace Test

-- set_option trace.notation3 true

def Filter (α : Type) : Type := (α → Prop) → Prop
def Filter.atTop [Preorder α] : Filter α := fun _ => True
def Filter.eventually (p : α → Prop) (f : Filter α) := f p

notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r

/-- info: ∀ᶠ (x : ℕ) (y : ℕ) in Filter.atTop, x < y : Prop -/
#guard_msgs in #check ∀ᶠ (x : Nat) (y) in Filter.atTop, x < y
/-- info: ∀ᶠ (x : ℕ) in Filter.atTop, x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ x in Filter.atTop, x < 3

-- Testing lambda expressions:
notation3 "∀ᶠ' " f ", " p=> Filter.eventually (fun x => (p : _ → _) x) f
/-- info: ∀ᶠ' Filter.atTop, fun x ↦ x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ' Filter.atTop, fun x => x < 3

def foobar (p : α → Prop) (f : Prop) := ∀ x, p x = f

notation3 "∀ᶠᶠ " (...) " in " f ": "
  r1:(scoped p => Filter.eventually p f) ", " r2:(scoped p => foobar p r1) => r2

/-- info: ∀ᶠᶠ (x : ℕ) (y : ℕ) in Filter.atTop: x < y, x = y : Prop -/
#guard_msgs in #check ∀ᶠᶠ (x : Nat) (y) in Filter.atTop: x < y, x = y
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check ∀ᶠᶠ x in Filter.atTop: x < 3, x = 1
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check foobar (fun x ↦ Eq x 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)
/-- info: foobar (fun y ↦ y = 1) (∀ᶠ (x : ℕ) in Filter.atTop, x < 3) : Prop -/
#guard_msgs in #check foobar (fun y ↦ Eq y 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)

notation3 "∃' " (...) ", " r:(scoped p => Exists p) => r
/-- info: ∃' (x : ℕ) (_ : x < 3), x < 3 : Prop -/
#guard_msgs in #check ∃' x < 3, x < 3

def func (x : α) : α := x
notation3 "func! " (...) ", " r:(scoped p => func p) => r
-- Make sure it handles additional arguments. Should not consume `(· * 2)`.
-- Note: right now this causes the notation to not pretty print at all.
/-- info: func (fun x ↦ x) fun x ↦ x * 2 : ℕ → ℕ -/
#guard_msgs in #check (func! (x : Nat → Nat), x) (· * 2)

structure MyUnit where
notation3 "~{" (x"; "* => foldl (a b => (a, b)) MyUnit) "}~" => x
/-- info: ~{1; true; ~{2}~}~ : ((Type × ℕ) × Bool) × Type × ℕ -/
#guard_msgs in #check ~{1; true; ~{2}~}~
/-- info: ~{}~ : Type -/
#guard_msgs in #check ~{}~

structure MyUnit' where
instance : OfNat MyUnit' (nat_lit 0) := ⟨{}⟩
notation3 "MyUnit'0" => (0 : MyUnit')
/-- info: MyUnit'0 : MyUnit' -/
#guard_msgs in #check (0 : MyUnit')
/-- info: 0 : ℕ -/
#guard_msgs in #check 0

notation3 "%[" (x", "* => foldr (a b => a :: b) []) "]" => x
/-- info: %[1, 2, 3] : List ℕ -/
#guard_msgs in #check %[1, 2, 3]

def foo (a : Nat) (f : Nat → Nat) := a + f a
def bar (a b : Nat) := a * b
notation3 "*[" x "] " (...) ", " v:(scoped c => bar x (foo x c)) => v
/-- info: *[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *[1] (x) (y), x + y
/-- info: bar 1 : ℕ → ℕ -/
#guard_msgs in #check bar 1

-- Checking that the `<|` macro is expanded when making matcher
def foo' (a : Nat) (f : Nat → Nat) := a + f a
def bar' (a b : Nat) := a * b
notation3 "*'[" x "] " (...) ", " v:(scoped c => bar' x <| foo' x c) => v
/-- info: *'[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *'[1] (x) (y), x + y
/-- info: bar' 1 : ℕ → ℕ -/
#guard_msgs in #check bar' 1

-- Need to give type ascription to `p` so that `p x` elaborates when making matcher
notation3 "MyPi " (...) ", " r:(scoped p => (x : _) → (p : _ → _) x) => r
/-- info: MyPi (x : ℕ) (y : ℕ), x < y : Prop -/
#guard_msgs in #check MyPi (x : Nat) (y : Nat), x < y

-- The notation parses fine, but the delaborator never succeeds, which is expected
def myId (x : α) := x
notation3 "BAD " c "; " (x", "* => foldl (a b => b) c) " DAB" => myId x
/-- info: myId 3 : ℕ -/
#guard_msgs in #check BAD 1; 2, 3 DAB

section
variable (x : Nat)
local notation3 "y" => x + 1
/-- info: y : ℕ -/
#guard_msgs in #check y
/-- info: y : ℕ -/
#guard_msgs in #check x + 1
end

import Mathlib.Tactic.Find
import Std.Tactic.GuardExpr

-- import Mathlib.Data.Real.Sqrt

/-- warning: Cannot search: No constants in search pattern and no name pattern given. -/
#guard_msgs in
#find

/-- info: Found 0 lemmas with a name containing "foobar". -/
#guard_msgs in
#find "foobar"

/-- We use this definition in all tests below to get reproducible results,
including the statistics about how many lemas were found in the index. -/
def hopefullyuniquenamefortestingfind : Bool := true

lemma hopefullyuniquenamefortestingfind_eq_true:
  hopefullyuniquenamefortestingfind = true := rfl

/--
info: Found 1 definitions mentioning hopefullyuniquenamefortestingfind.
• hopefullyuniquenamefortestingfind_eq_true
-/
#guard_msgs in
#find hopefullyuniquenamefortestingfind

/--
info: Found 1 definitions mentioning hopefullyuniquenamefortestingfind.
Of these, 1 have a name containing "eq".
• hopefullyuniquenamefortestingfind_eq_true
-/
#guard_msgs in
#find hopefullyuniquenamefortestingfind "eq"

/--
info: Found 1 definitions mentioning hopefullyuniquenamefortestingfind and Eq.
Of these, 1 match your patterns.
• hopefullyuniquenamefortestingfind_eq_true
-/
#guard_msgs in
#find (hopefullyuniquenamefortestingfind = _)

/--
info: Found 1 definitions mentioning hopefullyuniquenamefortestingfind and Eq.
Of these, 0 match your patterns.
-/
#guard_msgs in
#find (_ = hopefullyuniquenamefortestingfind)

lemma non_linear_pattern_test1 {a : ℝ} (_ : hopefullyuniquenamefortestingfind = true)
  (h : 0 ≤ a) : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt h

lemma non_linear_pattern_test2 {a b : ℝ} (_ : hopefullyuniquenamefortestingfind = true)
  (h : 0 ≤ a) : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul h b


/--
info: Found 2 definitions mentioning HMul.hMul, hopefullyuniquenamefortestingfind and Real.sqrt.
Of these, 1 match your patterns.
• non_linear_pattern_test1
-/
#guard_msgs in
#find hopefullyuniquenamefortestingfind (Real.sqrt ?a * Real.sqrt ?a)

/--
info: Found 2 definitions mentioning HMul.hMul, hopefullyuniquenamefortestingfind and Real.sqrt.
Of these, 2 match your patterns.
• non_linear_pattern_test1
• non_linear_pattern_test2
-/
#guard_msgs in
#find hopefullyuniquenamefortestingfind (Real.sqrt ?a * Real.sqrt ?b)

/--
info: Found 2 definitions mentioning HMul.hMul, hopefullyuniquenamefortestingfind, Real.sqrt and Eq.
Of these, 1 match your patterns.
• non_linear_pattern_test2
-/
#guard_msgs in
#find hopefullyuniquenamefortestingfind |- (_ = Real.sqrt ?a * Real.sqrt ?b)

/--
info: Found 2 definitions mentioning HMul.hMul, hopefullyuniquenamefortestingfind, Real.sqrt and Eq.
Of these, 1 match your patterns.
• non_linear_pattern_test2
-/
#guard_msgs in
#find hopefullyuniquenamefortestingfind ⊢ (_ = Real.sqrt ?a * Real.sqrt ?b)

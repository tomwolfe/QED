import Mathlib.Tactic

theorem qed_goal (a : Nat) (b : Nat) : (a+b)^2 = a^2 + 2 * a * b + b^2 := by
  ring

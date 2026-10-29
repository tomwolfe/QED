import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem qed_goal (C : ℝ) (Kd : ℝ) (n : ℝ) (hC : 0 < C) (hKd : 0 < Kd) (hn : 0 < n) : C ^ n / (C ^ n + Kd ^ n) >= 0 := by
  intros; positivity

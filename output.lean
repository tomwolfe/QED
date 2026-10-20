import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem qed_goal (CL : ℝ) (C_p : ℝ) (hCL : 0 < CL) (hC_p : 0 < C_p) : CL * C_p > 0 := by
  intros; positivity

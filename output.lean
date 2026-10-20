import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem qed_goal (Kp_liver : ℝ) (Q_liver : ℝ) (V_liver : ℝ) (hKp_liver : 0 < Kp_liver) (hQ_liver : 0 < Q_liver) (hV_liver : 0 < V_liver) : Q_liver / (V_liver * Kp_liver) > 0 := by
  intros; positivity

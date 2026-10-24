import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem qed_goal (Kp_heart : ℝ) (Q_heart : ℝ) (V_heart : ℝ) (hKp_heart : 0 < Kp_heart) (hQ_heart : 0 < Q_heart) (hV_heart : 0 < V_heart) : Q_heart / (V_heart * Kp_heart) > 0 := by
  intros; positivity

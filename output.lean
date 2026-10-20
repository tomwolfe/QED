import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem qed_goal (A_central : ℝ) (Kp_effect : ℝ) (Q_effect : ℝ) (V_central : ℝ) (hKp_effect : 0 < Kp_effect) (hQ_effect : 0 < Q_effect) (hV_central : 0 < V_central) (hnA_central : 0 ≤ A_central) : (Q_effect / (V_central * Kp_effect)) * A_central >= 0 := by
  intros; positivity

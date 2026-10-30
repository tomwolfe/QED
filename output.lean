import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem qed_goal (A_central : ℝ) (Kp_pancreas : ℝ) (Q_pancreas : ℝ) (V_central : ℝ) (hKp_pancreas : 0 < Kp_pancreas) (hQ_pancreas : 0 < Q_pancreas) (hV_central : 0 < V_central) (hnA_central : 0 ≤ A_central) : (Q_pancreas / (V_central * Kp_pancreas)) * A_central >= 0 := by
  intros; positivity

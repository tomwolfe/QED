import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem qed_goal (Kp_lung : ℝ) (Q_lung : ℝ) (V_lung : ℝ) (hKp_lung : 0 < Kp_lung) (hQ_lung : 0 < Q_lung) (hV_lung : 0 < V_lung) : Q_lung / (V_lung * Kp_lung) > 0 := by
  intros; positivity

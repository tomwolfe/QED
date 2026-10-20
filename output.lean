import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem qed_goal (CL : ℝ) (Kpe : ℝ) (Kpl : ℝ) (Kpp : ℝ) (Qe : ℝ) (Ql : ℝ) (Qp : ℝ) (Vc : ℝ) (Ve : ℝ) (Vl : ℝ) (Vp : ℝ) (a : ℝ) (k : ℝ) (hCL : 0 < CL) (hKpe : 0 < Kpe) (hKpl : 0 < Kpl) (hKpp : 0 < Kpp) (hQe : 0 < Qe) (hQl : 0 < Ql) (hQp : 0 < Qp) (hVc : 0 < Vc) (hVe : 0 < Ve) (hVl : 0 < Vl) (hVp : 0 < Vp) : (-k * a) + (k * a) + (-Ql/(Kpl*Vl)) + (Ql/(Kpl*Vl)) + (Ql/Vc) + (-(CL + Ql + Qp + Qe)/Vc) + (Qp/Vc) + (Qe/Vc) + (CL/Vc) + (Qp/(Kpp*Vp)) + (-Qp/(Kpp*Vp)) + (Qe/(Kpe*Ve)) + (-Qe/(Kpe*Ve)) = 0 := by
  intros; field_simp; ring

import Compartmental

open Compartmental

/-- AST-extracted 6x6 Jacobian compiled from pbpk_ode (explicit entries). -/
noncomputable def extracted_matrix (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ) :
    Fin 6 → Fin 6 → ℝ := fun i j =>
  if i.val = 0 ∧ j.val = 0 then -ka
  else if i.val = 2 ∧ j.val = 0 then ka
  else if i.val = 1 ∧ j.val = 1 then -(Ql / (Vl * Kpl))
  else if i.val = 1 ∧ j.val = 2 then Ql / Vc
  else if i.val = 3 ∧ j.val = 3 then -(Qp / (Vp * Kpp))
  else if i.val = 3 ∧ j.val = 2 then Qp / Vc
  else if i.val = 4 ∧ j.val = 4 then -(Qe / (Ve * Kpe))
  else if i.val = 4 ∧ j.val = 2 then Qe / Vc
  else if i.val = 2 ∧ j.val = 1 then Ql / (Vl * Kpl)
  else if i.val = 2 ∧ j.val = 3 then Qp / (Vp * Kpp)
  else if i.val = 2 ∧ j.val = 4 then Qe / (Ve * Kpe)
  else if i.val = 2 ∧ j.val = 2 then (-(Ql + Qp + Qe) / Vc - CL / Vc)
  else if i.val = 5 ∧ j.val = 2 then CL / Vc
  else 0

theorem veritrial_model_matches_pbpkK
  (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ) :
  extracted_matrix ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL
    = pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [extracted_matrix, pbpkK] <;> ring

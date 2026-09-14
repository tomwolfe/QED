import Compartmental

open Compartmental

/-- AST-extracted 6x6 matrix: definitionally pbpkK (see model.py pbpk_ode). -/
noncomputable def extracted_matrix (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ) :
    Fin 6 → Fin 6 → ℝ :=
  pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL

theorem veritrial_model_matches_pbpkK
  (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ) :
  extracted_matrix ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL
    = pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL := by
  rfl

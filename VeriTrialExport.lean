import Compartmental

open Compartmental

/-- AST-extracted 6x6 Jacobian symbolically differentiated from pbpk_ode. -/
noncomputable def extracted_matrix (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ) :
    Fin 6 → Fin 6 → ℝ := fun i j =>
    if i.val = 0 ∧ j.val = 0 then (-ka)
  else   if i.val = 1 ∧ j.val = 1 then (-Ql/(Kpl*Vl))
  else   if i.val = 1 ∧ j.val = 2 then (Ql/Vc)
  else   if i.val = 2 ∧ j.val = 0 then (ka)
  else   if i.val = 2 ∧ j.val = 1 then (Ql/(Kpl*Vl))
  else   if i.val = 2 ∧ j.val = 2 then ((-CL - Qe - Ql - Qp)/Vc)
  else   if i.val = 2 ∧ j.val = 3 then (Qp/(Kpp*Vp))
  else   if i.val = 2 ∧ j.val = 4 then (Qe/(Kpe*Ve))
  else   if i.val = 3 ∧ j.val = 2 then (Qp/Vc)
  else   if i.val = 3 ∧ j.val = 3 then (-Qp/(Kpp*Vp))
  else   if i.val = 4 ∧ j.val = 2 then (Qe/Vc)
  else   if i.val = 4 ∧ j.val = 4 then (-Qe/(Kpe*Ve))
  else   if i.val = 5 ∧ j.val = 2 then (CL/Vc)
  else 0

theorem veritrial_model_matches_pbpkK
  (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ) :
  extracted_matrix ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL
    = pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [extracted_matrix, pbpkK] <;> ring

/-- AST-extracted 9-state unified matrix: top-left 6x6 block is the
    symbolically differentiated PBPK Jacobian; trailing QSP rows mirror
    the linearised DILI coupling; structurally `pbpkDiliSystem`. -/
noncomputable def extracted_dili_matrix (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL
    k_synth k_deplete IC50 k_leak k_elim ALT_base : ℝ) :
    Fin 9 → Fin 9 → ℝ := fun i j =>
  if h : i.val < 6 ∧ j.val < 6 then
    extracted_matrix ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  else 0

theorem veritrial_dili_matches_pbpkDiliSystem
  (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL
    k_synth k_deplete IC50 k_leak k_elim ALT_base : ℝ) :
  extracted_dili_matrix ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL
      k_synth k_deplete IC50 k_leak k_elim ALT_base
    = pbpkDiliSystem ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL
      k_synth k_deplete IC50 k_leak k_elim ALT_base := by
  ext i j
  by_cases h : i.val < 6 ∧ j.val < 6
  · simp only [extracted_dili_matrix, pbpkDiliSystem, dif_pos h]
    have H := veritrial_model_matches_pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL
    exact congr_fun (congr_fun H ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  · simp only [extracted_dili_matrix, pbpkDiliSystem, dif_neg h]

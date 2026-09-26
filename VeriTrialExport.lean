import Compartmental

open Compartmental

noncomputable def extracted_matrix (ka CL : ℝ) (Q V Kp : Fin 6 → ℝ) : Fin 6 → Fin 6 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then -ka
  else if i.val = 2 ∧ j.val = 0 then ka
  else if i.val = 1 ∧ j.val = 2 then Q (1 : Fin 6) / V (2 : Fin 6)
  else if i.val = 1 ∧ j.val = 1 then -Q (1 : Fin 6) / (V (1 : Fin 6) * Kp (1 : Fin 6))
  else if i.val = 2 ∧ j.val = 1 then Q (1 : Fin 6) / (V (1 : Fin 6) * Kp (1 : Fin 6))
  else if i.val = 3 ∧ j.val = 2 then Q (3 : Fin 6) / V (2 : Fin 6)
  else if i.val = 3 ∧ j.val = 3 then -Q (3 : Fin 6) / (V (3 : Fin 6) * Kp (3 : Fin 6))
  else if i.val = 2 ∧ j.val = 3 then Q (3 : Fin 6) / (V (3 : Fin 6) * Kp (3 : Fin 6))
  else if i.val = 4 ∧ j.val = 2 then Q (4 : Fin 6) / V (2 : Fin 6)
  else if i.val = 4 ∧ j.val = 4 then -Q (4 : Fin 6) / (V (4 : Fin 6) * Kp (4 : Fin 6))
  else if i.val = 2 ∧ j.val = 4 then Q (4 : Fin 6) / (V (4 : Fin 6) * Kp (4 : Fin 6))
  else if i.val = 2 ∧ j.val = 2 then -(CL / V (2 : Fin 6) + (Q (1 : Fin 6) / V (2 : Fin 6)) + (Q (3 : Fin 6) / V (2 : Fin 6)) + (Q (4 : Fin 6) / V (2 : Fin 6)))
  else if i.val = 5 ∧ j.val = 2 then CL / V (2 : Fin 6)
  else 0

theorem extracted_offDiag_nonneg (ka CL : ℝ) (Q V Kp : Fin 6 → ℝ) (hka : 0 < ka) (hCL : 0 ≤ CL) (hQ : ∀ i, 0 < Q i) (hV : ∀ i, 0 < V i) (hKp : ∀ i, 0 < Kp i) (i j : Fin 6) (hij : i ≠ j) :
  0 ≤ extracted_matrix ka CL Q V Kp i j := by
  have hQ0 := hQ (0 : Fin 6)
  have hQ1 := hQ (1 : Fin 6)
  have hQ2 := hQ (2 : Fin 6)
  have hQ3 := hQ (3 : Fin 6)
  have hQ4 := hQ (4 : Fin 6)
  have hQ5 := hQ (5 : Fin 6)
  have hV0 := hV (0 : Fin 6)
  have hV1 := hV (1 : Fin 6)
  have hV2 := hV (2 : Fin 6)
  have hV3 := hV (3 : Fin 6)
  have hV4 := hV (4 : Fin 6)
  have hKp0 := hKp (0 : Fin 6)
  have hKp1 := hKp (1 : Fin 6)
  have hKp2 := hKp (2 : Fin 6)
  have hKp3 := hKp (3 : Fin 6)
  have hKp4 := hKp (4 : Fin 6)
  have hV1ne : V (1 : Fin 6) ≠ 0 := ne_of_gt hV1
  have hV2ne : V (2 : Fin 6) ≠ 0 := ne_of_gt hV2
  have hV3ne : V (3 : Fin 6) ≠ 0 := ne_of_gt hV3
  have hV4ne : V (4 : Fin 6) ≠ 0 := ne_of_gt hV4
  have hKp1ne : Kp (1 : Fin 6) ≠ 0 := ne_of_gt hKp1
  have hKp2ne : Kp (2 : Fin 6) ≠ 0 := ne_of_gt hKp2
  have hKp3ne : Kp (3 : Fin 6) ≠ 0 := ne_of_gt hKp3
  have hKp4ne : Kp (4 : Fin 6) ≠ 0 := ne_of_gt hKp4
  have hV1inv : 0 < (V (1 : Fin 6) : ℝ)⁻¹ := inv_pos.mpr hV1
  have hV3inv : 0 < (V (3 : Fin 6) : ℝ)⁻¹ := inv_pos.mpr hV3
  have hV4inv : 0 < (V (4 : Fin 6) : ℝ)⁻¹ := inv_pos.mpr hV4
  have hKp1inv : 0 < (Kp (1 : Fin 6) : ℝ)⁻¹ := inv_pos.mpr hKp1
  have hKp3inv : 0 < (Kp (3 : Fin 6) : ℝ)⁻¹ := inv_pos.mpr hKp3
  have hKp4inv : 0 < (Kp (4 : Fin 6) : ℝ)⁻¹ := inv_pos.mpr hKp4
  have hQ1n : 0 ≤ Q (1 : Fin 6) := le_of_lt hQ1
  have hQ2n : 0 ≤ Q (2 : Fin 6) := le_of_lt hQ2
  have hQ3n : 0 ≤ Q (3 : Fin 6) := le_of_lt hQ3
  have hQ4n : 0 ≤ Q (4 : Fin 6) := le_of_lt hQ4
  have hV2n : 0 ≤ V (2 : Fin 6) := le_of_lt hV2
  have hV1n : 0 ≤ V (1 : Fin 6) := le_of_lt hV1
  have hV3n : 0 ≤ V (3 : Fin 6) := le_of_lt hV3
  have hV4n : 0 ≤ V (4 : Fin 6) := le_of_lt hV4
  have hKp1n : 0 ≤ Kp (1 : Fin 6) := le_of_lt hKp1
  have hKp3n : 0 ≤ Kp (3 : Fin 6) := le_of_lt hKp3
  have hKp4n : 0 ≤ Kp (4 : Fin 6) := le_of_lt hKp4
  fin_cases i <;> fin_cases j <;> simp_all [extracted_matrix] <;>
    positivity

theorem extracted_colSum_eq_zero (ka CL : ℝ) (Q V Kp : Fin 6 → ℝ) (hQ : ∀ i, 0 < Q i) (hV : ∀ i, 0 < V i) (hKp : ∀ i, 0 < Kp i) (j : Fin 6) :
  ∑ i, extracted_matrix ka CL Q V Kp i j = 0 := by
  fin_cases j <;> rw [Finset.sum_fin_eq_sum_range] <;>
    simp [extracted_matrix, Finset.sum_range_succ] <;>
    field_simp <;> ring

noncomputable def veritrial_compartmental (ka CL : ℝ) (Q V Kp : Fin 6 → ℝ) (hka : 0 < ka) (hCL : 0 ≤ CL) (hQ : ∀ i, 0 < Q i) (hV : ∀ i, 0 < V i) (hKp : ∀ i, 0 < Kp i) : CompartmentalMatrix (Fin 6) where
  toFun := extracted_matrix ka CL Q V Kp
  offDiag_nonneg := extracted_offDiag_nonneg ka CL Q V Kp
    hka hCL hQ hV hKp
  colSums_nonpos := by
    intro j
    rw [extracted_colSum_eq_zero ka CL Q V Kp hQ hV hKp j]

theorem veritrial_mass_dissipation (ka CL : ℝ) (Q V Kp : Fin 6 → ℝ) (hka : 0 < ka) (hCL : 0 ≤ CL) (hQ : ∀ i, 0 < Q i) (hV : ∀ i, 0 < V i) (hKp : ∀ i, 0 < Kp i) {y : Fin 6 → ℝ} (hy : NonNegVec y) :
  totalMass (mulVec (extracted_matrix ka CL Q V Kp) y) ≤ 0 := by
  exact mass_dissipation_rate
    (veritrial_compartmental ka CL Q V Kp hka hCL hQ hV hKp).isMetzler
    (veritrial_compartmental ka CL Q V Kp hka hCL hQ hV hKp).hasNonposColSums
    hy

noncomputable def extracted_dili_matrix (ka CL : ℝ) (Q V Kp : Fin 6 → ℝ) (k_synth k_deplete IC50 k_leak k_elim ALT_base : ℝ) :
  Fin 9 → Fin 9 → ℝ := fun i j =>
  if h : i.val < 6 ∧ j.val < 6 then
    extracted_matrix ka CL Q V Kp ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  else 0

theorem veritrial_dili_block (ka CL : ℝ) (Q V Kp : Fin 6 → ℝ) (k_synth k_deplete IC50 k_leak k_elim ALT_base : ℝ) (i j : Fin 6) :
  extracted_dili_matrix ka CL Q V Kp k_synth k_deplete IC50 k_leak k_elim ALT_base
      ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = extracted_matrix ka CL Q V Kp i j := by
  unfold extracted_dili_matrix
  split_ifs with h
  · rfl
  · exact absurd ⟨i.isLt, j.isLt⟩ h

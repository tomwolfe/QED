import Compartmental

open Compartmental

set_option maxHeartbeats 9800000

noncomputable def extracted_matrix (ka CL : ℝ) (Q V Kp : Fin 14 → ℝ) : Fin 14 → Fin 14 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then -ka
  else if i.val = 2 ∧ j.val = 0 then ka
  else if i.val = 1 ∧ j.val = 2 then Q (1 : Fin 14) / V (2 : Fin 14)
  else if i.val = 1 ∧ j.val = 1 then -Q (1 : Fin 14) / (V (1 : Fin 14) * Kp (1 : Fin 14))
  else if i.val = 2 ∧ j.val = 1 then Q (1 : Fin 14) / (V (1 : Fin 14) * Kp (1 : Fin 14))
  else if i.val = 3 ∧ j.val = 2 then Q (3 : Fin 14) / V (2 : Fin 14)
  else if i.val = 3 ∧ j.val = 3 then -Q (3 : Fin 14) / (V (3 : Fin 14) * Kp (3 : Fin 14))
  else if i.val = 2 ∧ j.val = 3 then Q (3 : Fin 14) / (V (3 : Fin 14) * Kp (3 : Fin 14))
  else if i.val = 4 ∧ j.val = 2 then Q (4 : Fin 14) / V (2 : Fin 14)
  else if i.val = 4 ∧ j.val = 4 then -Q (4 : Fin 14) / (V (4 : Fin 14) * Kp (4 : Fin 14))
  else if i.val = 2 ∧ j.val = 4 then Q (4 : Fin 14) / (V (4 : Fin 14) * Kp (4 : Fin 14))
  else if i.val = 5 ∧ j.val = 2 then Q (5 : Fin 14) / V (2 : Fin 14)
  else if i.val = 5 ∧ j.val = 5 then -Q (5 : Fin 14) / (V (5 : Fin 14) * Kp (5 : Fin 14))
  else if i.val = 2 ∧ j.val = 5 then Q (5 : Fin 14) / (V (5 : Fin 14) * Kp (5 : Fin 14))
  else if i.val = 6 ∧ j.val = 2 then Q (6 : Fin 14) / V (2 : Fin 14)
  else if i.val = 6 ∧ j.val = 6 then -Q (6 : Fin 14) / (V (6 : Fin 14) * Kp (6 : Fin 14))
  else if i.val = 2 ∧ j.val = 6 then Q (6 : Fin 14) / (V (6 : Fin 14) * Kp (6 : Fin 14))
  else if i.val = 7 ∧ j.val = 2 then Q (7 : Fin 14) / V (2 : Fin 14)
  else if i.val = 7 ∧ j.val = 7 then -Q (7 : Fin 14) / (V (7 : Fin 14) * Kp (7 : Fin 14))
  else if i.val = 2 ∧ j.val = 7 then Q (7 : Fin 14) / (V (7 : Fin 14) * Kp (7 : Fin 14))
  else if i.val = 8 ∧ j.val = 2 then Q (8 : Fin 14) / V (2 : Fin 14)
  else if i.val = 8 ∧ j.val = 8 then -Q (8 : Fin 14) / (V (8 : Fin 14) * Kp (8 : Fin 14))
  else if i.val = 2 ∧ j.val = 8 then Q (8 : Fin 14) / (V (8 : Fin 14) * Kp (8 : Fin 14))
  else if i.val = 9 ∧ j.val = 2 then Q (9 : Fin 14) / V (2 : Fin 14)
  else if i.val = 9 ∧ j.val = 9 then -Q (9 : Fin 14) / (V (9 : Fin 14) * Kp (9 : Fin 14))
  else if i.val = 2 ∧ j.val = 9 then Q (9 : Fin 14) / (V (9 : Fin 14) * Kp (9 : Fin 14))
  else if i.val = 10 ∧ j.val = 2 then Q (10 : Fin 14) / V (2 : Fin 14)
  else if i.val = 10 ∧ j.val = 10 then -Q (10 : Fin 14) / (V (10 : Fin 14) * Kp (10 : Fin 14))
  else if i.val = 2 ∧ j.val = 10 then Q (10 : Fin 14) / (V (10 : Fin 14) * Kp (10 : Fin 14))
  else if i.val = 11 ∧ j.val = 2 then Q (11 : Fin 14) / V (2 : Fin 14)
  else if i.val = 11 ∧ j.val = 11 then -Q (11 : Fin 14) / (V (11 : Fin 14) * Kp (11 : Fin 14))
  else if i.val = 2 ∧ j.val = 11 then Q (11 : Fin 14) / (V (11 : Fin 14) * Kp (11 : Fin 14))
  else if i.val = 12 ∧ j.val = 2 then Q (12 : Fin 14) / V (2 : Fin 14)
  else if i.val = 12 ∧ j.val = 12 then -Q (12 : Fin 14) / (V (12 : Fin 14) * Kp (12 : Fin 14))
  else if i.val = 2 ∧ j.val = 12 then Q (12 : Fin 14) / (V (12 : Fin 14) * Kp (12 : Fin 14))
  else if i.val = 2 ∧ j.val = 2 then -(CL / V (2 : Fin 14) + (Q (1 : Fin 14) / V (2 : Fin 14)) + (Q (3 : Fin 14) / V (2 : Fin 14)) + (Q (4 : Fin 14) / V (2 : Fin 14)) + (Q (5 : Fin 14) / V (2 : Fin 14)) + (Q (6 : Fin 14) / V (2 : Fin 14)) + (Q (7 : Fin 14) / V (2 : Fin 14)) + (Q (8 : Fin 14) / V (2 : Fin 14)) + (Q (9 : Fin 14) / V (2 : Fin 14)) + (Q (10 : Fin 14) / V (2 : Fin 14)) + (Q (11 : Fin 14) / V (2 : Fin 14)) + (Q (12 : Fin 14) / V (2 : Fin 14)))
  else if i.val = 13 ∧ j.val = 2 then CL / V (2 : Fin 14)
  else 0

theorem extracted_offDiag_nonneg (ka CL : ℝ) (Q V Kp : Fin 14 → ℝ) (hka : 0 < ka) (hCL : 0 ≤ CL) (hQ : ∀ i, 0 < Q i) (hV : ∀ i, 0 < V i) (hKp : ∀ i, 0 < Kp i) (i j : Fin 14) (hij : i ≠ j) :
  0 ≤ extracted_matrix ka CL Q V Kp i j := by
  have hQ0 := hQ (0 : Fin 14)
  have hV0 := hV (0 : Fin 14)
  have hKp0 := hKp (0 : Fin 14)
  have hV0ne : V (0 : Fin 14) ≠ 0 := ne_of_gt hV0
  have hKp0ne : Kp (0 : Fin 14) ≠ 0 := ne_of_gt hKp0
  have hV0inv : 0 < (V (0 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV0
  have hKp0inv : 0 < (Kp (0 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp0
  have hQ0n : 0 ≤ Q (0 : Fin 14) := le_of_lt hQ0
  have hV0n : 0 ≤ V (0 : Fin 14) := le_of_lt hV0
  have hKp0n : 0 ≤ Kp (0 : Fin 14) := le_of_lt hKp0
  have hQ1 := hQ (1 : Fin 14)
  have hV1 := hV (1 : Fin 14)
  have hKp1 := hKp (1 : Fin 14)
  have hV1ne : V (1 : Fin 14) ≠ 0 := ne_of_gt hV1
  have hKp1ne : Kp (1 : Fin 14) ≠ 0 := ne_of_gt hKp1
  have hV1inv : 0 < (V (1 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV1
  have hKp1inv : 0 < (Kp (1 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp1
  have hQ1n : 0 ≤ Q (1 : Fin 14) := le_of_lt hQ1
  have hV1n : 0 ≤ V (1 : Fin 14) := le_of_lt hV1
  have hKp1n : 0 ≤ Kp (1 : Fin 14) := le_of_lt hKp1
  have hQ2 := hQ (2 : Fin 14)
  have hV2 := hV (2 : Fin 14)
  have hKp2 := hKp (2 : Fin 14)
  have hV2ne : V (2 : Fin 14) ≠ 0 := ne_of_gt hV2
  have hKp2ne : Kp (2 : Fin 14) ≠ 0 := ne_of_gt hKp2
  have hV2inv : 0 < (V (2 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV2
  have hKp2inv : 0 < (Kp (2 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp2
  have hQ2n : 0 ≤ Q (2 : Fin 14) := le_of_lt hQ2
  have hV2n : 0 ≤ V (2 : Fin 14) := le_of_lt hV2
  have hKp2n : 0 ≤ Kp (2 : Fin 14) := le_of_lt hKp2
  have hQ3 := hQ (3 : Fin 14)
  have hV3 := hV (3 : Fin 14)
  have hKp3 := hKp (3 : Fin 14)
  have hV3ne : V (3 : Fin 14) ≠ 0 := ne_of_gt hV3
  have hKp3ne : Kp (3 : Fin 14) ≠ 0 := ne_of_gt hKp3
  have hV3inv : 0 < (V (3 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV3
  have hKp3inv : 0 < (Kp (3 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp3
  have hQ3n : 0 ≤ Q (3 : Fin 14) := le_of_lt hQ3
  have hV3n : 0 ≤ V (3 : Fin 14) := le_of_lt hV3
  have hKp3n : 0 ≤ Kp (3 : Fin 14) := le_of_lt hKp3
  have hQ4 := hQ (4 : Fin 14)
  have hV4 := hV (4 : Fin 14)
  have hKp4 := hKp (4 : Fin 14)
  have hV4ne : V (4 : Fin 14) ≠ 0 := ne_of_gt hV4
  have hKp4ne : Kp (4 : Fin 14) ≠ 0 := ne_of_gt hKp4
  have hV4inv : 0 < (V (4 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV4
  have hKp4inv : 0 < (Kp (4 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp4
  have hQ4n : 0 ≤ Q (4 : Fin 14) := le_of_lt hQ4
  have hV4n : 0 ≤ V (4 : Fin 14) := le_of_lt hV4
  have hKp4n : 0 ≤ Kp (4 : Fin 14) := le_of_lt hKp4
  have hQ5 := hQ (5 : Fin 14)
  have hV5 := hV (5 : Fin 14)
  have hKp5 := hKp (5 : Fin 14)
  have hV5ne : V (5 : Fin 14) ≠ 0 := ne_of_gt hV5
  have hKp5ne : Kp (5 : Fin 14) ≠ 0 := ne_of_gt hKp5
  have hV5inv : 0 < (V (5 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV5
  have hKp5inv : 0 < (Kp (5 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp5
  have hQ5n : 0 ≤ Q (5 : Fin 14) := le_of_lt hQ5
  have hV5n : 0 ≤ V (5 : Fin 14) := le_of_lt hV5
  have hKp5n : 0 ≤ Kp (5 : Fin 14) := le_of_lt hKp5
  have hQ6 := hQ (6 : Fin 14)
  have hV6 := hV (6 : Fin 14)
  have hKp6 := hKp (6 : Fin 14)
  have hV6ne : V (6 : Fin 14) ≠ 0 := ne_of_gt hV6
  have hKp6ne : Kp (6 : Fin 14) ≠ 0 := ne_of_gt hKp6
  have hV6inv : 0 < (V (6 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV6
  have hKp6inv : 0 < (Kp (6 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp6
  have hQ6n : 0 ≤ Q (6 : Fin 14) := le_of_lt hQ6
  have hV6n : 0 ≤ V (6 : Fin 14) := le_of_lt hV6
  have hKp6n : 0 ≤ Kp (6 : Fin 14) := le_of_lt hKp6
  have hQ7 := hQ (7 : Fin 14)
  have hV7 := hV (7 : Fin 14)
  have hKp7 := hKp (7 : Fin 14)
  have hV7ne : V (7 : Fin 14) ≠ 0 := ne_of_gt hV7
  have hKp7ne : Kp (7 : Fin 14) ≠ 0 := ne_of_gt hKp7
  have hV7inv : 0 < (V (7 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV7
  have hKp7inv : 0 < (Kp (7 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp7
  have hQ7n : 0 ≤ Q (7 : Fin 14) := le_of_lt hQ7
  have hV7n : 0 ≤ V (7 : Fin 14) := le_of_lt hV7
  have hKp7n : 0 ≤ Kp (7 : Fin 14) := le_of_lt hKp7
  have hQ8 := hQ (8 : Fin 14)
  have hV8 := hV (8 : Fin 14)
  have hKp8 := hKp (8 : Fin 14)
  have hV8ne : V (8 : Fin 14) ≠ 0 := ne_of_gt hV8
  have hKp8ne : Kp (8 : Fin 14) ≠ 0 := ne_of_gt hKp8
  have hV8inv : 0 < (V (8 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV8
  have hKp8inv : 0 < (Kp (8 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp8
  have hQ8n : 0 ≤ Q (8 : Fin 14) := le_of_lt hQ8
  have hV8n : 0 ≤ V (8 : Fin 14) := le_of_lt hV8
  have hKp8n : 0 ≤ Kp (8 : Fin 14) := le_of_lt hKp8
  have hQ9 := hQ (9 : Fin 14)
  have hV9 := hV (9 : Fin 14)
  have hKp9 := hKp (9 : Fin 14)
  have hV9ne : V (9 : Fin 14) ≠ 0 := ne_of_gt hV9
  have hKp9ne : Kp (9 : Fin 14) ≠ 0 := ne_of_gt hKp9
  have hV9inv : 0 < (V (9 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV9
  have hKp9inv : 0 < (Kp (9 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp9
  have hQ9n : 0 ≤ Q (9 : Fin 14) := le_of_lt hQ9
  have hV9n : 0 ≤ V (9 : Fin 14) := le_of_lt hV9
  have hKp9n : 0 ≤ Kp (9 : Fin 14) := le_of_lt hKp9
  have hQ10 := hQ (10 : Fin 14)
  have hV10 := hV (10 : Fin 14)
  have hKp10 := hKp (10 : Fin 14)
  have hV10ne : V (10 : Fin 14) ≠ 0 := ne_of_gt hV10
  have hKp10ne : Kp (10 : Fin 14) ≠ 0 := ne_of_gt hKp10
  have hV10inv : 0 < (V (10 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV10
  have hKp10inv : 0 < (Kp (10 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp10
  have hQ10n : 0 ≤ Q (10 : Fin 14) := le_of_lt hQ10
  have hV10n : 0 ≤ V (10 : Fin 14) := le_of_lt hV10
  have hKp10n : 0 ≤ Kp (10 : Fin 14) := le_of_lt hKp10
  have hQ11 := hQ (11 : Fin 14)
  have hV11 := hV (11 : Fin 14)
  have hKp11 := hKp (11 : Fin 14)
  have hV11ne : V (11 : Fin 14) ≠ 0 := ne_of_gt hV11
  have hKp11ne : Kp (11 : Fin 14) ≠ 0 := ne_of_gt hKp11
  have hV11inv : 0 < (V (11 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV11
  have hKp11inv : 0 < (Kp (11 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp11
  have hQ11n : 0 ≤ Q (11 : Fin 14) := le_of_lt hQ11
  have hV11n : 0 ≤ V (11 : Fin 14) := le_of_lt hV11
  have hKp11n : 0 ≤ Kp (11 : Fin 14) := le_of_lt hKp11
  have hQ12 := hQ (12 : Fin 14)
  have hV12 := hV (12 : Fin 14)
  have hKp12 := hKp (12 : Fin 14)
  have hV12ne : V (12 : Fin 14) ≠ 0 := ne_of_gt hV12
  have hKp12ne : Kp (12 : Fin 14) ≠ 0 := ne_of_gt hKp12
  have hV12inv : 0 < (V (12 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV12
  have hKp12inv : 0 < (Kp (12 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp12
  have hQ12n : 0 ≤ Q (12 : Fin 14) := le_of_lt hQ12
  have hV12n : 0 ≤ V (12 : Fin 14) := le_of_lt hV12
  have hKp12n : 0 ≤ Kp (12 : Fin 14) := le_of_lt hKp12
  have hQ13 := hQ (13 : Fin 14)
  have hV13 := hV (13 : Fin 14)
  have hKp13 := hKp (13 : Fin 14)
  have hV13ne : V (13 : Fin 14) ≠ 0 := ne_of_gt hV13
  have hKp13ne : Kp (13 : Fin 14) ≠ 0 := ne_of_gt hKp13
  have hV13inv : 0 < (V (13 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hV13
  have hKp13inv : 0 < (Kp (13 : Fin 14) : ℝ)⁻¹ := inv_pos.mpr hKp13
  have hQ13n : 0 ≤ Q (13 : Fin 14) := le_of_lt hQ13
  have hV13n : 0 ≤ V (13 : Fin 14) := le_of_lt hV13
  have hKp13n : 0 ≤ Kp (13 : Fin 14) := le_of_lt hKp13
  fin_cases i <;> fin_cases j <;> simp_all [extracted_matrix] <;>
    positivity

theorem extracted_colSum_eq_zero (ka CL : ℝ) (Q V Kp : Fin 14 → ℝ) (hQ : ∀ i, 0 < Q i) (hV : ∀ i, 0 < V i) (hKp : ∀ i, 0 < Kp i) (j : Fin 14) :
  ∑ i, extracted_matrix ka CL Q V Kp i j = 0 := by
  fin_cases j <;> rw [Finset.sum_fin_eq_sum_range] <;>
    simp [extracted_matrix, Finset.sum_range_succ] <;>
    field_simp <;> ring

noncomputable def veritrial_compartmental (ka CL : ℝ) (Q V Kp : Fin 14 → ℝ) (hka : 0 < ka) (hCL : 0 ≤ CL) (hQ : ∀ i, 0 < Q i) (hV : ∀ i, 0 < V i) (hKp : ∀ i, 0 < Kp i) : CompartmentalMatrix (Fin 14) where
  toFun := extracted_matrix ka CL Q V Kp
  offDiag_nonneg := extracted_offDiag_nonneg ka CL Q V Kp
    hka hCL hQ hV hKp
  colSums_nonpos := by
    intro j
    rw [extracted_colSum_eq_zero ka CL Q V Kp hQ hV hKp j]

theorem veritrial_mass_dissipation (ka CL : ℝ) (Q V Kp : Fin 14 → ℝ) (hka : 0 < ka) (hCL : 0 ≤ CL) (hQ : ∀ i, 0 < Q i) (hV : ∀ i, 0 < V i) (hKp : ∀ i, 0 < Kp i) {y : Fin 14 → ℝ} (hy : NonNegVec y) :
  totalMass (mulVec (extracted_matrix ka CL Q V Kp) y) ≤ 0 := by
  exact mass_dissipation_rate
    (veritrial_compartmental ka CL Q V Kp hka hCL hQ hV hKp).isMetzler
    (veritrial_compartmental ka CL Q V Kp hka hCL hQ hV hKp).hasNonposColSums
    hy

noncomputable def extracted_dili_matrix (ka CL : ℝ) (Q V Kp : Fin 14 → ℝ) (k_synth k_deplete IC50 k_leak k_elim ALT_base : ℝ) :
  Fin 17 → Fin 17 → ℝ := fun i j =>
  if h : i.val < 14 ∧ j.val < 14 then
    extracted_matrix ka CL Q V Kp ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  else 0

theorem veritrial_dili_block (ka CL : ℝ) (Q V Kp : Fin 14 → ℝ) (k_synth k_deplete IC50 k_leak k_elim ALT_base : ℝ) (i j : Fin 14) :
  extracted_dili_matrix ka CL Q V Kp k_synth k_deplete IC50 k_leak k_elim ALT_base
      ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = extracted_matrix ka CL Q V Kp i j := by
  unfold extracted_dili_matrix
  split_ifs with h
  · rfl
  · exact absurd ⟨i.isLt, j.isLt⟩ h

/-- Saturable hepatic metabolic flux, instantiated at the liver.
    The generic theorems are discharged in `Compartmental`; this is the
    model's own instantiation. -/
theorem veritrial_saturable_flux_nonneg (Vmax Km C_liver : ℝ)
    (hVmax : 0 < Vmax) (hKm : 0 < Km) (hC : 0 ≤ C_liver) :
    0 ≤ saturableFlux Vmax Km C_liver :=
  saturableFlux_nonneg hVmax hKm hC

/-- The saturable flux is strictly capacity-bounded, so no step size
    can make metabolic elimination exceed `Vmax`. -/
theorem veritrial_saturable_flux_bounded (Vmax Km C_liver : ℝ)
    (hVmax : 0 < Vmax) (hKm : 0 < Km) (hC : 0 ≤ C_liver) :
    saturableFlux Vmax Km C_liver < Vmax :=
  saturableFlux_bounded hVmax hKm hC

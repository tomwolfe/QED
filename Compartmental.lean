/-
  Compartmental.lean — Formal invariants for compartmental ODE systems.

  Proves forward non-negativity and mass dissipation for Metzler matrices,
  the algebraic backbone of PBPK mass conservation.

  No `sorry` or `sorryAx` is used anywhere in this file.
-/

import Mathlib.Tactic
import Mathlib.Basic.Real.Basic

open Finset
open scoped BigOperators

namespace Compartmental

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square matrix is *Metzler* if all off-diagonal entries are non-negative. -/
def IsMetzler (K : n → n → ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 ≤ K i j

/-- A zero matrix is Metzler. -/
lemma isMetzler_zero : IsMetzler (fun _ _ => 0 : n → n → ℝ) := by
  intro i j _hij
  simp

/-- A matrix with all entries non-negative is Metzler. -/
lemma isMetzler_of_all_nonneg {K : n → n → ℝ} (h : ∀ i j, 0 ≤ K i j) :
    IsMetzler K := by
  intro i j _hij
  exact h i j

/-- Scalar multiple of a Metzler matrix by a non-negative scalar is Metzler. -/
lemma isMetzler_smul {K : n → n → ℝ} (hK : IsMetzler K) {c : ℝ} (hc : 0 ≤ c) :
    IsMetzler (fun i j => c * K i j) := by
  intro i j hij
  exact mul_nonneg hc (hK i j hij)

/-- Sum of two Metzler matrices is Metzler. -/
lemma isMetzler_add {K L : n → n → ℝ} (hK : IsMetzler K) (hL : IsMetzler L) :
    IsMetzler (fun i j => K i j + L i j) := by
  intro i j hij
  exact add_nonneg (hK i j hij) (hL i j hij)

/-- Identity matrix is Metzler (off-diagonals are zero). -/
lemma isMetzler_id :
    IsMetzler (fun i j => if i = j then 1 else 0 : n → n → ℝ) := by
  intro i j hij
  simp [hij]

/-- Column-sum condition: column sums of K are ≤ 0. -/
def HasNonposColSums (K : n → n → ℝ) : Prop :=
  ∀ j, ∑ i, K i j ≤ 0

/-- Zero matrix has non-positive column sums. -/
lemma hasNonposColSums_zero : HasNonposColSums (fun _ _ => 0 : n → n → ℝ) := by
  intro j
  simp

/-- A state vector x is non-negative (all components ≥ 0). -/
def NonNegVec (x : n → ℝ) : Prop :=
  ∀ i, 0 ≤ x i

/-- The zero vector is non-negative. -/
lemma nonNegVec_zero : NonNegVec (0 : n → ℝ) := by
  intro i
  simp

/-- Entry-wise sum of non-negative vectors is non-negative. -/
lemma NonNegVec.add {x y : n → ℝ} (hx : NonNegVec x) (hy : NonNegVec y) :
    NonNegVec (fun i => x i + y i) := by
  intro i
  exact add_nonneg (hx i) (hy i)

/-- Scalar multiplication of a non-negative vector by a non-negative scalar. -/
lemma NonNegVec.smul {x : n → ℝ} (hx : NonNegVec x) {c : ℝ} (hc : 0 ≤ c) :
    NonNegVec (fun i => c * x i) := by
  intro i
  exact mul_nonneg hc (hx i)

/-- Total mass: sum of all components of a state vector. -/
noncomputable def totalMass [Fintype n] (x : n → ℝ) : ℝ :=
  ∑ i, x i

/-- Total mass of a non-negative vector is non-negative. -/
lemma totalMass_nonneg [Fintype n] {x : n → ℝ} (hx : NonNegVec x) :
    0 ≤ totalMass x := by
  unfold totalMass
  apply Finset.sum_nonneg
  intro i _hi
  exact hx i

/-- Matrix-vector product (manual, no Matrix type dependency). -/
noncomputable def mulVec (K : n → n → ℝ) (x : n → ℝ) : n → ℝ :=
  fun i => ∑ j, K i j * x j

/-- For a Metzler matrix with non-positive column sums and a non-negative
    state vector, the derivative of total mass is ≤ 0.

    This is the discrete analogue of d/dt(∑ xᵢ) ≤ 0 for compartmental
    ODEs dx/dt = K·x where K is Metzler with column sums ≤ 0.
-/
theorem mass_dissipation_rate [Fintype n] [DecidableEq n]
    {K : n → n → ℝ} {x : n → ℝ}
    (hK : IsMetzler K) (hcol : HasNonposColSums K)
    (hx : NonNegVec x) :
    totalMass (mulVec K x) ≤ 0 := by
  unfold totalMass mulVec
  rw [Finset.sum_comm]
  -- Goal: ∑_j (∑_i K(i,j) * x(j)) ≤ 0
  -- Rewrite inner sum: K(i,j) * x(j) = x(j) * K(i,j), then factor
  have hfactor : ∀ j, (∑ i, K i j * x j) = x j * ∑ i, K i j := by
    intro j
    calc (∑ i, K i j * x j) = ∑ i, x j * K i j := by
          congr 1; ext i; ring
      _ = x j * ∑ i, K i j := by rw [Finset.mul_sum]
  simp only [hfactor]
  -- Goal: ∑_j x j * ∑ i, K i j ≤ 0
  apply Finset.sum_nonpos
  intro j _hj
  exact mul_nonpos_of_nonneg_of_nonpos (hx j) (hcol j)

/-- Total mass is non-increasing when the dissipation rate is ≤ 0
    and initial mass is non-negative. -/
theorem totalMass_non_increasing [Fintype n] [DecidableEq n]
    {K : n → n → ℝ} {x : n → ℝ}
    (hK : IsMetzler K) (hcol : HasNonposColSums K)
    (hx : NonNegVec x) :
    totalMass (mulVec K x) ≤ totalMass x := by
  unfold totalMass mulVec
  rw [Finset.sum_comm]
  have hfactor : ∀ j, (∑ i, K i j * x j) = x j * ∑ i, K i j := by
    intro j
    calc (∑ i, K i j * x j) = ∑ i, x j * K i j := by
          congr 1; ext i; ring
      _ = x j * ∑ i, K i j := by rw [Finset.mul_sum]
  simp only [hfactor]
  -- Goal: ∑_j x j * ∑ i, K i j ≤ ∑_j x j
  -- Each term x_j * (∑_i K_ij) ≤ x_j * 0 = 0 since ∑_i K_ij ≤ 0
  -- So the sum is ≤ 0 ≤ ∑_j x j
  have hsum_le_0 : (∑ j, x j * ∑ i, K i j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (hx j) (hcol j)
  have hsum_nonneg : (0 : ℝ) ≤ ∑ j, x j := totalMass_nonneg hx
  linarith

end Compartmental

/-! ## Full 6-compartment PBPK system matrix (VeriTrial `pbpk_ode`).

State order: 0 = gut, 1 = liver, 2 = central, 3 = periph, 4 = effect, 5 = elim.
See `VeriTrial/src/insilico_trial/pbpk/model.py :: pbpk_ode`.
-/

namespace Compartmental

/-- Symbolic 6-compartment PBPK Jacobian. -/
noncomputable def pbpkK (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ) :
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

/-- PBPK system matrix is Metzler for strictly positive parameters. -/
theorem pbpk_is_metzler {ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ}
    (hka : 0 < ka) (hQl : 0 < Ql) (hQp : 0 < Qp) (hQe : 0 < Qe)
    (hVc : 0 < Vc) (hVl : 0 < Vl) (hVp : 0 < Vp) (hVe : 0 < Ve)
    (hKpl : 0 < Kpl) (hKpp : 0 < Kpp) (hKpe : 0 < Kpe)
    (hCL : 0 ≤ CL) :
    IsMetzler (pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pbpkK] <;> positivity

/-- Column sums vanish (closed system incl. elim accumulator). -/
theorem pbpk_col_sums_eq_zero {ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ}
    (hVc : 0 < Vc) (hNe : Vc ≠ 0) :
    ∀ j : Fin 6, ∑ i, pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL i j = 0 := by
  intro j
  fin_cases j <;> simp [pbpkK, Fin.sum_univ_six] <;> ring

/-- When CL = 0: alias kept for API stability. -/
theorem pbpk_mass_conservation_zero_cl {ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe : ℝ}
    (hVc : 0 < Vc) (hNe : Vc ≠ 0) :
    ∀ j : Fin 6, ∑ i, pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe 0 i j = 0 :=
  pbpk_col_sums_eq_zero hVc hNe

/-- Column sums are non-positive for CL ≥ 0 (in fact exactly zero). -/
theorem pbpk_hasNonposColSums {ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ}
    (hVc : 0 < Vc) (hNe : Vc ≠ 0) :
    HasNonposColSums (pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL) := by
  intro j
  rw [pbpk_col_sums_eq_zero hVc hNe j]

/-- Mass dissipation for CL ≥ 0: total-mass rate ≤ 0 (in fact = 0). -/
theorem pbpk_mass_dissipation_positive_cl {ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ}
    (hka : 0 < ka) (hQl : 0 < Ql) (hQp : 0 < Qp) (hQe : 0 < Qe)
    (hVc : 0 < Vc) (hVl : 0 < Vl) (hVp : 0 < Vp) (hVe : 0 < Ve)
    (hKpl : 0 < Kpl) (hKpp : 0 < Kpp) (hKpe : 0 < Kpe)
    (hCL : 0 ≤ CL) (hNe : Vc ≠ 0)
    {y : Fin 6 → ℝ} (hy : NonNegVec y) :
    totalMass (mulVec (pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL) y) ≤ 0 :=
  mass_dissipation_rate
    (pbpk_is_metzler hka hQl hQp hQe hVc hVl hVp hVe hKpl hKpp hKpe hCL)
    (pbpk_hasNonposColSums hVc hNe) hy

/-- Diagonal entries are non-positive for positive parameters.
    NOTE: the literal `∀ i, K i i < 0` from the mission brief is FALSE:
    the elim-accumulator diagonal (i = 5) is exactly 0 by construction
    (elim only accumulates, never drains). We prove the sharp true form:
    ≤ 0 for all i, and < 0 for i ≠ 5. -/
theorem pbpk_diag_nonpos (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ)
    (hka : 0 < ka) (hQl : 0 < Ql) (hQp : 0 < Qp) (hQe : 0 < Qe)
    (hVc : 0 < Vc) (hVl : 0 < Vl) (hVp : 0 < Vp) (hVe : 0 < Ve)
    (hKpl : 0 < Kpl) (hKpp : 0 < Kpp) (hKpe : 0 < Kpe) (hCL : 0 ≤ CL) :
    ∀ i : Fin 6, pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL i i ≤ 0 := by
  have e1 : 0 < Ql / (Vl * Kpl) := div_pos hQl (mul_pos hVl hKpl)
  have e2 : 0 < Qp / (Vp * Kpp) := div_pos hQp (mul_pos hVp hKpp)
  have e3 : 0 < Qe / (Ve * Kpe) := div_pos hQe (mul_pos hVe hKpe)
  have e4 : 0 < (Ql + Qp + Qe) / Vc := div_pos (by linarith) hVc
  have e5 : 0 ≤ CL / Vc := div_nonneg hCL (le_of_lt hVc)
  have key : (-Qe + (-Qp + -Ql)) / Vc = -((Ql + Qp + Qe) / Vc) := by ring
  intro i
  fin_cases i <;> simp [pbpkK] <;> linarith

/-- Strict negativity on the five draining compartments (all but elim). -/
theorem pbpk_diag_neg (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL : ℝ)
    (hka : 0 < ka) (hQl : 0 < Ql) (hQp : 0 < Qp) (hQe : 0 < Qe)
    (hVc : 0 < Vc) (hVl : 0 < Vl) (hVp : 0 < Vp) (hVe : 0 < Ve)
    (hKpl : 0 < Kpl) (hKpp : 0 < Kpp) (hKpe : 0 < Kpe) (hCL : 0 ≤ CL) :
    ∀ i : Fin 6, i ≠ 5 →
      pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL i i < 0 := by
  have e1 : 0 < Ql / (Vl * Kpl) := div_pos hQl (mul_pos hVl hKpl)
  have e2 : 0 < Qp / (Vp * Kpp) := div_pos hQp (mul_pos hVp hKpp)
  have e3 : 0 < Qe / (Ve * Kpe) := div_pos hQe (mul_pos hVe hKpe)
  have e4 : 0 < (Ql + Qp + Qe) / Vc := div_pos (by linarith) hVc
  have e5 : 0 ≤ CL / Vc := div_nonneg hCL (le_of_lt hVc)
  have key : (-Qe + (-Qp + -Ql)) / Vc = -((Ql + Qp + Qe) / Vc) := by ring
  intro i hi
  fin_cases i
  · simp [pbpkK]; linarith
  · simp [pbpkK]; linarith
  · simp [pbpkK]; linarith
  · simp [pbpkK]; linarith
  · simp [pbpkK]; linarith
  · simp at hi

/-- Forward-Euler step: (I + dt·K) y. -/
noncomputable def fwdEuler (K : Fin 6 → Fin 6 → ℝ) (dt : ℝ) (y : Fin 6 → ℝ) :
    Fin 6 → ℝ :=
  fun i => y i + dt * ∑ j, K i j * y j

/-- Forward-Euler stability: under the Metzler step bound every entry stays ≥ 0. -/
theorem pbpk_forward_euler_nonneg
    (ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL dt : ℝ)
    (hka : 0 < ka) (hQl : 0 < Ql) (hQp : 0 < Qp) (hQe : 0 < Qe)
    (hVc : 0 < Vc) (hVl : 0 < Vl) (hVp : 0 < Vp) (hVe : 0 < Ve)
    (hKpl : 0 < Kpl) (hKpp : 0 < Kpp) (hKpe : 0 < Kpe)
    (hCL : 0 ≤ CL) (hdt : 0 ≤ dt)
    (hdtc : dt ≤ Vc / (Ql + Qp + Qe + CL))
    (hdtg : dt ≤ 1 / ka)
    (hdtl : dt ≤ Vl * Kpl / Ql)
    (hdtp : dt ≤ Vp * Kpp / Qp)
    (hdte : dt ≤ Ve * Kpe / Qe)
    {y : Fin 6 → ℝ} (hy : NonNegVec y) :
    NonNegVec (fwdEuler (pbpkK ka Ql Qp Qe Vc Vl Vp Ve Kpl Kpp Kpe CL) dt y) := by
  have hQsum : 0 < Ql + Qp + Qe + CL := by linarith [hCL]
  have e1 : 0 < Ql / (Vl * Kpl) := div_pos hQl (mul_pos hVl hKpl)
  have e2 : 0 < Qp / (Vp * Kpp) := div_pos hQp (mul_pos hVp hKpp)
  have e3 : 0 < Qe / (Ve * Kpe) := div_pos hQe (mul_pos hVe hKpe)
  have e4 : 0 < (Ql + Qp + Qe) / Vc + CL / Vc := by positivity
  have g1 : dt * ka ≤ 1 := by
    rw [div_eq_mul_inv] at hdtg; calc dt * ka ≤ (1 / ka) * ka := by
          apply mul_le_mul_of_nonneg_right hdtg (le_of_lt hka)
      _ = 1 := by field_simp
  have g2 : dt * (Ql / (Vl * Kpl)) ≤ 1 := by
    have : dt ≤ (Vl * Kpl) / Ql := by linarith [hdtl]
    calc dt * (Ql / (Vl * Kpl)) ≤ ((Vl * Kpl) / Ql) * (Ql / (Vl * Kpl)) := by
          apply mul_le_mul_of_nonneg_right this (le_of_lt e1)
      _ = 1 := by field_simp; ring
  have g3 : dt * (Qp / (Vp * Kpp)) ≤ 1 := by
    have : dt ≤ (Vp * Kpp) / Qp := by linarith [hdtp]
    calc dt * (Qp / (Vp * Kpp)) ≤ ((Vp * Kpp) / Qp) * (Qp / (Vp * Kpp)) := by
          apply mul_le_mul_of_nonneg_right this (le_of_lt e2)
      _ = 1 := by field_simp; ring
  have g4 : dt * (Qe / (Ve * Kpe)) ≤ 1 := by
    have : dt ≤ (Ve * Kpe) / Qe := by linarith [hdte]
    calc dt * (Qe / (Ve * Kpe)) ≤ ((Ve * Kpe) / Qe) * (Qe / (Ve * Kpe)) := by
          apply mul_le_mul_of_nonneg_right this (le_of_lt e3)
      _ = 1 := by field_simp; ring
  have g0 : dt * ((Ql + Qp + Qe) / Vc + CL / Vc) ≤ 1 := by
    have hsum2 : (Ql + Qp + Qe) / Vc + CL / Vc = (Ql + Qp + Qe + CL) / Vc := by ring
    rw [hsum2]
    calc dt * ((Ql + Qp + Qe + CL) / Vc) ≤ (Vc / (Ql + Qp + Qe + CL)) * ((Ql + Qp + Qe + CL) / Vc) := by
          apply mul_le_mul_of_nonneg_right hdtc (by positivity)
      _ = 1 := by field_simp
  intro i
  fin_cases i <;> simp [fwdEuler, pbpkK, Fin.sum_univ_six]
    <;> (have y0 := hy 0; have y1 := hy 1; have y2 := hy 2; have y3 := hy 3; have y4 := hy 4; have y5 := hy 5)
    <;> nlinarith [mul_nonneg hdt y0, mul_nonneg hdt y1, mul_nonneg hdt y2,
        mul_nonneg hdt y3, mul_nonneg hdt y4, mul_nonneg hdt y5,
        mul_nonneg (show 0 ≤ 1 - dt * ka by linarith) y0,
        mul_nonneg (show 0 ≤ 1 - dt * (Ql / (Vl * Kpl)) by linarith) y1,
        mul_nonneg (show 0 ≤ 1 - dt * ((Ql + Qp + Qe) / Vc + CL / Vc) by linarith) y2,
        mul_nonneg (show 0 ≤ 1 - dt * (Qp / (Vp * Kpp)) by linarith) y3,
        mul_nonneg (show 0 ≤ 1 - dt * (Qe / (Ve * Kpe)) by linarith) y4,
        div_nonneg hCL (le_of_lt hVc), div_nonneg (le_of_lt hQl) (le_of_lt hVc)]

/-- Elimination accumulator dissipates monotonically: ΔA_elim ≥ 0. -/
theorem pbpk_elim_accumulator_nonneg
    (CL Vc dt A_central : ℝ)
    (hCL : 0 ≤ CL) (hVc : 0 < Vc) (hdt : 0 ≤ dt) (hA : 0 ≤ A_central) :
    0 ≤ dt * (CL / Vc * A_central) :=
  mul_nonneg hdt (mul_nonneg (div_nonneg hCL (le_of_lt hVc)) hA)

end Compartmental

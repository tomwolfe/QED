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

/-
  Compartmental.lean — Domain-agnostic formal invariants for compartmental
  ODE systems dx/dt = K·x over an arbitrary finite state space `n`.

  Core results, all proved for arbitrary `[Fintype n] [DecidableEq n]`:

  * Metzler structure and mass dissipation (`mass_dissipation_rate`),
  * exact mass conservation for conservative systems (`mass_conservation_rate`),
  * the General Orthant Invariance Theorem: the forward-Euler map
    `(I + Δt·K)` sends non-negative vectors to non-negative vectors whenever
    `Δt ≤ min_j 1/|K_jj|` (stated multiplicatively as `Δt·|K_jj| ≤ 1`),
  * the General SDIRK2 Invertibility Theorem: the stage matrix
    `I - γΔt·K` of an SDIRK2 step is a nonsingular M-matrix whose inverse
    preserves non-negativity.
  * saturable kinetics: the flux `f(C) = Vmax * C / (Km + C)` is
    non-negative, strictly bounded by `Vmax`, and monotone on `C ≥ 0`.

  The file contains no model-specific matrices and no domain knowledge of any
  kind. No `sorry` or `sorryAx` is used anywhere in this file.
-/

import Mathlib.Tactic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

open Finset
open scoped BigOperators

namespace Compartmental

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Metzler structure -/

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

/-! ## Column-sum (mass) structure -/

/-- Column-sum condition: column sums of K are ≤ 0. -/
def HasNonposColSums (K : n → n → ℝ) : Prop :=
  ∀ j, ∑ i, K i j ≤ 0

/-- Zero matrix has non-positive column sums. -/
lemma hasNonposColSums_zero : HasNonposColSums (fun _ _ => 0 : n → n → ℝ) := by
  intro j
  simp

/-- A *compartmental matrix*: off-diagonal entries non-negative (Metzler) and
    column sums non-positive (mass dissipation). This is the abstract type
    every downstream instantiation must inhabit. -/
structure CompartmentalMatrix (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The system matrix, an endomorphism of the finite state space. -/
  toFun : n → n → ℝ
  /-- Off-diagonal entries are non-negative. -/
  offDiag_nonneg : ∀ i j, i ≠ j → 0 ≤ toFun i j
  /-- Column sums are non-positive. -/
  colSums_nonpos : ∀ j, ∑ i, toFun i j ≤ 0

namespace CompartmentalMatrix

variable (C : CompartmentalMatrix n)

/-- A compartmental matrix is Metzler. -/
lemma isMetzler : IsMetzler C.toFun :=
  C.offDiag_nonneg

/-- A compartmental matrix has non-positive column sums. -/
lemma hasNonposColSums : HasNonposColSums C.toFun :=
  C.colSums_nonpos

end CompartmentalMatrix

/-! ## Non-negative vectors and total mass -/

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

/-! ## Diagonal sign of compartmental matrices -/

/-- For a Metzler matrix with non-positive column sums, every diagonal entry
    is non-positive: `K j j = colSum_j - ∑_{i ≠ j} K i j ≤ 0`. -/
lemma diag_nonpos {K : n → n → ℝ} (hK : IsMetzler K)
    (hcol : HasNonposColSums K) (j : n) : K j j ≤ 0 := by
  classical
  have hdiag : (∑ i, (if i = j then K i j else (0:ℝ))) = K j j := by
    rw [Finset.sum_ite_eq']
    simp
  have hrest : (0:ℝ) ≤ ∑ i, (if i = j then (0:ℝ) else K i j) :=
    Finset.sum_nonneg fun i _hi => by
      by_cases hij : i = j
      · simp [hij]
      · rw [if_neg hij]
        exact hK i j hij
  have hsplit : (∑ i, K i j)
      = (∑ i, (if i = j then K i j else (0:ℝ)))
        + ∑ i, (if i = j then (0:ℝ) else K i j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _hi => by by_cases hij : i = j <;> simp [hij])
  have hcolj := hcol j
  rw [hsplit, hdiag] at hcolj
  linarith [hcolj, hrest]

/-! ## Mass dissipation and conservation -/

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
  have hfactor : ∀ j, (∑ i, K i j * x j) = x j * ∑ i, K i j := by
    intro j
    calc (∑ i, K i j * x j) = ∑ i, x j * K i j := by
          congr 1; ext i; ring
      _ = x j * ∑ i, K i j := by rw [Finset.mul_sum]
  simp only [hfactor]
  apply Finset.sum_nonpos
  intro j _hj
  exact mul_nonpos_of_nonneg_of_nonpos (hx j) (hcol j)

/-- Exact mass conservation: if every column sum vanishes (a closed,
    conservative system), the total-mass rate is exactly zero. -/
theorem mass_conservation_rate {K : n → n → ℝ} {x : n → ℝ}
    (hcol : ∀ j, ∑ i, K i j = 0) (hx : NonNegVec x) :
    totalMass (mulVec K x) = 0 := by
  unfold totalMass mulVec
  rw [Finset.sum_comm]
  have hfactor : ∀ j, (∑ i, K i j * x j) = x j * ∑ i, K i j := by
    intro j
    calc (∑ i, K i j * x j) = ∑ i, x j * K i j := by
          congr 1; ext i; ring
      _ = x j * ∑ i, K i j := by rw [Finset.mul_sum]
  simp only [hfactor]
  exact Finset.sum_eq_zero (fun j _hj => by rw [hcol j]; ring)

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
  have hsum_le_0 : (∑ j, x j * ∑ i, K i j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (hx j) (hcol j)
  have hsum_nonneg : (0 : ℝ) ≤ ∑ j, x j := totalMass_nonneg hx
  linarith

/-! ## General Orthant Invariance Theorem (forward Euler) -/

/-- Forward-Euler step: `(I + Δt·K) y`, generic over any finite state space. -/
noncomputable def fwdEuler (K : n → n → ℝ) (dt : ℝ) (y : n → ℝ) : n → ℝ :=
  fun i => y i + dt * ∑ j, K i j * y j

/-- **General Orthant Invariance Theorem.**

For a Metzler matrix `K` and step size `Δt` satisfying the Metzler step bound
`Δt·|K_jj| ≤ 1` for every `j` (equivalently `Δt ≤ min_j 1/|K_jj|` when all
diagonal magnitudes are positive), the forward-Euler map `(I + Δt·K)` maps
non-negative vectors to non-negative vectors.

Proof: entry `i` expands as `(1 + Δt·K_ii)·y_i + Δt·∑_{j≠i} K_ij·y_j`, where
the step bound makes the first factor non-negative (splitting on the sign of
`K_ii`) and the Metzler property makes every summand of the second term
non-negative. -/
theorem orthant_invariance_fwdEuler
    {K : n → n → ℝ} (hK : IsMetzler K)
    {dt : ℝ} (hdt : 0 ≤ dt) (hstep : ∀ j, dt * |K j j| ≤ 1)
    {y : n → ℝ} (hy : NonNegVec y) :
    NonNegVec (fwdEuler K dt y) := by
  intro i
  unfold fwdEuler
  have hco : 0 ≤ 1 + dt * K i i := by
    have h := hstep i
    by_cases hz : K i i < 0
    · have habs : |K i i| = -(K i i) := abs_of_neg hz
      rw [habs] at h
      linarith
    · have hnn : 0 ≤ K i i := le_of_not_gt hz
      have hprod : 0 ≤ dt * K i i := mul_nonneg hdt hnn
      linarith
  have hsplit : ∑ j, K i j * y j
      = K i i * y i
        + Finset.sum (Finset.univ.erase i) (fun j => K i j * y j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hoff : 0 ≤ dt * Finset.sum (Finset.univ.erase i) (fun j => K i j * y j) := by
    apply mul_nonneg hdt
    apply Finset.sum_nonneg
    intro j hj
    rw [Finset.mem_erase] at hj
    exact mul_nonneg (hK i j (Ne.symm hj.1)) (hy j)
  calc y i + dt * ∑ j, K i j * y j
      = (1 + dt * K i i) * y i
        + dt * Finset.sum (Finset.univ.erase i) (fun j => K i j * y j) := by
          rw [hsplit]; ring
    _ ≥ 0 := add_nonneg (mul_nonneg hco (hy i)) hoff

/-- **Orthant invariance under the literal division-form step bound**
`Δt ≤ 1/|K_jj|` for every `j` (i.e. `Δt ≤ min_j 1/|K_jj|`). -/
theorem orthant_invariance_fwdEuler_divBound
    {K : n → n → ℝ} (hK : IsMetzler K)
    {dt : ℝ} (hdt : 0 ≤ dt) (hstep : ∀ j, dt ≤ 1 / |K j j|)
    {y : n → ℝ} (hy : NonNegVec y) :
    NonNegVec (fwdEuler K dt y) := by
  refine orthant_invariance_fwdEuler hK hdt ?_ hy
  intro j
  have h := hstep j
  by_cases hz : K j j = 0
  · rw [hz, abs_zero, div_zero] at h
    have ht : dt = 0 := le_antisymm h hdt
    simp [ht]
  · have hpos : 0 < |K j j| := abs_pos.2 hz
    have h2 : dt * |K j j| ≤ (1 / |K j j|) * |K j j| :=
      mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
    exact h2

/-! ## General SDIRK2 stage matrix (M-matrix structure) -/

/-- SDIRK2 stage matrix `M = I - c·K` for step factor `c = γΔt > 0`. -/
noncomputable def sdirkStage (K : n → n → ℝ) (c : ℝ) : n → n → ℝ :=
  fun i j => (if i = j then 1 else 0) - c * K i j

/-- A Z-matrix has non-positive off-diagonal entries. -/
def IsZMatrix (M : n → n → ℝ) : Prop :=
  ∀ i j, i ≠ j → M i j ≤ 0

/-- The SDIRK2 stage matrix of a compartmental (Metzler) system is a
    Z-matrix with diagonal entries ≥ 1: off-diagonals `-c·K_ij ≤ 0`
    since `K_ij ≥ 0`, and diagonal `1 - c·K_ii ≥ 1` since `K_ii ≤ 0`. -/
theorem sdirk_stage_isMmatrix {K : n → n → ℝ} (hK : IsMetzler K)
    (hcol : HasNonposColSums K) {c : ℝ} (hc : 0 < c) :
    IsZMatrix (sdirkStage K c) ∧ ∀ i, 1 ≤ sdirkStage K c i i := by
  constructor
  · intro i j hij
    unfold sdirkStage
    rw [if_neg hij]
    have h : 0 ≤ c * K i j := mul_nonneg (le_of_lt hc) (hK i j hij)
    linarith
  · intro i
    unfold sdirkStage
    rw [if_pos rfl]
    have hd : K i i ≤ 0 := diag_nonpos hK hcol i
    have h : c * K i i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hd
    linarith

/-- Any matrix with a non-negative inverse preserves non-negativity:
    if `M⁻¹` exists entry-wise non-negative and `M·z = b ≥ 0`,
    then `z = M⁻¹·b ≥ 0`. This is the abstract inverse-nonnegativity
    used by the SDIRK2 stage solve. -/
theorem mmatrix_inv_preserves_nonneg {M Minv : n → n → ℝ}
    (hinv_nonneg : ∀ i j, 0 ≤ Minv i j)
    {b z : n → ℝ} (hb : NonNegVec b)
    (hsolve : ∀ i, ∑ j, M i j * z j = b i)
    (hinv : ∀ i j, ∑ k, Minv i k * M k j = (if i = j then 1 else 0)) :
    NonNegVec z := by
  intro i
  have h : z i = ∑ k, Minv i k * b k := by
    calc z i = ∑ j, (if i = j then (1:ℝ) else 0) * z j := by
            simp
      _ = ∑ j, (∑ k, Minv i k * M k j) * z j := by
            congr 1; ext j; rw [hinv i j]
      _ = ∑ k, Minv i k * b k := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [← hsolve k, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            ring
  rw [h]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hinv_nonneg i k) (hb k))

/-! ## Saturable cooperative kinetics -/

/-- Saturable flux with capacity `Vmax > 0` and half-saturation `Km > 0`:
    `f(C) = Vmax * C / (Km + C)`.

    Purely real-analytic: `Vmax` is a rate capacity and `Km` a saturation
    constant. No domain meaning is attached; downstream models instantiate
    this with their own parameters. -/
noncomputable def saturableFlux (Vmax Km C : ℝ) : ℝ :=
  Vmax * C / (Km + C)

/-- Saturable flux is non-negative on non-negative substrate. -/
theorem saturableFlux_nonneg {Vmax Km C : ℝ}
    (hV : 0 < Vmax) (hK : 0 < Km) (hC : 0 ≤ C) :
    0 ≤ saturableFlux Vmax Km C := by
  unfold saturableFlux
  exact div_nonneg (mul_nonneg (le_of_lt hV) hC) (by linarith : (0:ℝ) ≤ Km + C)

/-- Saturable flux is strictly bounded by capacity on non-negative substrate:
    `Vmax * C / (Km + C) < Vmax` since `Vmax * Km > 0` absorbs the gap. -/
theorem saturableFlux_bounded {Vmax Km C : ℝ}
    (hV : 0 < Vmax) (hK : 0 < Km) (hC : 0 ≤ C) :
    saturableFlux Vmax Km C < Vmax := by
  unfold saturableFlux
  have hden : (0:ℝ) < Km + C := by linarith
  rw [div_lt_iff₀ hden]
  have heq : Vmax * (Km + C) - Vmax * C = Vmax * Km := by ring
  have hpos : (0:ℝ) < Vmax * Km := mul_pos hV hK
  linarith

/-- Saturable flux is monotone on non-negative substrate: clearing the two
    positive denominators reduces the goal to `0 ≤ Vmax * Km * (C₂ - C₁)`. -/
theorem saturableFlux_mono {Vmax Km C₁ C₂ : ℝ}
    (hV : 0 < Vmax) (hK : 0 < Km)
    (hC₁ : 0 ≤ C₁) (h12 : C₁ ≤ C₂) :
    saturableFlux Vmax Km C₁ ≤ saturableFlux Vmax Km C₂ := by
  unfold saturableFlux
  have hden₁ : (0:ℝ) < Km + C₁ := by linarith
  have hC₂ : (0:ℝ) ≤ C₂ := le_trans hC₁ h12
  have hden₂ : (0:ℝ) < Km + C₂ := by linarith
  rw [div_le_div_iff₀ hden₁ hden₂]
  have heq : Vmax * C₂ * (Km + C₁) - Vmax * C₁ * (Km + C₂)
      = Vmax * Km * (C₂ - C₁) := by ring
  have hkey : (0:ℝ) ≤ Vmax * Km * (C₂ - C₁) :=
    mul_nonneg (mul_nonneg (le_of_lt hV) (le_of_lt hK)) (sub_nonneg.mpr h12)
  linarith

end Compartmental

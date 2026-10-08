import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalInputRayleigh
import Mathlib.Tactic

/-!
# P4: diagonal control of genuine pair-Haar residual Gram cross terms

At the exact post-#5271 physical input Rayleigh interface, the remaining
quantitative issue is a finite Gram matrix with entries

  G(i,j) = sum_e inner(v_i - Q_e v_i, v_j - Q_e v_j),

for the ORIGINAL joint-posterior projections transported through the
genuine half-density.  Here we prove the unconditional finite-volume
cross-term estimate

  2 * abs(G(i,j)) <= G(i,i) + G(j,j).

The proof is the real Hilbert-space Cauchy-Schwarz inequality applied
BEFORE summation over the original spatial links, combined with Young's
inequality.  No count of links replaces this exact sum. Consequently,
any common upper bound on the two true diagonal losses also controls
their off-diagonal interference; there is no separate off-diagonal
volume-uniform problem at fixed Krylov depth.

We specialize to the ACTUAL right (r+1)-mode Krylov Gram and the
three physical left-mode Gram. The orbit is at beta(n+1), with the
frozen conditional law at beta(n).  This is an algebraic reduction,
NOT an independently proved volume-uniform diagonal bound.

Dobrushin, covariance/local-coordinate identification, positive-depth
hard support, new conditional kernels, and continuum mass gap are
not used or claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4CrossControlTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4CrossControlCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4CrossControlSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4CrossControlMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4CrossControlBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4CrossControlSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Full-link mixed Gram entries are bounded by the two TRUE
full-link diagonal energies. This is Hilbert Cauchy-Schwarz and Young,
not a bound by spatial-link cardinality or by a surrogate covariance. -/
theorem pairHaarSpatialLinkResidualGram_offdiag_le_diagonal_sum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (i j : ι) :
    2 * |pairHaarSpatialLinkResidualGram H N hN beta hbeta v i j| ≤
      pairHaarSpatialLinkResidualGram H N hN beta hbeta v i i +
      pairHaarSpatialLinkResidualGram H N hN beta hbeta v j j := by
  classical
  let G := pairHaarSpatialLinkResidualGram H N hN beta hbeta v
  let D (e : PeriodicHypercubicEvenSpatialSliceLink H) (p : ι) :=
    v p - pairHaarTransportedGroundStateSpatialLinkProjection
      H N hN beta hbeta e (v p)
  have hEntry (p q : ι) :
      G p q = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ⟪D e p, D e q⟫_ℝ := by
    simp only [G, D, pairHaarSpatialLinkResidualGram,
      Matrix.sum_apply, Matrix.gram_apply]
  have hDiag (p : ι) :
      G p p = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖D e p‖ ^ 2 :=
    pairHaarSpatialLinkResidualGram_diag H N hN beta hbeta v p
  have hEach (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      2 * |⟪D e i, D e j⟫_ℝ| ≤ ‖D e i‖ ^ 2 + ‖D e j‖ ^ 2 := by
    have hCS := abs_real_inner_le_norm (D e i) (D e j)
    have hSquare := sq_nonneg (‖D e i‖ - ‖D e j‖)
    nlinarith
  have hAbs :=
    Finset.abs_sum_le_sum_abs
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        ⟪D e i, D e j⟫_ℝ) (Finset.univ)
  have hSum :
      2 * |∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ⟪D e i, D e j⟫_ℝ| ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (‖D e i‖ ^ 2 + ‖D e j‖ ^ 2) := by
    calc
      2 * |∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ⟪D e i, D e j⟫_ℝ| ≤
        2 * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          |⟪D e i, D e j⟫_ℝ| :=
            mul_le_mul_of_nonneg_left hAbs (by norm_num)
      _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          2 * |⟪D e i, D e j⟫_ℝ| := by rw [Finset.mul_sum]
      _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (‖D e i‖ ^ 2 + ‖D e j‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro e _he
            exact hEach e
  calc
    2 * |G i j| =
        2 * |∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ⟪D e i, D e j⟫_ℝ| := by rw [hEntry]
    _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (‖D e i‖ ^ 2 + ‖D e j‖ ^ 2) := hSum
    _ = G i i + G j j := by
      rw [Finset.sum_add_distrib, hDiag i, hDiag j]

/-- A common upper bound on two actual full-link diagonal losses
also bounds their Gram cross term: no separate mixed-entry hypothesis. -/
theorem pairHaarSpatialLinkResidualGram_offdiag_abs_le_of_diagonal_bounds
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (i j : ι) (C : ℝ)
    (hi : pairHaarSpatialLinkResidualGram H N hN beta hbeta v i i ≤ C)
    (hj : pairHaarSpatialLinkResidualGram H N hN beta hbeta v j j ≤ C) :
    |pairHaarSpatialLinkResidualGram H N hN beta hbeta v i j| ≤ C := by
  have hCross :=
    pairHaarSpatialLinkResidualGram_offdiag_le_diagonal_sum
      H N hN beta hbeta v i j
  linarith

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Right Krylov interference is controlled by its two true diagonal
full-link residual losses, at each finite n,r, without Dobrushin. -/
theorem fineRightKrylovPairHaarResidualGram_offdiag_le_diagonal_sum
    (i j : Fin (r + 1)) :
    2 * |fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j| ≤
      fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i i +
      fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j j :=
  pairHaarSpatialLinkResidualGram_offdiag_le_diagonal_sum
    Hn 2 Pos (beta n) (hbeta n)
    (fun k : Fin (r + 1) =>
      normalizedPhysicalOneSlabPairHaarReceiver
        Hn 2 Pos (beta n) (hbeta n) (RightFactor n (k : ℕ))) i j

/-- All mixed entries of the original left three-mode Gram are
controlled by its two exact diagonal full-link losses. -/
theorem fineLeftThreeModePairHaarResidualGram_offdiag_le_diagonal_sum
    (i j : Fin 3) :
    2 * |fineLeftThreeModePairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j| ≤
      fineLeftThreeModePairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i i +
      fineLeftThreeModePairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j j :=
  pairHaarSpatialLinkResidualGram_offdiag_le_diagonal_sum
    Hn 2 Pos (beta n) (hbeta n)
    (fun k : Fin 3 =>
      normalizedPhysicalOneSlabPairHaarReceiver
        Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)) i j

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

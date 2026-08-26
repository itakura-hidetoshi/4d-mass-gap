import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszDynamics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexRieszAsymptoticCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- A geometric norm bound with ratio in `[0,1)` forces convergence to zero.
This small generic carrier is shared by operator-norm, strong, and matrix-element
limits below. -/
private theorem tendsto_zero_of_norm_le_geometric_succ
    {E : Type*} [SeminormedAddCommGroup E]
    (q C : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (u : ℕ → E)
    (hu : ∀ n : ℕ, ‖u n‖ ≤ q ^ (n + 1) * C) :
    Tendsto u atTop (𝓝 0) := by
  have hqpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hqpowSucc : Tendsto (fun n : ℕ => q ^ (n + 1)) atTop (𝓝 0) := by
    simpa [pow_succ] using hqpow.mul_const q
  have hrhs : Tendsto (fun n : ℕ => q ^ (n + 1) * C) atTop (𝓝 0) := by
    simpa using hqpowSucc.mul_const C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg (u n)) hu hrhs

/-- For every admissible contour, positive powers of the genuine normalized
complex Wilson transfer converge in operator norm to the contour-defined Riesz
projector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_tendsto_rieszProjectorAtRadius
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1))
      atTop
      (𝓝
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r)) := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
    H N hN beta hbeta r
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta)
  have hq1 : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hbound : ∀ n : ℕ, ‖S ^ (n + 1) - P‖ ≤ q ^ (n + 1) * 1 := by
    intro n
    simpa [S, P, q] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_rieszProjectorAtRadius_norm_le
        H N hN beta hbeta r hr hrgap n
  have hdiff : Tendsto (fun n : ℕ => S ^ (n + 1) - P) atTop (𝓝 0) :=
    tendsto_zero_of_norm_le_geometric_succ q 1 hq0 hq1
      (fun n : ℕ => S ^ (n + 1) - P) hbound
  have hconst : Tendsto (fun _ : ℕ => P) atTop (𝓝 P) := tendsto_const_nhds
  have hadd : Tendsto
      (fun n : ℕ => (S ^ (n + 1) - P) + P) atTop (𝓝 P) := by
    simpa using hdiff.add hconst
  simpa [S, P] using hadd

/-- The same contour-defined asymptotic projector is the strong limit on every
physical vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_tendsto_rieszProjectorAtRadius
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    Tendsto
      (fun n : ℕ =>
        ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1)) f)
      atTop
      (𝓝
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r f)) := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
    H N hN beta hbeta r
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta)
  have hq1 : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hbound : ∀ n : ℕ,
      ‖(S ^ (n + 1)) f - P f‖ ≤ q ^ (n + 1) * ‖f‖ := by
    intro n
    simpa [S, P, q] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_sub_rieszProjectorAtRadius_norm_le
        H N hN beta hbeta r hr hrgap n f
  have hdiff : Tendsto (fun n : ℕ => (S ^ (n + 1)) f - P f) atTop (𝓝 0) :=
    tendsto_zero_of_norm_le_geometric_succ q ‖f‖ hq0 hq1
      (fun n : ℕ => (S ^ (n + 1)) f - P f) hbound
  have hconst : Tendsto (fun _ : ℕ => P f) atTop (𝓝 (P f)) := tendsto_const_nhds
  have hadd : Tendsto
      (fun n : ℕ => ((S ^ (n + 1)) f - P f) + P f)
      atTop (𝓝 (P f)) := by
    simpa using hdiff.add hconst
  simpa [S, P] using hadd

/-- All complex Hilbert matrix elements converge to the matrix element of the
same admissible contour-defined Riesz projector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_tendsto_rieszProjectorAtRadius
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    Tendsto
      (fun n : ℕ =>
        inner ℂ f
          (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) g))
      atTop
      (𝓝
        (inner ℂ f
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
            H N hN beta hbeta r g))) := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
    H N hN beta hbeta r
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta)
  have hq1 : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hbound : ∀ n : ℕ,
      ‖inner ℂ f ((S ^ (n + 1)) g) - inner ℂ f (P g)‖ ≤
        q ^ (n + 1) * (‖f‖ * ‖g‖) := by
    intro n
    have h :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_sub_rieszProjectorAtRadius_norm_le
        H N hN beta hbeta r hr hrgap n f g
    simpa [S, P, q, mul_assoc] using h
  have hdiff : Tendsto
      (fun n : ℕ => inner ℂ f ((S ^ (n + 1)) g) - inner ℂ f (P g))
      atTop (𝓝 0) :=
    tendsto_zero_of_norm_le_geometric_succ q (‖f‖ * ‖g‖) hq0 hq1
      (fun n : ℕ => inner ℂ f ((S ^ (n + 1)) g) - inner ℂ f (P g)) hbound
  have hconst : Tendsto
      (fun _ : ℕ => inner ℂ f (P g)) atTop (𝓝 (inner ℂ f (P g))) :=
    tendsto_const_nhds
  have hadd : Tendsto
      (fun n : ℕ =>
        (inner ℂ f ((S ^ (n + 1)) g) - inner ℂ f (P g)) + inner ℂ f (P g))
      atTop (𝓝 (inner ℂ f (P g))) := by
    simpa using hdiff.add hconst
  simpa [S, P] using hadd

/-- Audit-visible statement that the contour-defined Riesz projector is
simultaneously the operator-norm, strong, and matrix-element asymptotic
projection of the normalized complex Wilson transfer. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszAsymptoticProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  operatorNormLimit :
    ∀ (r : ℝ), 0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      Tendsto
        (fun n : ℕ =>
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1))
        atTop
        (𝓝
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
            H N hN beta hbeta r))
  strongLimit :
    ∀ (r : ℝ), 0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      Tendsto
        (fun n : ℕ =>
          ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) f)
        atTop
        (𝓝
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
            H N hN beta hbeta r f))
  matrixElementLimit :
    ∀ (r : ℝ), 0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      ∀ f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      Tendsto
        (fun n : ℕ =>
          inner ℂ f
            (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) g))
        atTop
        (𝓝
          (inner ℂ f
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
              H N hN beta hbeta r g)))

/-- Construct the exact Riesz asymptotic-projection package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszAsymptoticProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszAsymptoticProjectionPackage
      H N hN beta hbeta :=
  { operatorNormLimit :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_tendsto_rieszProjectorAtRadius
        H N hN beta hbeta
    strongLimit :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_tendsto_rieszProjectorAtRadius
        H N hN beta hbeta
    matrixElementLimit :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_tendsto_rieszProjectorAtRadius
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorVolumeIndependentConstant
import Mathlib.Tactic

/-!
# Exact posterior receiver bridge for the Gram--Schmidt seed

The seed-right receiver from the exact Dirichlet factorization contains the raw
one-slice transfer integral

  integral K(A,B) O(A) dHaar(A).

The normalized continuous-vacuum posterior instead has raw density

  Omega(A) K(A,B).

Thus the literal posterior observable corresponding to the transfer receiver is
not the bare seed O, but the vacuum-divided observable O / Omega.  This file
records that distinction exactly.

For every bounded-continuous O,

  integral K(A,B) O(A) dHaar(A)
    = ||T_phys|| * Omega(B) * E_{pi_B}[O / Omega].

We then specialize this identity to the canonical SU(2) primary-plaquette
Gram--Schmidt seed and rewrite the decomposable right-output factor.

This is an exact interface theorem only.  It does not identify covariance with
an L2 coordinate norm, assert positive-depth hard support, remove the output
drift, or add a new Dobrushin hypothesis.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3SeedPosteriorReceiverBridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3SeedPosteriorReceiverBridgeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3SeedPosteriorReceiverBridgeSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3SeedPosteriorReceiverBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3SeedPosteriorReceiverBridgeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3SeedPosteriorReceiverBridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Divide a bounded-continuous slice observable by the strictly positive
continuous physical vacuum.  Compactness makes the quotient bounded. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun A =>
        O A /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta A,
      O.continuous.div
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
          H N hN beta hbeta)
        (fun A =>
          ne_of_gt
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
              H N hN beta hbeta A))⟩

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
        H N hN beta hbeta O A =
      O A /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta A := by
  rfl

/-- Exact normalized-posterior presentation of the raw kernel integral of an
arbitrary bounded-continuous observable.  The vacuum division is essential. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_vacuumDivided_eq_kernelIntegral_div
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
          H N hN beta hbeta O) =
      (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A B * O A
          ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) /
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta B) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
  rw [MeasureTheory.integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp_integral_eq_topNorm_mul_vacuum
      H N hN beta hbeta B
  ]
  congr 1
  apply integral_congr_ae
  filter_upwards with A
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp
      H N hN beta hbeta B A
  ]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
  simp only [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable_apply
  ]
  field_simp [
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta A).ne'
  ]
  <;> ring

namespace GroundStatePosteriorJoint

/-- Exact receiver identity for the canonical primary-plaquette Gram--Schmidt
physical mode.  The L2 representative is replaced only under the Haar
integral by its already-proved continuous representative. -/
theorem
    decomposableOneSliceTransferIntegral_gramSchmidt_eq_topNorm_mul_vacuum_mul_posteriorMean
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    decomposableOneSliceTransferIntegral H 2 beta
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H mode :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
        B =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
            (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
              H mode)) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let O :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
      H mode
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
  have hlambda : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  have homega : 0 < omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
  have hcoe :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2_coeFn
      H mode
  have htransfer :
      decomposableOneSliceTransferIntegral H 2 beta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
            H mode : Lp ℝ 2 mu)
          B =
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H 2 beta A B * O A
          ∂mu := by
    unfold decomposableOneSliceTransferIntegral
    apply integral_congr_ae
    filter_upwards [hcoe] with A hA
    rw [hA]
  rw [htransfer]
  have hposterior :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_vacuumDivided_eq_kernelIntegral_div
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B O
  change
    (∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H 2 beta A B * O A
        ∂mu) =
      lambda * omega *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta O)
  rw [hposterior]
  field_simp [hlambda.ne', homega.ne']

/-- The depth-zero Gram--Schmidt right-output factor therefore receives the
posterior mean of O/Omega, not the bare four-link seed O.  All normalization
and joint half-density factors remain explicit. -/
theorem
    decomposableRightOutputFactor_gramSchmidt_eq_vacuumDividedPosteriorMean
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    decomposableRightOutputFactor
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H mode)
        z =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖ ^ 2)⁻¹ *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H 2 specialUnitaryTwoWilsonRankPositive beta hbeta z.2 *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta z.2
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
              H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
              (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
                H mode))) /
        continuousJointSqrtDensity
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta z := by
  unfold decomposableRightOutputFactor
  rw [
    decomposableOneSliceTransferIntegral_gramSchmidt_eq_topNorm_mul_vacuum_mul_posteriorMean
      H mode beta hbeta z.2
  ]

end GroundStatePosteriorJoint

end

end MathlibAnalytic
end MGAP4D

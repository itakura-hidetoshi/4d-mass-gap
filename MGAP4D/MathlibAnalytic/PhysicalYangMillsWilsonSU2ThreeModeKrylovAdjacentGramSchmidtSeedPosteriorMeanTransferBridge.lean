import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedVacuumL2Bridge
import MGAP4D.MathlibAnalytic.RealL2BoundedKernelIntegralRepresentation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalization
import Mathlib.Tactic

/-!
# Gram--Schmidt posterior mean as normalized physical transfer in vacuum L2

PR #5252 identifies the literal seed receiver posterior observable as O/Omega.
PR #5253 identifies O/Omega itself with the existing Haar-to-vacuum L2 isometry.

The remaining exact bridge is the posterior mean over the left boundary.
For a physical Haar-L2 vector f, the one-slab transfer has the literal
fiber-integral representative

  B |-> integral K(A,B) f(A) dHaar(A).

For the canonical Gram--Schmidt seed O, PR #5252 then gives

  E_{pi_B}[O/Omega]
    = lambda^(-1) (integral K(A,B) O(A) dHaar(A)) / Omega(B).

This is exactly the representative of

  U (S f_GS),

where U is the existing Haar-to-vacuum ground-state isometry and
S = lambda^(-1) T_phys is the normalized physical one-slab transfer.

Consequently the posterior-mean receiver has vacuum-L2 norm at most one,
using only ||S|| = 1 and ||f_GS|| = 1.  No inverse-vacuum sup bound, new
Dobrushin estimate, covariance/L2-coordinate identification, positive-depth
hard support, or output-drift deletion is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3PosteriorMeanTransferBridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3PosteriorMeanTransferBridgeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3PosteriorMeanTransferBridgeSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3PosteriorMeanTransferBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3PosteriorMeanTransferBridgeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3PosteriorMeanTransferBridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3PosteriorMeanTransferBridgeSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance p3PosteriorMeanTransferBridgeVacuumProbability
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- The physical one-slab transfer has the literal one-slice Wilson-kernel
fiber integral as a Haar-a.e. representative.  This is the vector-level
version of the raw scalar matrix-coefficient identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_ae_eq_decomposableOneSliceTransferIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      decomposableOneSliceTransferIntegral H N beta
        (f :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let k := fun
      (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A B
  let fA : Lp ℝ 2 mu := f
  have hkMeas :
      AEStronglyMeasurable
        (fun p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          k p.1 p.2)
        (mu.prod mu) := by
    simpa [k, mu] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).measurable.aestronglyMeasurable
  have hkBound :
      ∀ A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |k A B| ≤ 1 := by
    intro A B
    simpa [k] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta A B
  have hK :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta =ᵐ[mu.prod mu]
        fun p => k p.1 p.2 := by
    simpa [mu, k,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H N hN beta hbeta
  let out :=
    realL2BoundedKernelIntegralOutputL2
      (mu := mu) k hkMeas hkBound fA
  have hApply :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta fA = out := by
    change
      realL2HilbertSchmidtKernelOperator
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
            H N hN beta hbeta) fA = out
    simpa [out] using
      (realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2
        (mu := mu) k
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta)
        hK hkMeas hkBound fA)
  have hOut :=
    realL2BoundedKernelIntegralOutputL2_coeFn
      (mu := mu) k hkMeas hkBound fA
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe]
  rw [show
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta fA = out by
      exact hApply]
  simpa [out, fA, mu, k,
    realL2BoundedKernelIntegralOutput,
    decomposableOneSliceTransferIntegral] using hOut

/-- The normalized physical transfer therefore has representative
lambda^{-1} times the literal one-slice transfer integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_ae_eq_inv_mul_decomposableOneSliceTransferIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun B =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ *
          decomposableOneSliceTransferIntegral H N beta
            (f :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            B := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let Tf : Lp ℝ 2 mu :=
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 mu)
  have hNormalized :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply
      H N hN beta hbeta f
  have hVec :
      ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 mu) =
      lambda⁻¹ • Tf := by
    exact congrArg
      (fun x :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
        (x : Lp ℝ 2 mu))
      hNormalized
  have hSmul := Lp.coeFn_smul lambda⁻¹ Tf
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_ae_eq_decomposableOneSliceTransferIntegral
      H N hN beta hbeta f
  rw [hVec]
  filter_upwards [hSmul, hRaw] with B hSmulB hRawB
  rw [hSmulB]
  change
    lambda⁻¹ * Tf B =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        decomposableOneSliceTransferIntegral H N beta
          (f :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          B
  rw [hRawB]
  rfl

/-- Continuous posterior-mean receiver for the vacuum-divided canonical
Gram--Schmidt seed.  It is written directly in transfer coordinates so its
continuity is inherited from the literal one-slice kernel integral. -/
noncomputable def
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun B =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖⁻¹ *
          decomposableOneSliceTransferIntegral H 2 beta
            (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
              H mode :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
            B /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B,
      by
        have hInt :=
          decomposableOneSliceTransferIntegral_continuous
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
            (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
              H mode :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
        have hOmega :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        exact
          (continuous_const.mul hInt).div hOmega
            (fun B =>
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
                H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B).ne')⟩

/-- The preceding BCF is pointwise exactly the posterior mean of the
vacuum-divided Gram--Schmidt seed from PR #5252. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF_apply
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF
        H mode beta hbeta B =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
            H mode)) := by
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
  let m :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode))
  have hlambda : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  have homega : 0 < omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
  have hReceiver :=
    decomposableOneSliceTransferIntegral_gramSchmidt_eq_topNorm_mul_vacuum_mul_posteriorMean
      H mode beta hbeta B
  change
    lambda⁻¹ *
        decomposableOneSliceTransferIntegral H 2 beta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
            H mode :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
          B /
        omega =
      m
  change
    decomposableOneSliceTransferIntegral H 2 beta
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H mode :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
        B =
      lambda * omega * m at hReceiver
  rw [hReceiver]
  field_simp [hlambda.ne', homega.ne']

/-- As a vacuum-L2 vector, the posterior mean receiver is exactly the existing
Haar-to-vacuum isometry applied to the normalized physical transfer of the
Gram--Schmidt physical mode. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF_toLp_eq_haarToVacuum_normalizedTransfer
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
        ℝ
        (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF
          H mode beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
            (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
              H mode) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  let fp :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
      H mode
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  let g : Lp ℝ 2 mu := (S fp : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
  let M :=
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF
      H mode beta hbeta
  have hnuMu : nu ≪ mu := by
    simpa [nu, mu] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_absolutelyContinuous_Haar
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  have hMrep :=
    BoundedContinuousFunction.coeFn_toLp 2 nu ℝ M
  have hUrep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta g
  have hGmu :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_ae_eq_inv_mul_decomposableOneSliceTransferIntegral
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta fp
  have hGnu := hnuMu.ae_eq hGmu
  have hOmegaMu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  have hOmegaNu := hnuMu.ae_eq hOmegaMu
  apply Lp.ext
  filter_upwards [hMrep, hUrep, hGnu, hOmegaNu]
      with B hM hU hG hOmega
  rw [hM, hU]
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖⁻¹ *
        decomposableOneSliceTransferIntegral H 2 beta
          (fp :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
          B /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B =
      g B /
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta).1 B
  rw [hG, hOmega]
  rfl

/-- The vacuum-L2 norm of the posterior mean receiver is exactly the Haar-L2
norm of the normalized physical transfer image. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF_toLp_norm_eq_normalizedTransfer
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
        ℝ
        (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF
          H mode beta hbeta)‖ =
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
            H mode)‖ := by
  rw [
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF_toLp_eq_haarToVacuum_normalizedTransfer
      H mode beta hbeta
  ]
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
            (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
              H mode) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))‖ =
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
            (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
              H mode) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))‖ := by
        exact
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta).norm_map _
    _ =
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
            H mode)‖ := rfl

/-- Since the normalized physical transfer has operator norm one and every
canonical Gram--Schmidt seed mode has norm one, the posterior mean receiver has
vacuum-L2 norm at most one, uniformly in the finite spatial volume. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF_toLp_norm_le_one
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
        ℝ
        (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF
          H mode beta hbeta)‖ ≤ 1 := by
  rw [
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF_toLp_norm_eq_normalizedTransfer
      H mode beta hbeta
  ]
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  let f :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
      H mode
  have hOp :
      ‖S f‖ ≤ ‖S‖ * ‖f‖ :=
    ContinuousLinearMap.le_opNorm S f
  have hS :
      ‖S‖ = 1 := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  have hf :
      ‖f‖ = 1 := by
    simpa [f] using
      periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2_norm
        H mode
  simpa [S, f, hS, hf] using hOp

end GroundStatePosteriorJoint

end

end MathlibAnalytic
end MGAP4D

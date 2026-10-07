import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorReceiverBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonVacuumL2LinearIsometry
import Mathlib.Tactic

/-!
# Gram--Schmidt vacuum-divided receiver as the existing vacuum L2 isometry

PR #5252 exposes the exact posterior receiver observable as the bounded
continuous quotient

  O / Omega_cont.

The repository already contains the canonical ground-state transform

  U : L2(Haar) -> L2(Omega^2 dHaar),   f |-> f / Omega,

proved to be a linear isometry.

This file identifies the new continuous quotient with that existing Hilbert
space construction for every canonical SU(2) primary-plaquette Gram--Schmidt
mode.  Hence its vacuum-weighted L2 norm is exactly the original Haar-L2 norm,
with no inverse-vacuum sup bound and no finite-volume vacuum floor.

The Gram--Schmidt physical mode has Haar-L2 norm one, so the vacuum-divided
receiver has vacuum-L2 norm one as well.

No new Dobrushin estimate, positive-depth hard support, covariance/L2
identification, or continuum claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3SeedVacuumL2BridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3SeedVacuumL2BridgeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3SeedVacuumL2BridgeSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3SeedVacuumL2BridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3SeedVacuumL2BridgeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3SeedVacuumL2BridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The canonical vacuum law is a probability measure.  Registering this
locally lets Mathlib synthesize the finite-measure instance required by
BoundedContinuousFunction.toLp. -/
local instance p3SeedVacuumL2BridgeVacuumProbability
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
    H 2 specialUnitaryTwoWilsonRankPositive beta hbeta

/-- The continuous vacuum-divided Gram--Schmidt BCF represents exactly the
existing Haar-to-vacuum ground-state transform in vacuum-weighted L2. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedBCF_toLp_eq_haarToVacuumL2
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
        ℝ
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
            H mode)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H mode :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  let f : Lp ℝ 2 mu :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
      H mode
  let O :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
      H mode
  let Q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta O
  have hnuMu : nu ≪ mu := by
    simpa [nu, mu] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_absolutelyContinuous_Haar
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  have hQrep :=
    BoundedContinuousFunction.coeFn_toLp 2 nu ℝ Q
  have hUrep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta f
  have hfHaar :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2_coeFn
      H mode
  have hfVacuum := hnuMu.ae_eq hfHaar
  have hOmegaHaar :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  have hOmegaVacuum := hnuMu.ae_eq hOmegaHaar
  apply Lp.ext
  filter_upwards [hQrep, hUrep, hfVacuum, hOmegaVacuum]
      with A hQ hU hf hOmega
  rw [hQ, hU]
  change
    O A /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta A =
      f A /
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta).1 A
  rw [hf, hOmega]

/-- The vacuum-weighted L2 norm of the continuous quotient is exactly the
Haar-L2 norm of the original Gram--Schmidt physical mode. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedBCF_toLp_norm
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
        ℝ
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
            H mode))‖ =
      ‖(periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H mode :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))‖ := by
  rw [
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedBCF_toLp_eq_haarToVacuumL2
      H mode beta hbeta
  ]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_norm
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
        H mode :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))

/-- Every canonical primary-plaquette SU(2) Gram--Schmidt physical slice mode
has Haar-L2 norm one. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2_norm
    (H mode : ℕ) :
    ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
        H mode‖ = 1 := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  have hPair :
      ‖periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
          H mode‖ = 1 :=
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_orthonormal
      H).norm_eq_one mode
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_eq_physicalDecomposable
      H mode
  ] at hPair
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
    at hPair
  have hTensor :
      ‖realL2ExternalTensor
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
            H mode :
            Lp ℝ 2 mu)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            H 2 :
            Lp ℝ 2 mu)‖ =
        ‖(periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
            H mode :
            Lp ℝ 2 mu)‖ *
          ‖(periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            H 2 :
            Lp ℝ 2 mu)‖ := by
    exact
      realL2ExternalTensor_norm
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H mode :
          Lp ℝ 2 mu)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          H 2 :
          Lp ℝ 2 mu)
  have hOne :
      ‖(periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          H 2 :
          Lp ℝ 2 mu)‖ = 1 := by
    simpa only [Submodule.norm_coe] using
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  change
    ‖realL2ExternalTensor
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H mode :
          Lp ℝ 2 mu)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          H 2 :
          Lp ℝ 2 mu)‖ = 1
    at hPair
  rw [hTensor, hOne, mul_one] at hPair
  simpa only [Submodule.norm_coe] using hPair

/-- Consequently the continuous posterior receiver O/Omega has exact
vacuum-weighted L2 norm one for every canonical Gram--Schmidt mode. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedBCF_toLp_norm_eq_one
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
        ℝ
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumDividedBoundedObservable
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
            H mode))‖ = 1 := by
  rw [
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedBCF_toLp_norm
      H mode beta hbeta
  ]
  simpa only [Submodule.norm_coe] using
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2_norm
      H mode

end

end MathlibAnalytic
end MGAP4D

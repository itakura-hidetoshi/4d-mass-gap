import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureInfluence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledRandomScanFiniteStep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceRestrictedRandomScanLocalResidualSweep
import MGAP4D.MathlibAnalytic.FinitePositiveWeightReciprocalInfluenceKernelResponse
import Mathlib.Tactic

/-!
# Canonical high-temperature random-scan contraction

The canonical high-temperature physical influence theorem gives a weighted
column contraction for every scale s >= 1.  At the endpoint s = 1 the spatial
weight is identically one, so the same theorem becomes an ordinary Dobrushin
column bound for the actual canonical pin-free physical influence kernel:

  columnSum K_can < q(1,beta) < 1.

The repository's reciprocal random-scan machinery then gives geometric
finite-step contraction.  After one whole number of physical-link sweeps the
cardinality dependence disappears from the exponent:

  variation <= exp (-(1 - q(1,beta)) * sweeps) * bound.

Finally the existing finite-step physical transport theorem carries this
abstract kernel contraction to the literal restricted random-scan observable
dynamics.

This is still a finite-volume random-scan variation contraction theorem.  It
does not yet assert a Poincare/coercivity inequality, a Hamiltonian spectral
gap, covariance clustering, or a continuum Yang-Mills construction.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

local instance canonicalHighTemperatureRandomScanSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalHighTemperatureRandomScanSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalHighTemperatureRandomScanSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalHighTemperatureRandomScanSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalHighTemperatureRandomScanSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalHighTemperatureRandomScanSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At scale one the exponential base-L1 weight is identically one. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_one
    (H : ℕ)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H 1 center source = 1 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight]

/-- The actual canonical pin-free physical influence kernel has an ordinary
column sum strictly below the common high-temperature envelope at s = 1. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_columnSum_lt_halfBarrierCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta))
        source <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        1 beta := by
  classical
  have hWeighted :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_lt_halfBarrierCoefficient
      H N hN 1 (by norm_num) beta hbeta hcut source source
  simpa [finiteInfluenceKernelColumnSum] using hWeighted

/-- The reciprocal one-coordinate random-scan rate generated by the canonical
high-temperature envelope is strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRight_reciprocalRandomScanRate_lt_one
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1) :
    finiteInfluenceKernelReciprocalRandomScanRate
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          1 beta) < 1 := by
  exact
    finiteInfluenceKernelReciprocalRandomScanRate_lt_one
      (periodicHypercubicEvenSpatialSliceLink_card_pos H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        1 beta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
        1 beta hbeta hcut).2

/-- Finite-step random-scan contraction for the actual canonical physical
influence kernel, using the common volume/rank-independent column envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_randomScanVariationIterate_le_rate_pow_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (n : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta))
        variation n source ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            1 beta) ^ n *
        bound := by
  classical
  exact
    finiteInfluenceKernelRandomScanVariationIterate_le_rate_pow_mul
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta))
      (periodicHypercubicEvenSpatialSliceLink_card_pos H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        1 beta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
        1 beta hbeta hcut).1
      (fun e =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_columnSum_lt_halfBarrierCoefficient
          H N hN beta hbeta hcut e).le)
      variation hVariationNonneg bound hBoundNonneg hVariationBound n source

/-- After an integral number of complete physical-link sweeps, the random-scan
variation has a volume-independent exponential envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_fullSweepVariationIterate_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (sweeps : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta))
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        source ≤
      Real.exp
          (-(1 -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
                1 beta) *
            (sweeps : ℝ)) *
        bound := by
  classical
  have hIter :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_randomScanVariationIterate_le_rate_pow_mul
      H N hN beta hbeta hcut variation hVariationNonneg
      bound hBoundNonneg hVariationBound
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
      source
  have hEnvelope :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      1 beta hbeta hcut
  have hSweep :=
    periodicHypercubicEvenSpatialSlice_reciprocalRandomScanRate_pow_card_mul_le_expSweep
      H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        1 beta)
      hEnvelope.1 hEnvelope.2 sweeps
  exact hIter.trans
    (mul_le_mul_of_nonneg_right hSweep hBoundNonneg)

/-- The repository's pin-free response-controlled orbit for the canonical
profile is exactly the ordinary random-scan iterate of its physical influence
kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_eq_kernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)
        variation n =
      finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta))
        variation n := by
  classical
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_succ,
        finiteInfluenceKernelRandomScanVariationIterate_succ]
      funext source
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
      rw [ih]
      exact
        finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_id_eq
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta))
          (finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                H N hN beta hbeta)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                H N hN beta hbeta))
            variation n)
          source

/-- The canonical pin-free response-controlled orbit therefore inherits the
same volume-independent full-sweep exponential contraction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_fullSweep_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (sweeps : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        source ≤
      Real.exp
          (-(1 -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
                1 beta) *
            (sweeps : ℝ)) *
        bound := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_eq_kernel]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_fullSweepVariationIterate_le_exp
      H N hN beta hbeta hcut variation hVariationNonneg
      bound hBoundNonneg hVariationBound sweeps source

/-- Literal finite-step physical restricted random-scan observables inherit the
canonical full-sweep contraction envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_canonicalHighTemperatureFullSweep
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (sweeps : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        (Function.update A e u) -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        (Function.update A e v)| ≤
      Real.exp
          (-(1 -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
                1 beta) *
            (sweeps : ℝ)) *
        bound := by
  have hPhysical :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_pinFreeResponseControlled
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_uniformBound
        H N hN beta hbeta)
      B target source g₂ k F hF variation hVariationNonneg hVariation
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
      e A u v
  have hOrbit :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_fullSweep_le_exp
      H N hN beta hbeta hcut variation hVariationNonneg
      bound hBoundNonneg hVariationBound sweeps e
  exact hPhysical.trans hOrbit

end

end MGAP4D.MathlibAnalytic

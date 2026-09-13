import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkMarginal
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance continuousVacuumReferenceOneLinkConditionalDensitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkConditionalDensitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkConditionalDensitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkConditionalDensitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkConditionalDensitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkConditionalDensitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The normalized literal one-link reference law has the exact density
`rho_ref(A[fiber <- g]) / lmarginal_{fiber}(rho_ref)(A)` against normalized
compact Haar measure.  This is a normalized-density identity only; no RCD
identification is asserted here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_withDensity_lmarginal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A =
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).withDensity
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
              H N hN beta hbeta B target source k g₂ (Function.update A fiber g) /
            MeasureTheory.lmarginal
              (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
                normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
              {fiber}
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
                H N hN beta hbeta B target source k g₂)
              A) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target source fiber k g₂ A
  have hwInt : Integrable w μ := by
    simpa [μ, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B target source fiber k g₂ A
  have hwNonneg : ∀ᵐ g ∂μ, 0 ≤ w g :=
    ae_of_all μ fun g =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B target source fiber k g₂ A g).le
  have hMass :
      doobWeightMass μ (fun g => ENNReal.ofReal (w g)) =
        MeasureTheory.lmarginal
          (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
          {fiber}
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
            H N hN beta hbeta B target source k g₂)
          A := by
    calc
      doobWeightMass μ (fun g => ENNReal.ofReal (w g)) =
          ENNReal.ofReal (∫ g, w g ∂μ) :=
        realIntegralWeighted_doobWeightMass_eq_ofReal_integral μ w hwInt hwNonneg
      _ = ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
            H N hN beta hbeta B target source fiber k g₂ A) := by
        rfl
      _ = MeasureTheory.lmarginal
          (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
          {fiber}
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
            H N hN beta hbeta B target source k g₂)
          A :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_ofReal_eq_lmarginal_singleton
          H N hN beta hbeta B target source fiber k g₂ A
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
    realIntegralWeightedProbabilityMeasure
    doobWeightedMeasure
    doobWeightedDensity
  change
    μ.withDensity (fun g => ENNReal.ofReal (w g) /
      doobWeightMass μ (fun x => ENNReal.ofReal (w x))) = _
  rw [hMass]
  rfl

/-- Replacing the arbitrary background value stored at the selected fiber and
then inserting the integration variable gives the same literal fiber weight.
Thus the fiber law depends only on the off-fiber background coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_update_fiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₀ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ (Function.update A fiber g₀) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A := by
  classical
  funext g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
  have hcfg :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N (Function.update A fiber g₀) fiber g =
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N A fiber g := by
    funext e
    by_cases he : e = fiber
    · subst e
      simp [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]
    · simp [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink, he]
  rw [hcfg]

/-- The exact real normalizing mass is independent of the arbitrary base value
stored at the selected fiber coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_update_fiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₀ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
        H N hN beta hbeta B target source fiber k g₂ (Function.update A fiber g₀) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
        H N hN beta hbeta B target source fiber k g₂ A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_update_fiber
    H N hN beta hbeta B target source fiber k g₂ A g₀]

/-- Consequently the normalized literal one-link reference probability measure
is independent of the arbitrary base value stored at the selected fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_update_fiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₀ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ (Function.update A fiber g₀) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_update_fiber
    H N hN beta hbeta B target source fiber k g₂ A g₀]

end

end MathlibAnalytic
end MGAP4D

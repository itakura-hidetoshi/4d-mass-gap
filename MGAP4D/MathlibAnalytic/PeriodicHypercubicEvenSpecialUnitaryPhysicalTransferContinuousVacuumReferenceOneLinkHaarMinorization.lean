import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkFiber
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceOneLinkHaarMinorizationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceOneLinkHaarMinorizationSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceOneLinkHaarMinorizationSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceOneLinkHaarMinorizationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceOneLinkHaarMinorizationSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every literal C5 reference one-link law, including the distinguished target
fiber, dominates normalized compact Haar by the volume-independent factor
exp(-32 * beta).

The proof uses only the already established pairwise Harnack comparison for the
literal reference weight. It does not use terminal covariance decay, a remote
residual bound, or a sweep contraction hypothesis. This gives an independent
finite-volume ergodicity input for closing the covariance-telescope remainder. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_lower_bound_normalizedCompactHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (ENNReal.ofReal (Real.exp (32 * beta)))⁻¹ •
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let wReal : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target source fiber k g₂ A
  let w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    fun g => ENNReal.ofReal (wReal g)
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (32 * beta))
  have hR0 : R ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hRtop : R ≠ ∞ := ENNReal.ofReal_ne_top
  have hwInt : Integrable wReal μ := by
    simpa [μ, wReal] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B target source fiber k g₂ A
  have hwNonneg : ∀ᵐ g ∂μ, 0 ≤ wReal g := by
    exact ae_of_all μ fun g =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B target source fiber k g₂ A g).le
  have hMassPos : 0 < ∫ g, wReal g ∂μ := by
    simpa [
      μ,
      wReal,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
        H N hN beta hbeta B target source fiber k g₂ A
  have hMassEq :
      doobWeightMass μ w = ENNReal.ofReal (∫ g, wReal g ∂μ) := by
    simpa [w] using
      realIntegralWeighted_doobWeightMass_eq_ofReal_integral μ wReal hwInt hwNonneg
  have hMass0 : doobWeightMass μ w ≠ 0 := by
    rw [hMassEq]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hMassPos)
  have hMassTop : doobWeightMass μ w ≠ ∞ := by
    rw [hMassEq]
    exact ENNReal.ofReal_ne_top
  have hPair :
      ∀ g h : Matrix.specialUnitaryGroup (Fin N) ℂ,
        w g ≤ R * w h := by
    intro g h
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
        H N hN beta hbeta B target source fiber k g₂ A g h).1
    dsimp [w, wReal, R]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      ENNReal.ofReal_mul (Real.exp_pos (32 * beta)).le] using
      ENNReal.ofReal_le_ofReal hReal
  have hDensity :
      (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => R⁻¹) ≤ᵐ[μ]
        doobWeightedDensity μ w := by
    filter_upwards with g
    have hMassLe : doobWeightMass μ w ≤ R * w g := by
      calc
        doobWeightMass μ w = ∫⁻ h, w h ∂μ := rfl
        _ ≤ ∫⁻ _h : Matrix.specialUnitaryGroup (Fin N) ℂ, R * w g ∂μ := by
          exact lintegral_mono (fun h => hPair h g)
        _ = R * w g := by simp [μ]
    have hScaled : R⁻¹ * doobWeightMass μ w ≤ w g := by
      calc
        R⁻¹ * doobWeightMass μ w ≤ R⁻¹ * (R * w g) := by
          gcongr
        _ = (R⁻¹ * R) * w g := by ac_rfl
        _ = w g := by
          rw [ENNReal.inv_mul_cancel hR0 hRtop, one_mul]
    change R⁻¹ ≤ w g / doobWeightMass μ w
    exact
      (ENNReal.le_div_iff_mul_le (Or.inl hMass0) (Or.inl hMassTop)).2 hScaled
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
    realIntegralWeightedProbabilityMeasure
  change R⁻¹ • μ ≤ doobWeightedMeasure μ w
  simpa [doobWeightedMeasure] using
    (withDensity_mono (μ := μ) hDensity)

end

end MathlibAnalytic
end MGAP4D

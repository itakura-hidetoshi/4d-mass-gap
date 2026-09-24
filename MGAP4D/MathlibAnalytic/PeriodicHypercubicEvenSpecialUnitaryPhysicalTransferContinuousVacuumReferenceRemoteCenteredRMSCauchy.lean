import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemoteConditionalCrossRatioInfluence
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCrossRatioCenteredRMS
import Mathlib.Tactic

/-!
# Centered RMS transport for remote physical one-link laws

The remote physical influence spine already identifies two source-updated
one-link reference laws with normalized Doob laws over one common raw one-slab
measure and proves the exact all-pairs vacuum cross-ratio estimate.

The generic Doob theorem from PR #4708 converts those same receipts into a
centered RMS comparison with the identical targetwise worst-case transformed
cross-ratio majorant.  No bounded-test radius, square-root loss in the
influence coefficient, or new matrix coefficient is introduced.

This theorem keeps the strict majorant bound M < 2 and the first/second moment
integrability receipts explicit.  High-temperature discharge of M < 2 and the
bounded-concrete automatic moment wrapper are separate theorem units.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance remoteCenteredRMSSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance remoteCenteredRMSSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance remoteCenteredRMSSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance remoteCenteredRMSSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteCenteredRMSSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- For a geometrically remote source/background update, the actual
continuous-vacuum one-link reference laws satisfy centered RMS transport with
exactly the existing targetwise worst-case cross-ratio influence majorant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_centered_integral_sub_abs_le_worstCaseCrossRatioInfluenceMajorant_mul_sqrt_energy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiberTarget : fiber ≠ distinguishedTarget) (hBackgroundFiberDistinct : backgroundFiber ≠ fiber)
    (hNoShare : ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H fiber backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) (hX : StronglyMeasurable X) (center : ℝ)
    (hMajorantLtTwo :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant H N hN beta hbeta A fiber backgroundFiber < 2)
    (hFirstU : Integrable (fun g => X g - center)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ (Function.update A backgroundFiber u)))
    (hFirstV : Integrable (fun g => X g - center)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ (Function.update A backgroundFiber v)))
    (hEnergyU : Integrable (fun g => (X g - center) ^ 2)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ (Function.update A backgroundFiber u)))
    (hEnergyV : Integrable (fun g => (X g - center) ^ 2)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ (Function.update A backgroundFiber v))) :
    |(∫ g, X g - center ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ (Function.update A backgroundFiber u)) -
      (∫ g, X g - center ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ (Function.update A backgroundFiber v))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant H N hN beta hbeta A fiber backgroundFiber *
        Real.sqrt ((∫ g, (X g - center) ^ 2 ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ (Function.update A backgroundFiber u)) +
          ∫ g, (X g - center) ^ 2 ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ (Function.update A backgroundFiber v)) := by
  classical
  have hPair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_pair_eq_commonRaw_vacuumDoob
      H N hN beta hbeta B
      distinguishedTarget distinguishedSource fiber backgroundFiber
      hFiberTarget hBackgroundFiberDistinct hNoShare
      k g₂ u v A
  rw [hPair.1, hPair.2] at hFirstU hFirstV hEnergyU hEnergyV ⊢

  let C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B distinguishedSource k
  let μ : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
      H N beta C A fiber
  let w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta (Function.update A backgroundFiber u) fiber
  let vWeight : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta (Function.update A backgroundFiber v) fiber
  let radius :
      Matrix.specialUnitaryGroup (Fin N) ℂ →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun x y =>
      Real.log
        (1 + Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta A fiber backgroundFiber x y u v)
  let M : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta A fiber backgroundFiber
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure_isProbabilityMeasure
      H N hN beta hbeta C A fiber
  let dW :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
      H N hN beta hbeta μ (Function.update A backgroundFiber u) fiber
  let dV :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
      H N hN beta hbeta μ (Function.update A backgroundFiber v) fiber

  have hMNonneg : 0 ≤ M := by
    have hChosenNonneg :
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
            H N hN beta hbeta A fiber backgroundFiber 1 1 1 1 := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
      exact
        finitePositiveWeightCrossRatioInfluenceTransform_nonneg _
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioRadius_nonneg
            H N hN beta hbeta A fiber backgroundFiber 1 1 1 1)
    have hChosenLe :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant_le_worstCase
        H N hN beta hbeta A fiber backgroundFiber 1 1 1 1
    exact hChosenNonneg.trans (by simpa [M] using hChosenLe)

  have hRadiusNonneg : ∀ x y, 0 ≤ radius x y := by
    intro x y
    simpa [radius] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioRadius_nonneg
        H N hN beta hbeta A fiber backgroundFiber x y u v
  have hInfluence : ∀ x y,
      finitePositiveWeightCrossRatioInfluenceTransform (radius x y) ≤ M := by
    intro x y
    simpa [
      radius,
      M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant_le_worstCase
        H N hN beta hbeta A fiber backgroundFiber x y u v

  have hwMeas : Measurable w := by
    dsimp [w]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight_continuous
        H N hN beta hbeta (Function.update A backgroundFiber u) fiber).measurable
  have hvMeas : Measurable vWeight := by
    dsimp [vWeight]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight_continuous
        H N hN beta hbeta (Function.update A backgroundFiber v) fiber).measurable

  have hwtop : ∀ x, w x ≠ ∞ := by
    intro x
    have hx : w x ≤ dW.M := by
      simpa [w, dW] using dW.upper x
    exact ne_of_lt (lt_of_le_of_lt hx dW.upper_finite)
  have hvtop : ∀ x, vWeight x ≠ ∞ := by
    intro x
    have hx : vWeight x ≤ dV.M := by
      simpa [vWeight, dV] using dV.upper x
    exact ne_of_lt (lt_of_le_of_lt hx dV.upper_finite)

  have hMassW0 : doobWeightMass μ w ≠ 0 := by
    have hLower : dW.m ≤ doobWeightMass μ w := by
      apply doobWeightMass_lower_bound
      intro x
      simpa [w, dW] using dW.lower x
    exact ne_of_gt (lt_of_lt_of_le dW.lower_pos hLower)
  have hMassWtop : doobWeightMass μ w ≠ ∞ := by
    have hUpper : doobWeightMass μ w ≤ dW.M := by
      apply doobWeightMass_upper_bound
      intro x
      simpa [w, dW] using dW.upper x
    exact ne_of_lt (lt_of_le_of_lt hUpper dW.upper_finite)
  have hMassV0 : doobWeightMass μ vWeight ≠ 0 := by
    have hLower : dV.m ≤ doobWeightMass μ vWeight := by
      apply doobWeightMass_lower_bound
      intro x
      simpa [vWeight, dV] using dV.lower x
    exact ne_of_gt (lt_of_lt_of_le dV.lower_pos hLower)
  have hMassVtop : doobWeightMass μ vWeight ≠ ∞ := by
    have hUpper : doobWeightMass μ vWeight ≤ dV.M := by
      apply doobWeightMass_upper_bound
      intro x
      simpa [vWeight, dV] using dV.upper x
    exact ne_of_lt (lt_of_le_of_lt hUpper dV.upper_finite)

  have hcross : ∀ x y,
      w x * vWeight y ≤
        ENNReal.ofReal (Real.exp (radius x y)) * vWeight x * w y := by
    intro x y
    let omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    let a : ℝ :=
      omega (Function.update (Function.update A backgroundFiber u) fiber x)
    let b : ℝ :=
      omega (Function.update (Function.update A backgroundFiber v) fiber y)
    let c : ℝ :=
      omega (Function.update (Function.update A backgroundFiber v) fiber x)
    let d : ℝ :=
      omega (Function.update (Function.update A backgroundFiber u) fiber y)
    have ha : 0 < a := by
      simpa [a, omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta
          (Function.update (Function.update A backgroundFiber u) fiber x)
    have hb : 0 < b := by
      simpa [b, omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta
          (Function.update (Function.update A backgroundFiber v) fiber y)
    have hc : 0 < c := by
      simpa [c, omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta
          (Function.update (Function.update A backgroundFiber v) fiber x)
    have hd : 0 < d := by
      simpa [d, omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta
          (Function.update (Function.update A backgroundFiber u) fiber y)
    have hRatio :
        a * b / (c * d) ≤ Real.exp (radius x y) := by
      simpa [a, b, c, d, omega, radius] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_le_exp_log_one_add_exp_sixteen_mul_fixedRightTargetRatioResponseAbs
          H N hN beta hbeta A hBackgroundFiberDistinct.symm hNoShare u v x y
    have hMul :
        a * b ≤ Real.exp (radius x y) * (c * d) :=
      (div_le_iff₀ (mul_pos hc hd)).mp hRatio
    have hENN :
        ENNReal.ofReal a * ENNReal.ofReal b ≤
          ENNReal.ofReal (Real.exp (radius x y)) *
            ENNReal.ofReal c * ENNReal.ofReal d := by
      calc
        ENNReal.ofReal a * ENNReal.ofReal b =
            ENNReal.ofReal (a * b) := by
              rw [ENNReal.ofReal_mul ha.le]
        _ ≤ ENNReal.ofReal (Real.exp (radius x y) * (c * d)) :=
          ENNReal.ofReal_le_ofReal hMul
        _ = ENNReal.ofReal (Real.exp (radius x y)) *
              ENNReal.ofReal c * ENNReal.ofReal d := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          rw [ENNReal.ofReal_mul hc.le]
          ac_rfl
    simpa [
      w,
      vWeight,
      a,
      b,
      c,
      d,
      omega,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using hENN

  have hDoob :=
    HaarLikelihoodRatioInfluence.doobWeightedMeasure_centered_integral_sub_abs_le_crossRatioInfluenceMajorant_mul_sqrt_energy
      μ w vWeight hwMeas hvMeas radius M hMNonneg
      (by simpa [M] using hMajorantLtTwo)
      hRadiusNonneg hInfluence hwtop hvtop
      hMassW0 hMassWtop hMassV0 hMassVtop hcross
      X hX center
      (by simpa [μ, w, C] using hFirstU)
      (by simpa [μ, vWeight, C] using hFirstV)
      (by simpa [μ, w, C] using hEnergyU)
      (by simpa [μ, vWeight, C] using hEnergyV)
  simpa [μ, w, vWeight, M, C] using hDoob

end

end MGAP4D.MathlibAnalytic

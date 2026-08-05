import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelStrictFiniteResponseAsymptotic
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorCanonicalEnvelopeKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForAsymptoticBootstrap
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

/-- Volume-independent asymptotic Perron bootstrap map obtained after sending
the finite random-scan terminal residual to zero. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap
    (β energyIdentity energyNontrivial coefficient : ℝ) : ℝ :=
  let ratio :=
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
  let sourceMagnitude := ratio - ratio⁻¹
  2 * finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
      β energyIdentity energyNontrivial +
    ratio *
      finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
        coefficient
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
          β energyIdentity energyNontrivial)
        sourceMagnitude

/-- The asymptotic Perron bootstrap map is nonnegative on a nonnegative strict
coefficient. -/
theorem finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap_nonneg
    (β energyIdentity energyNontrivial coefficient : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hCoefficientLtOne : coefficient < 1) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap
      β energyIdentity energyNontrivial coefficient := by
  let ratio :=
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
  let sourceMagnitude := ratio - ratio⁻¹
  have hRatio : 0 ≤ ratio :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  have hSourceMagnitude : 0 ≤ sourceMagnitude := by
    simpa [sourceMagnitude, ratio] using
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltAmplitude_nonneg
        β energyIdentity energyNontrivial hβ hEnergy
  have hOneSub : 0 ≤ (1 - coefficient)⁻¹ :=
    inv_nonneg.mpr (by linarith)
  unfold finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap
    finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient_nonneg
        β energyIdentity energyNontrivial hβ.le hEnergy.le))
    (mul_nonneg hRatio
      (mul_nonneg
        (mul_nonneg
          (finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceAmplitude_nonneg
            β energyIdentity energyNontrivial hβ hEnergy)
          hSourceMagnitude)
        hOneSub))

/-- At every finite side, a strict asymptotic Perron bootstrap margin is
realized by a finite response depth. -/
theorem exists_finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap_lt
    (H : ℕ)
    (β energyIdentity energyNontrivial coefficient bound : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hCoefficientLtOne : coefficient < 1)
    (hAsymptotic :
      finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap
        β energyIdentity energyNontrivial coefficient < bound) :
    ∃ responseIterations : ℕ,
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        responseIterations coefficient < bound := by
  let ratio :=
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
  let envelopeMagnitude :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
      β energyIdentity energyNontrivial
  let sourceMagnitude := ratio - ratio⁻¹
  let local :=
    2 * finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
      β energyIdentity energyNontrivial
  let responseBound := (bound - local) / ratio
  have hCard :
      0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
    Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (FiniteEvenFourTorusSpatialLink H))
  have hRatioPos : 0 < ratio := by
    exact finiteZ2CrossingLikelihoodRatio_pos
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
  have hEnvelopeMagnitude : 0 ≤ envelopeMagnitude := by
    exact finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceAmplitude_nonneg
      β energyIdentity energyNontrivial hβ hEnergy
  have hSourceMagnitude : 0 ≤ sourceMagnitude := by
    simpa [sourceMagnitude, ratio] using
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltAmplitude_nonneg
        β energyIdentity energyNontrivial hβ hEnergy
  have hResponseAsymptotic :
      finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
          coefficient envelopeMagnitude sourceMagnitude < responseBound := by
    apply (lt_div_iff₀ hRatioPos).2
    have hAsymptotic' :
        local + ratio *
            finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
              coefficient envelopeMagnitude sourceMagnitude < bound := by
      simpa [finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap,
        local, ratio, envelopeMagnitude, sourceMagnitude] using hAsymptotic
    linarith
  obtain ⟨responseIterations, hResponse⟩ :=
    exists_finiteInfluenceKernelBidirectionalFiniteResponseCoefficient_lt
      hCard hCoefficientNonneg hCoefficientLtOne
      hEnvelopeMagnitude hSourceMagnitude hResponseAsymptotic
  refine ⟨responseIterations, ?_⟩
  have hScaled :
      ratio *
          finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
            (FiniteEvenFourTorusSpatialLink H)
            responseIterations coefficient envelopeMagnitude sourceMagnitude <
        ratio * responseBound :=
    mul_lt_mul_of_pos_left hResponse hRatioPos
  have hBoundIdentity : local + ratio * responseBound = bound := by
    unfold responseBound
    field_simp [ne_of_gt hRatioPos]
    ring
  unfold finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
    finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
  change local + ratio *
      finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
        (FiniteEvenFourTorusSpatialLink H)
        responseIterations coefficient envelopeMagnitude sourceMagnitude < bound
  calc
    local + ratio *
        finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
          (FiniteEvenFourTorusSpatialLink H)
          responseIterations coefficient envelopeMagnitude sourceMagnitude <
      local + ratio * responseBound := add_lt_add_left hScaled local
    _ = bound := hBoundIdentity

/-- A volume-independent strict asymptotic barrier, together with its physical
nonnegativity data. -/
structure Z2PerronPosteriorAsymptoticBarrierData
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  barrier : ℝ
  barrier_nonneg : 0 ≤ barrier
  barrier_lt_one : barrier < 1
  asymptoticBootstrapMap_lt :
    finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap
      β energyIdentity energyNontrivial barrier < barrier

namespace Z2PerronPosteriorAsymptoticBarrierData

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorAsymptoticBarrierData
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Every finite side admits a finite response depth sending the exact finite
bootstrap map strictly inside the common barrier. -/
theorem exists_responseIterations
    (H : ℕ) :
    ∃ responseIterations : ℕ,
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        responseIterations C.barrier < C.barrier :=
  exists_finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap_lt
    H β energyIdentity energyNontrivial C.barrier C.barrier
    hβ hEnergy C.barrier_nonneg C.barrier_lt_one
    C.asymptoticBootstrapMap_lt

/-- A canonical finite response depth at each finite side. -/
noncomputable def responseIterations
    (H : ℕ) : ℕ :=
  Classical.choose (C.exists_responseIterations H)

/-- The selected finite response depth realizes the strict barrier. -/
theorem bootstrapMap_barrier_lt
    (H : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        (C.responseIterations H) C.barrier < C.barrier :=
  Classical.choose_spec (C.exists_responseIterations H)

/-- Non-strict form consumed by the persistent barrier package. -/
theorem bootstrapMap_barrier_le
    (H : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        (C.responseIterations H) C.barrier ≤ C.barrier :=
  le_of_lt (C.bootstrapMap_barrier_lt H)

end Z2PerronPosteriorAsymptoticBarrierData

end

end MathlibAnalytic
end MGAP4D
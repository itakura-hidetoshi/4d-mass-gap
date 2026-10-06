import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorSpatialDecayDobrushinBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberRemoteLocalZero
import Mathlib.Tactic

/-!
# Ordinary posterior response from the canonical fixed-right response envelope

The posterior Dobrushin route introduced after PR #5157 asks for the ordinary
remote response

  | E_{pi_B}[L_{B,t,g}] - E_{pi_B tilted at s}[L_{B,t,g}] |.

An older fixed-right route already proves a volume/rank independent
exponentially weighted bound for the canonical supremum of literal target-ratio
responses.  This file identifies the ordinary posterior response as the
special fixed-right response obtained by choosing

  g₂ = B(target),   k = B(source).

For a remote source, the exact target local factor is unchanged by the source
update.  Therefore the fixed-right ratio observable reduces to the ordinary
target local factor and its two kernel-section expectations are exactly the
base and source-updated vacuum ratios.

Combining this bridge with the existing canonical bootstrap envelope yields the
actual ordinary posterior response bound

  epsilon(t,s) <= Mbar(s,beta) / s^d_baseL1(t,s),

where Mbar is the volume-independent half-barrier bootstrap map and vanishes at
beta = 0.  No posterior self-influence iteration is used, so there is no
circular use of the remote response being bounded.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance posteriorCanonicalFixedRightResponseBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorCanonicalFixedRightResponseBridgeSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) := by
  refine ⟨
    (⟨(0 : PeriodicHypercubicEvenVertex H), by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
      ⟨(1 : PeriodicHypercubicAxis), by decide⟩)⟩

local instance posteriorCanonicalFixedRightResponseBridgeTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorCanonicalFixedRightResponseBridgeCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorCanonicalFixedRightResponseBridgeSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorCanonicalFixedRightResponseBridgeMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorCanonicalFixedRightResponseBridgeBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Updating a right-boundary link by its current value gives unit local
Boltzmann factor. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_self
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target (B target) = 1 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
  simp

/-- The ordinary posterior expectation response is the special literal
fixed-right target-ratio response with the denominator and reference source
values chosen from the current boundary configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_expectationResponseAbs_eq_fixedRightTargetRatioResponseAbs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
          H N hN beta hbeta B target g -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
          H N hN beta hbeta B target source sourceValue g| =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN beta hbeta B target source g (B target) sourceValue (B source) := by
  classical
  let Bs : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B source sourceValue
  have hBsTarget : Bs target = B target := by
    simp [Bs, Ne.symm hNe]
  have hUpdateSourceTarget :
      Function.update Bs target (B target) = Bs := by
    funext e
    by_cases he : e = target
    · subst e
      simp [hBsTarget]
    · simp [he]
  have hUpdateBase :
      Function.update (Function.update B source (B source)) target (B target) = B := by
    funext e
    by_cases heSource : e = source
    · subst e
      simp [hNe]
    · by_cases heTarget : e = target
      · subst e
        simp [Ne.symm hNe]
      · simp [heSource, heTarget]
  have hRemoteFactor :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A Bs target g := by
    intro A
    symm
    simpa [Bs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_source_eq_of_not_plaquetteLocal
        H N beta A B target source sourceValue hNe hRemote g
  have hFirst :
      (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target (B target)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source sourceValue) target (B target))) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
          H N hN beta hbeta B target source sourceValue g := by
    rw [show
      Function.update (Function.update B source sourceValue) target (B target) = Bs by
        simpa [Bs] using hUpdateSourceTarget]
    simp_rw [
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_self,
      div_one,
      hRemoteFactor]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_rightTargetLocalFactor_eq_vacuum_update_ratio]
    symm
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_eq_updated_vacuum_ratio
        H N hN beta hbeta B target source sourceValue g hNe hRemote
  have hSecond :
      (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target (B target)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source (B source)) target (B target))) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
          H N hN beta hbeta B target g := by
    rw [hUpdateBase]
    simp_rw [
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_self,
      div_one]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_rightTargetLocalFactor_eq_vacuum_update_ratio]
    symm
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_eq_vacuum_ratio
        H N hN beta hbeta B target g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
  rw [hFirst, hSecond, abs_sub_comm]

/-- The canonical actual response profile is bounded by the volume-independent
bootstrap envelope divided by the source-centered exponential weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_halfBarrierBootstrapMap_div_exponentialWeight
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s source target := by
  classical
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s source
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
      H N hN beta hbeta s source
  have hWeightNonneg : ∀ x, 0 ≤ W x := fun x =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
      H s (zero_lt_one.trans_le hs).le source x
  have hWeightPos : 0 < W target :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
      H s (zero_lt_one.trans_le hs) source target
  have hEntry :
      R target source * W target ≤
        ∑ x : PeriodicHypercubicEvenSpatialSliceLink H, R x source * W x :=
    Finset.single_le_sum
      (fun x _ =>
        mul_nonneg
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta x source)
          (hWeightNonneg x))
      (Finset.mem_univ target)
  have hColumn :
      (∑ x : PeriodicHypercubicEvenSpatialSliceLink H, R x source * W x) ≤
        M * W source := by
    simpa [R, W, M] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_exponentialWeightedColumnBound_exactCoefficient
        H N hN beta hbeta s hs source source)
  have hSelf : W source = 1 := by
    simp [W]
  have hPointMul : R target source * W target ≤ M := by
    calc
      R target source * W target ≤
          ∑ x : PeriodicHypercubicEvenSpatialSliceLink H, R x source * W x :=
        hEntry
      _ ≤ M * W source := hColumn
      _ = M := by rw [hSelf, mul_one]
  have hM :
      M ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_le_halfBarrierBootstrapMap
        H N hN s hs source beta hbeta hcut
  apply (le_div_iff₀ hWeightPos).2
  exact hPointMul.trans hM

/-- The actual ordinary remote posterior expectation response inherits the
volume-independent canonical exponential envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectationResponseBound_of_canonicalFixedRightBootstrapEnvelope
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
      H N hN beta hbeta B target source sourceValue
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s source target) := by
  intro g
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_expectationResponseAbs_eq_fixedRightTargetRatioResponseAbs
      H N hN beta hbeta B target source sourceValue g hNe hRemote]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_canonicalProfile
      H N hN beta hbeta B target source g (B target) sourceValue (B source)).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_halfBarrierBootstrapMap_div_exponentialWeight
        H N hN s hs beta hbeta hcut target source)


/-- On the canonical half-barrier interval, the volume-independent bootstrap
response envelope is nonnegative.  This is inherited from the nonnegative
actual weighted response coefficient together with its bootstrap-envelope
upper bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s beta := by
  let center : PeriodicHypercubicEvenSpatialSliceLink H :=
    Classical.choice
      (inferInstance : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H))
  have hActual :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
          H N hN beta hbeta s center :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_nonneg
      H N hN beta hbeta s hs center
  have hUpper :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
          H N hN beta hbeta s center ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_le_halfBarrierBootstrapMap
      H N hN s hs center beta hbeta hcut
  exact hActual.trans hUpper

/-- The canonical fixed-right bootstrap envelope supplies an actual ordinary
posterior remote-response matrix.  The response radius is source-centered
base-L1 exponential decay and is independent of the boundary configuration. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
      H N hN beta hbeta := by
  let Mbar :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
      s beta
  let W :=
    fun source target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s source target
  refine
    { epsilon := fun target source => Mbar / W source target
      epsilon_nonneg := ?_
      remote_response := ?_ }
  · intro target source
    have hMbar : 0 ≤ Mbar := by
      simpa [Mbar] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap_nonneg
          H N hN s hs beta hbeta hcut
    have hWPos : 0 < W source target := by
      simpa [W] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
          H s (zero_lt_one.trans_le hs) source target
    exact div_nonneg hMbar hWPos.le
  · intro A C target source hNe hRemote _hAgree
    simpa [Mbar, W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectationResponseBound_of_canonicalFixedRightBootstrapEnvelope
        H N hN s hs beta hbeta hcut A target source (C source) hNe hRemote

end

end MathlibAnalytic
end MGAP4D

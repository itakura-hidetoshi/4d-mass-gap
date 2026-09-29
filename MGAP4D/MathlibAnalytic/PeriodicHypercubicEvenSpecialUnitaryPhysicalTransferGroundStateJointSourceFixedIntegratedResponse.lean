import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedDirectCancellation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseResidualCoefficient
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferVacuumSecondMeanRMSTargetMajorant
import Mathlib.Tactic

/-!
# Ordered, vacuum-integrated response for source-fixed representatives

The fixed-background response and RMS estimates are already proved. We retain
one ordered pair, integrate its exact source-pair norm square over the vacuum,
and charge it to the genuine target conditional-expectation residual. The
coefficient is ofReal(K_pin(target,source)^2) times the existing RMS coefficient.
It is finite on the existing strict physical-sweep interval; no stronger shell
cutoff, pointwise RMS majorant, or source/target symmetry is needed.

For the single source-invariant representative from #4925, #4926 identifies
fullDifferenceL2 with responseL2 exactly. The same integrated estimate therefore
holds for the full difference of the actual source update, simultaneously for
all off-diagonal targets and distinguished-source choices.

The numerator remains a vacuum-integrated source-pair norm. Its identification
with the genuine joint-L2 source-fixed leakage, physical-envelope domination,
terminal recurrence and strict renewal contraction are separate obligations.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance sourceFixedIntegratedIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance sourceFixedIntegratedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance sourceFixedIntegratedSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance sourceFixedIntegratedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance sourceFixedIntegratedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance sourceFixedIntegratedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- Ordered response-energy coefficient, independent of outer boundary and
observable. The literal kernel entry is target,source, not its reversal. -/
def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
    (H N : ℕ) (hN : 0 < N) (s beta : ℝ) (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞ :=
  ENNReal.ofReal
      (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source) ^ 2) *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
      s beta

/-- The ordered coefficient is finite on the existing strict-sweep cutoff. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient_ne_top
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
      H N hN s beta hbeta source target ≠ ⊤ := by
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient_ne_top
      s hs beta hbeta hcut)

/-- Integrate one exact ordered response without replacing its kernel entry
by a row sum. The target energy becomes the canonical genuine fiber variance. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_vacuum_norm_sq_le_orderedCoefficient_mul_canonicalVariance
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C, ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
        H N hN s beta hbeta source target *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
  let coefficient :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
      H N hN s beta hbeta source target
  let energy := fun C =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
      H N hN beta hbeta C target F
  have hFinite : coefficient ≠ ⊤ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient_ne_top
      N hN s hs beta hbeta hcut H source target
  have hPoint : ∀ C, ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2) ≤
      coefficient * energy C := by
    intro C
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeEnergy_le_canonicalPinFree_sq_mul_targetMajorant_of_ne
        N hN s hs beta hbeta hcut H C distinguishedSource source target hne F hF bound hbound
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeEnergy_eq_fullResponseL2_norm_sq_ofReal
        H N hN beta hbeta C distinguishedSource source target F hF bound hbound,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant_eq_coefficient_mul_targetResidualEnergy
        H N hN s beta hbeta C target F] at h
    simpa only [coefficient, energy,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient,
      mul_assoc] using h
  calc
    (∫⁻ C, ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
      ∫⁻ C, coefficient * energy C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta := lintegral_mono hPoint
    _ = coefficient * (∫⁻ C, energy C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) :=
      lintegral_const_mul' coefficient energy hFinite
    _ = coefficient *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
        H N hN beta hbeta target F hF bound hbound]

/-- The sole observable-dependent right-hand side is a genuine joint-L2
target residual. No pointwise RMS-majorant hypothesis is required. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C, ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
        H N hN s beta hbeta source target * ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta F hF bound hbound -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_vacuum_norm_sq_le_orderedCoefficient_mul_canonicalVariance
      N hN s hs beta hbeta hcut H distinguishedSource source target hne F hF bound hbound
  have hVariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
      H N hN beta hbeta target F hF bound hbound
  exact hResponse.trans (mul_le_mul' le_rfl hVariance)

/-- Source invariance cancels the direct term before integration. The full
source-pair difference inherits the same ordered genuine-target bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
      F (left, Function.update right source value) = F (left, right)) :
    (∫⁻ C, ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
        H N hN s beta hbeta source target * ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta F hF bound hbound -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  have hEnergy :
      (∫⁻ C, ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) =
      (∫⁻ C, ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) := by
    apply lintegral_congr
    intro C
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_eq_responseL2_of_sourceInvariant
      H N hN beta hbeta C distinguishedSource source target hne
      (C distinguishedSource) (C source) F hF bound hbound hInvariant C 0]
  rw [hEnergy]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual
      N hN s hs beta hbeta hcut H distinguishedSource source target hne F hF bound hbound

/-- One representative of the actual source update has the integrated estimate
for every off-diagonal target. Its selection precedes both target and
auxiliary distinguished source; the right-hand residual is the actual update. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_representative_integratedResponse
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta) :
    ∃ (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta source f ∧
      (∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (left, Function.update right source value) = F (left, right)) ∧
      ∀ (distinguishedSource target : PeriodicHypercubicEvenSpatialSliceLink H),
        target ≠ source →
        (∫⁻ C, ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
            H N hN s beta hbeta source target * ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta source f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta source f)‖ ^ 2) := by
  obtain ⟨F, hF, bound, hbound, hRep, hInvariant⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_sourceInvariant_representative
      H N hN beta hbeta source f hf
  refine ⟨F, hF, bound, hbound, hRep, hInvariant, ?_⟩
  intro distinguishedSource target hne
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
      N hN s hs beta hbeta hcut H distinguishedSource source target hne F hF bound hbound hInvariant
  simpa only [hRep] using h

end

end MGAP4D.MathlibAnalytic

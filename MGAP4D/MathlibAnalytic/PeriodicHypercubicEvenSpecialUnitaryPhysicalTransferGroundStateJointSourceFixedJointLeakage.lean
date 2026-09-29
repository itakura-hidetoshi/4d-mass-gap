import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalMeanCondExpIdentification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedPairVariance
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

/-!
# The actual stationary source residual is the genuine joint leakage norm

#4930 identifies the actual source conditional variance with its stationary
fixed-boundary residual. #4931 identifies the canonical mean with the genuine
joint CondExpL2. We connect these facts using the already-proved nested a.e.
mean identity and exact source heat-bath stationarity. In particular, a.e.
equality is transported through source resampling, not asserted pointwise.

The resulting numerator identity holds for all bounded strongly measurable
inputs and every beta >= 0, including equal source and target. Source
invariance, distinct links and the existing cutoff are used only to compose
with the ordered response bound. No operator commutativity, different-carrier
identification or new comparison factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory GroundStateCanonicalMean
open scoped ENNReal ProbabilityTheory

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStateSourceFixedPairEnergy

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Joint" => Cfg × Cfg
local notation "νV" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta
local notation "μC" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "embed" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta

/-- The canonical joint mean and the literal fixed-boundary mean agree under
exactly the physical vacuum / section disintegration. -/
theorem canonicalMean_ae_eq_targetMean (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    ∀ᵐ C ∂νV, (fun A => canonicalMean H N hN beta hbeta target F (C, A)) =ᵐ[μC C]
      targetMean H N hN beta hbeta target F C := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_vacuum_kernelSection
      H N hN beta hbeta target target F hF
  filter_upwards [h] with C hC
  filter_upwards [hC] with A hA
  have hX : StronglyMeasurable (fun D : Cfg => F (C, D)) :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hProj :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta C A target target (fun D => F (C, D)) hX
  change F (C, A) - canonicalMean H N hN beta hbeta target F (C, A) =
    F (C, A) - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
      H N hN beta hbeta C target target target (C target) (C target)
      (fun D => F (C, D)) A at hA
  rw [hProj] at hA
  change F (C, A) - canonicalMean H N hN beta hbeta target F (C, A) =
    F (C, A) - targetMean H N hN beta hbeta target F C A at hA
  linarith

/-- Stationarity transports a.e. equality through the actual source update.
The source projection is never applied pointwise to an arbitrary L2 class. -/
theorem sourceProjection_congr_ae (C : Cfg) (source : Link)
    (U V : Cfg → ℝ) (hUV : U =ᵐ[μC C] V) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta C source source source (C source) (C source) U =ᵐ[μC C]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta C source source source (C source) (C source) V := by
  let κ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
    H N hN beta hbeta C source source source (C source) (C source)
  have hStationary : κ ∘ₘ μC C = μC C := by
    simpa only [κ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_comp_referenceProbabilityMeasure
        H N hN beta hbeta C source source source (C source) (C source)
  have hComp : U =ᵐ[κ ∘ₘ μC C] V := by
    rw [hStationary]
    exact hUV
  have hNested := Measure.ae_ae_of_ae_comp hComp
  filter_upwards [hNested] with A hA
  exact integral_congr_ae hA

/-- The actual source projection of the literal target mean agrees a.e. with
the canonical source mean of the canonical target mean. No order swap occurs. -/
theorem sourceProjectedTargetMean_ae_eq_canonicalDoubleMean (source target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    ∀ᵐ C ∂νV, sourceProjectedTargetMean H N hN beta hbeta source target F C =ᵐ[μC C]
      (fun A => canonicalMean H N hN beta hbeta source
        (canonicalMean H N hN beta hbeta target F) (C, A)) := by
  let G := canonicalMean H N hN beta hbeta target F
  have hG : StronglyMeasurable G :=
    canonicalMean_stronglyMeasurable H N hN beta hbeta target F hF
  have ht := canonicalMean_ae_eq_targetMean H N hN beta hbeta target F hF
  have hd := canonicalMean_ae_eq_targetMean H N hN beta hbeta source G hG
  filter_upwards [ht, hd] with C hTarget hSource
  have hProjected := sourceProjection_congr_ae H N hN beta hbeta C source
    (targetMean H N hN beta hbeta target F C) (fun A => G (C, A)) hTarget.symm
  filter_upwards [hProjected, hSource] with A hProj hMean
  have hGC : StronglyMeasurable (fun D : Cfg => G (C, D)) :=
    hG.comp_measurable (measurable_const.prodMk measurable_id)
  calc
    sourceProjectedTargetMean H N hN beta hbeta source target F C A =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
          H N hN beta hbeta C source source source (C source) (C source)
          (fun D => G (C, D)) A := hProj
    _ = targetMean H N hN beta hbeta source G C A :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_diagonalCurrentValues_eq_kernelSectionSpatialLinkIntegral
        H N hN beta hbeta C A source source source (fun D => G (C, D)) hGC
    _ = canonicalMean H N hN beta hbeta source G (C, A) := hMean.symm

/-- The missing numerator bridge: vacuum-averaged actual stationary source
residual equals the genuine JOINT double-projection leakage norm squared. -/
theorem fixedBoundaryLeakageEnergy_vacuum_eq_jointLeakageNormSq (source target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C, fixedBoundaryLeakageEnergy H N hN beta hbeta source target F C ∂νV) =
      ENNReal.ofReal (‖P target (embed F hF bound hbound) -
        P source (P target (embed F hF bound hbound))‖ ^ 2) := by
  let G := canonicalMean H N hN beta hbeta target F
  let hG := canonicalMean_stronglyMeasurable H N hN beta hbeta target F hF
  let hGb := canonicalMean_norm_le H N hN beta hbeta target F bound hbound
  let g := embed G hG bound hGb
  have hg : g = P target (embed F hF bound hbound) :=
    canonicalMeanL2_eq_condExpL2 H N hN beta hbeta target F hF bound hbound
  have hEnergy :
      (∫⁻ C, fixedBoundaryLeakageEnergy H N hN beta hbeta source target F C ∂νV) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta source G := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_vacuum_kernelSection_canonicalFiberMean_residual_lintegral
      H N hN beta hbeta source G hG]
    apply lintegral_congr_ae
    filter_upwards [canonicalMean_ae_eq_targetMean H N hN beta hbeta target F hF,
      sourceProjectedTargetMean_ae_eq_canonicalDoubleMean H N hN beta hbeta source target F hF]
      with C hM hQ
    unfold fixedBoundaryLeakageEnergy
    apply lintegral_congr_ae
    filter_upwards [hM, hQ] with A hMA hQA
    change ENNReal.ofReal
      ((targetMean H N hN beta hbeta target F C A -
        sourceProjectedTargetMean H N hN beta hbeta source target F C A) ^ 2) =
      ENNReal.ofReal ((G (C, A) - canonicalMean H N hN beta hbeta source G (C, A)) ^ 2)
    rw [← hMA, hQA]
  rw [hEnergy,
    canonicalVariance_eq_condExpResidualNormSq H N hN beta hbeta source G hG bound hGb]
  change ENNReal.ofReal (‖g - P source g‖ ^ 2) = _
  rw [hg]

/-- The established ordered coefficient now bounds the genuine joint leakage,
with exactly half the pair-energy coefficient, on source-invariant inputs. -/
theorem jointLeakage_norm_sq_le_half_orderedCoefficient_of_sourceInvariant
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source target : Link) (hne : target ≠ source)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : Cfg) (value : Gauge),
      F (left, Function.update right source value) = F (left, right)) :
    ENNReal.ofReal (‖P target (embed F hF bound hbound) -
      P source (P target (embed F hF bound hbound))‖ ^ 2) ≤
      ((2 : ℝ≥0∞)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
          H N hN s beta hbeta source target) *
      ENNReal.ofReal (‖embed F hF bound hbound - P target (embed F hF bound hbound)‖ ^ 2) := by
  rw [← fixedBoundaryLeakageEnergy_vacuum_eq_jointLeakageNormSq
    H N hN beta hbeta source target F hF bound hbound]
  exact fixedBoundaryLeakageEnergy_vacuum_le_half_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
    H N hN beta hbeta s hs hcut source target hne F hF bound hbound hInvariant

/-- Apply the genuine bound to the actual source update of ANY vector in the
bounded concrete core. One representative is chosen before all targets. -/
theorem sourceUpdate_jointLeakage_norm_sq_le_half_orderedCoefficient
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source : Link) (f : JL2)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta) :
    ∀ target : Link, target ≠ source →
      ENNReal.ofReal (‖P target (P source f) - P source (P target (P source f))‖ ^ 2) ≤
        ((2 : ℝ≥0∞)⁻¹ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
            H N hN s beta hbeta source target) *
        ENNReal.ofReal (‖P source f - P target (P source f)‖ ^ 2) := by
  obtain ⟨F, hF, bound, hbound, hRep, hInvariant⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_sourceInvariant_representative
      H N hN beta hbeta source f hf
  intro target hne
  have h := jointLeakage_norm_sq_le_half_orderedCoefficient_of_sourceInvariant
    H N hN beta hbeta s hs hcut source target hne F hF bound hbound hInvariant
  simpa only [hRep] using h

end GroundStateSourceFixedPairEnergy

end

end MGAP4D.MathlibAnalytic

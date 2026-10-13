import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalPosteriorDensityFloorV5_FK
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Tactic

/-!
# P4-Q2-FL: ACTUAL Wilson posterior one-link measure and RMS Haar sandwich

P4-Q2-FK proves the normalized real density of the TRUE interacting
Wilson posterior link measure lies in [exp(-16 beta), exp(16 beta)]
at every physical boundary pair, selected link and finite volume.

This file promotes precisely that result to:
(1) lower and upper domination between the GENUINE conditional
    Wilson posterior measure and normalized compact SU(N) Haar;
(2) a volume-uniform lower/upper control of the actual posterior
    resampling square moment by the same square against Haar.

The Haar law appears ONLY as an analytic comparison/reference, NEVER
as a replacement for the physical conditional law. The integrand can
be FG's original signed Wilson relative-response BCF, unchanged.

These are genuine quantitative physical posterior results. No positive
all-link response frame bound, spatial decay, β-dependent continuum
mass gap, or H1-C3 closure is concluded.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2FL_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FL_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FL_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FL_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FL_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorJoint

/-- Exact original interacting Wilson one-link posterior is uniformly
minorized and majorized by normalized compact Haar probability. -/
theorem p4Q2FL_originalWilsonPosteriorConditionalMeasure_haar_sandwich
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (ENNReal.ofReal (Real.exp (-16 * beta))) •
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta left right e ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta left right e ≤
      ENNReal.ofReal (Real.exp (16 * beta)) •
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let μ : Measure G := normalizedCompactHaar G
  let L : G → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H N hN beta hbeta left right e
  let p : G → ℝ := continuousNormalizedExp μ L
  have hp : ∀ g : G,
      Real.exp (-16 * beta) ≤ p g ∧ p g ≤ Real.exp (16 * beta) := by
    intro g
    simpa [p, μ, L,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity]
      using
        p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
          H N hN beta hbeta left right e g
  have hDLower :
      (fun _ : G => ENNReal.ofReal (Real.exp (-16 * beta))) ≤ᵐ[μ]
        (fun g => ENNReal.ofReal (p g)) := by
    filter_upwards with g
    exact ENNReal.ofReal_le_ofReal (hp g).1
  have hDUpper :
      (fun g : G => ENNReal.ofReal (p g)) ≤ᵐ[μ]
        (fun _ => ENNReal.ofReal (Real.exp (16 * beta))) := by
    filter_upwards with g
    exact ENNReal.ofReal_le_ofReal (hp g).2
  have hLower :
      (ENNReal.ofReal (Real.exp (-16 * beta))) • μ ≤ μ.tilted L := by
    have h := withDensity_mono (μ := μ) hDLower
    simpa [Measure.tilted, p, continuousNormalizedExp,
      continuousExpPartition] using h
  have hUpper :
      μ.tilted L ≤ (ENNReal.ofReal (Real.exp (16 * beta))) • μ := by
    have h := withDensity_mono (μ := μ) hDUpper
    simpa [Measure.tilted, p, continuousNormalizedExp,
      continuousExpPartition] using h
  change
    (ENNReal.ofReal (Real.exp (-16 * beta))) • μ ≤ μ.tilted L ∧
      μ.tilted L ≤ (ENNReal.ofReal (Real.exp (16 * beta))) • μ
  exact ⟨hLower, hUpper⟩

/-- An arbitrary ACTUAL squared one-link response receives a uniform Haar
lower estimate, without changing its genuine Wilson posterior law. -/
theorem p4Q2FL_originalWilsonPosteriorConditionalSquaredLIntegral_haar_lower
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) :
    ENNReal.ofReal (Real.exp (-16 * beta)) *
      (∫⁻ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        ENNReal.ofReal ((X g) ^ 2)
        ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
      (∫⁻ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        ENNReal.ofReal ((X g) ^ 2)
        ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta left right e)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta left right e
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-16 * beta))
  have hLo : a • μ ≤ ν := by
    simpa [a, μ, ν] using
      (p4Q2FL_originalWilsonPosteriorConditionalMeasure_haar_sandwich
        H N hN beta hbeta left right e).1
  calc
    a * (∫⁻ g, ENNReal.ofReal ((X g) ^ 2) ∂μ) =
        ∫⁻ g, ENNReal.ofReal ((X g) ^ 2) ∂(a • μ) := by
          simpa [smul_eq_mul] using
            (lintegral_smul_measure (μ := μ) a
              (fun g => ENNReal.ofReal ((X g) ^ 2))).symm
    _ ≤ ∫⁻ g, ENNReal.ofReal ((X g) ^ 2) ∂ν :=
      lintegral_mono' hLo le_rfl

/-- Matching volume-uniform upper estimate of the ACTUAL interacting
one-link Wilson resampling square against its Haar reference. -/
theorem p4Q2FL_originalWilsonPosteriorConditionalSquaredLIntegral_haar_upper
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) :
    (∫⁻ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      ENNReal.ofReal ((X g) ^ 2)
      ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta left right e)) ≤
    ENNReal.ofReal (Real.exp (16 * beta)) *
      (∫⁻ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        ENNReal.ofReal ((X g) ^ 2)
        ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta left right e
  let A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  have hHi : ν ≤ A • μ := by
    simpa [A, μ, ν] using
      (p4Q2FL_originalWilsonPosteriorConditionalMeasure_haar_sandwich
        H N hN beta hbeta left right e).2
  calc
    (∫⁻ g, ENNReal.ofReal ((X g) ^ 2) ∂ν) ≤
        ∫⁻ g, ENNReal.ofReal ((X g) ^ 2) ∂(A • μ) :=
      lintegral_mono' hHi le_rfl
    _ = A * (∫⁻ g, ENNReal.ofReal ((X g) ^ 2) ∂μ) := by
      simpa [smul_eq_mul] using
        (lintegral_smul_measure (μ := μ) A
          (fun g => ENNReal.ofReal ((X g) ^ 2)))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FL_originalWilsonPosteriorConditionalMeasure_haar_sandwich
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FL_originalWilsonPosteriorConditionalSquaredLIntegral_haar_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FL_originalWilsonPosteriorConditionalSquaredLIntegral_haar_upper

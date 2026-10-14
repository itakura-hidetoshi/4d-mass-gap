import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalRMSRealHaarSandwichV5_FM
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalRMSSpatialSupportV5_FH
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-FT: the ORIGINAL physical link masses are Haar-comparable after outer integration

FM proves a true interacting one-link WILSON posterior squared-response
sandwich pointwise in every real pair-Haar boundary context, retaining
the LITERAL signed FF physical-source response R(e,f,z,g).
FH then defines the original true source-dependent integrated spatial
link mean m_e(f) := integral_pairHaar_z M2_Wilson(e,f,z).

Here:
1. prove the exactly corresponding Haar squared-response mean is
   pair-Haar integrable, using actual continuous FF bounded response on
   the compact genuine product and Fubini;
2. integrate FM's real physical posterior/Haar inequality in z;
3. extend the comparison to arbitrary finite sets of ORIGINAL spatial
   links without claiming an unproved geometric tail or summability.

The resulting bounds are GENUINE, pointwise in frozen beta:

  exp(-16 beta) * h_e(f) <= m_e(f) <= exp(16 beta) * h_e(f),

where h_e(f) is the PAIR-HAAR outer mean of the unchanged original FF
signed response squared against normalized Haar in the inner coordinate.
Haar is strictly an analytical comparison and does NOT replace the
genuine posterior in m_e. Every constant is independent of H,e,f,z.

No bound on sum_e h_e(f), positive-beta volume-uniform spatial
summability, nontrivial integrated frame lower floor, H1-C3 closure,
or continuum mass-gap theorem is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2FT_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FT_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FT_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FT_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FT_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorJoint

/-- Fubini-integrability of the UNCHANGED exact FF signed-response Haar
squared moment, integrated against actual pair-Haar. This is an
analytical comparison; the inner true physical Wilson posterior
remains untouched in the FG and FH quantities. -/
theorem p4Q2FT_originalWilsonSignedHaarSquaredMoment_pairHaar_integrable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Integrable
      (p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
        H N hN beta hbeta f e)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let ν : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H N hN beta hbeta f e
  have hCont : Continuous
      (fun t : Pair × Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (B t) ^ 2) :=
    B.continuous.pow 2
  have hIntegrable : Integrable
      (fun t : Pair × Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (B t) ^ 2) (μ.prod ν) :=
    hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change Integrable
    (fun z : Pair => ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      (B (z,g)) ^ 2 ∂ν) μ
  exact hIntegrable.integral_prod_left

/-- Actual source- and link-resolved pair-Haar OUTER mean of the original
signed response squared against Haar in the inner comparison coordinate. -/
noncomputable def p4Q2FT_originalWilsonSignedHaarOuterLinkMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ z, p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
    H N hN beta hbeta f e z
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N

theorem p4Q2FT_originalWilsonSignedHaarOuterLinkMean_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2FT_originalWilsonSignedHaarOuterLinkMean
      H N hN beta hbeta f e := by
  unfold p4Q2FT_originalWilsonSignedHaarOuterLinkMean
  exact integral_nonneg (fun z =>
    p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment_nonneg
      H N hN beta hbeta f e z)

/-- The actual original physical Wilson source/link conditional RMS mean,
already identified EXACTLY by FG/FH, is sandwiched by the corresponding
literal signed-response Haar mean, uniformly in physical volume H.
This is the integrated version of FM, not an invented source profile. -/
theorem p4Q2FT_originalWilsonLinkMean_real_haar_sandwich
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Real.exp (-16 * beta) *
      p4Q2FT_originalWilsonSignedHaarOuterLinkMean
        H N hN beta hbeta f e ≤
      p4Q2FH_originalWilsonConditionalRMSLinkMean
        H N hN beta hbeta f e ∧
    p4Q2FH_originalWilsonConditionalRMSLinkMean
        H N hN beta hbeta f e ≤
      Real.exp (16 * beta) *
        p4Q2FT_originalWilsonSignedHaarOuterLinkMean
          H N hN beta hbeta f e := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let M := p4Q2FG_originalWilsonRelativeResponseConditionalSquare
    H N hN beta hbeta f e
  let A := p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
    H N hN beta hbeta f e
  have hM : Integrable M μ :=
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare_pairHaar_integrable
      H N hN beta hbeta f e
  have hA : Integrable A μ :=
    p4Q2FT_originalWilsonSignedHaarSquaredMoment_pairHaar_integrable
      H N hN beta hbeta f e
  have hPoint (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      Real.exp (-16 * beta) * A z ≤ M z ∧
      M z ≤ Real.exp (16 * beta) * A z :=
    p4Q2FM_originalWilsonConditionalRMS_real_haar_sandwich
      H N hN beta hbeta f e z
  have hLow : Real.exp (-16 * beta) * (∫ z, A z ∂μ) ≤
      ∫ z, M z ∂μ := by
    calc
      Real.exp (-16 * beta) * (∫ z, A z ∂μ) =
          ∫ z, Real.exp (-16 * beta) * A z ∂μ := by
        rw [integral_const_mul]
      _ ≤ ∫ z, M z ∂μ := by
        apply integral_mono (hA.const_mul _) hM
        intro z
        exact (hPoint z).1
  have hUp : (∫ z, M z ∂μ) ≤
      Real.exp (16 * beta) * (∫ z, A z ∂μ) := by
    calc
      (∫ z, M z ∂μ) ≤
          ∫ z, Real.exp (16 * beta) * A z ∂μ := by
        apply integral_mono hM (hA.const_mul _)
        intro z
        exact (hPoint z).2
      _ = Real.exp (16 * beta) * (∫ z, A z ∂μ) := by
        rw [integral_const_mul]
  exact ⟨hLow, hUp⟩

/-- The finite source-dependent Haar link-mass profile on any selectable
set S of ORIGINAL physical spatial links, before taking any H-limit. -/
noncomputable def p4Q2FT_originalWilsonSignedHaarSpatialMass
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  S.sum (p4Q2FT_originalWilsonSignedHaarOuterLinkMean H N hN beta hbeta f)

/-- Uniform physical finite-patch Wilson/Haar comparison, on precisely
the SAME set of actual physical links and the SAME physical input f.
The issue of an H-uniform bound on the right-hand side is kept open. -/
theorem p4Q2FT_originalWilsonSpatialMass_real_haar_sandwich
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    Real.exp (-16 * beta) *
        p4Q2FT_originalWilsonSignedHaarSpatialMass H N hN beta hbeta f S ≤
      p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S ∧
    p4Q2FH_originalWilsonSpatialRMSMass H N hN beta hbeta f S ≤
      Real.exp (16 * beta) *
        p4Q2FT_originalWilsonSignedHaarSpatialMass H N hN beta hbeta f S := by
  unfold p4Q2FT_originalWilsonSignedHaarSpatialMass
    p4Q2FH_originalWilsonSpatialRMSMass
  constructor
  · calc
      Real.exp (-16 * beta) *
          S.sum (p4Q2FT_originalWilsonSignedHaarOuterLinkMean
            H N hN beta hbeta f) =
        S.sum (fun e => Real.exp (-16 * beta) *
          p4Q2FT_originalWilsonSignedHaarOuterLinkMean
            H N hN beta hbeta f e) := by
          rw [Finset.mul_sum]
      _ ≤ S.sum (p4Q2FH_originalWilsonConditionalRMSLinkMean
        H N hN beta hbeta f) := by
        apply Finset.sum_le_sum
        intro e _he
        exact (p4Q2FT_originalWilsonLinkMean_real_haar_sandwich
          H N hN beta hbeta f e).1
  · calc
      S.sum (p4Q2FH_originalWilsonConditionalRMSLinkMean
        H N hN beta hbeta f) ≤
        S.sum (fun e => Real.exp (16 * beta) *
          p4Q2FT_originalWilsonSignedHaarOuterLinkMean
            H N hN beta hbeta f e) := by
        apply Finset.sum_le_sum
        intro e _he
        exact (p4Q2FT_originalWilsonLinkMean_real_haar_sandwich
          H N hN beta hbeta f e).2
      _ = Real.exp (16 * beta) *
          S.sum (p4Q2FT_originalWilsonSignedHaarOuterLinkMean
            H N hN beta hbeta f) := by
          rw [Finset.mul_sum]

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FT_originalWilsonSignedHaarSquaredMoment_pairHaar_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FT_originalWilsonSignedHaarOuterLinkMean_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FT_originalWilsonLinkMean_real_haar_sandwich
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FT_originalWilsonSpatialMass_real_haar_sandwich

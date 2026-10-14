import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSharpExpectationGapPhysicalGramV5_GK
import Mathlib.Tactic

/-!
# P4-Q2-GL: exact genuine Wilson expectation-gap square / density-contrast variance

At beta>0 the two genuine normalized SU(2) Wilson posterior densities
selected by the identity versus pi-rotated LEFT physical boundary have
a strictly positive Haar squared distance Q_beta,e(z) (GA/FX).

GI shows that the expectation gap Delta_beta,e,f(z) of the EXACT signed
FF physical receiver response under these two ORIGINAL interacting
posterior measures is Q_beta,e(z)*alpha_beta,e,f(z), where alpha is
the original genuine physical-source contrast projection.

Hence the integrand in GJ/GK's sharp Wilson physical Gram certificate
is exactly

     Delta(z)*alpha(z) = Delta(z)^2 / Q(z).

This removes the auxiliary projection coefficient from the physical
Rayleigh LOWER estimate; it does NOT replace either Wilson posterior
with independent Haar. The denominator is the actual Wilson
density-row Haar L² squared distance and is strictly positive for
positive beta. Automatic integrability is inherited from GJ/GD,
not assumed.

The statement is proved for original individual links, finite
physical patches, arbitrary signed physical input-family Gram Rayleigh,
and actual adjacent fine-right Krylov and left-three-mode Gram matrices.
No nonzero physical source witness, frame positive constant, common
volume/coupling bound, continuum mass gap or H1-C3 closure is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 650000

local instance p4Q2GL_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GL_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GL_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GL_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GL_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

private noncomputable instance p4Q2GL_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The exact SHARP GJ physical signed expectation-gap source response
equals its observable two-posterior expectation gap squared divided
by the genuine NONZERO Wilson density-contrast Haar variance. -/
theorem p4Q2GL_originalWilsonSignedGap_projection_eq_square_div_contrast
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta (le_of_lt hbeta) f e z *
    p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H beta (le_of_lt hbeta) f e z =
    (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta (le_of_lt hbeta) f e z) ^ 2 /
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta (le_of_lt hbeta) z.2 e := by
  let Q := p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
    H beta (le_of_lt hbeta) z.2 e
  let A := p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    H beta (le_of_lt hbeta) f e z
  let D := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H beta (le_of_lt hbeta) f e z
  have hQ : 0 < Q :=
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      H beta hbeta z.2 e
  have hD : D = A * Q :=
    p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
      H beta hbeta f e z
  change D * A = D ^ 2 / Q
  rw [hD]
  field_simp [hQ.ne']

/-- The TRUE two-Wilson-posterior physical expectation-gap square over
the actual positive density-contrast variance is automatically
integrable in the original OUTER pair-Haar physical context. -/
theorem p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Integrable
      (fun z =>
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta (le_of_lt hbeta) f e z) ^ 2 /
        p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
          H beta (le_of_lt hbeta) z.2 e)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  have hG := p4Q2GJ_originalWilsonSignedGapProjection_pairHaar_integrable
    H beta hbeta f e
  convert hG using 1
  funext z
  exact (p4Q2GL_originalWilsonSignedGap_projection_eq_square_div_contrast
    H beta hbeta f e z).symm

/-- A finite original Wilson link has the exact expectation-gap /
density-row separation certificate as an OUTER pair-Haar integral. -/
noncomputable def p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ z,
    (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta hbeta f e z) ^ 2 /
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H beta hbeta z.2 e
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- The observable expectation-gap square / genuine density-distance
link mass is exactly the sharp GI/GJ signed-source projection link mean. -/
theorem p4Q2GL_originalWilsonSharpSignedGapLinkMean_eq_gapSquareDivVariance
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2GJ_originalWilsonSignedGapProjectionLinkMean
      H beta (le_of_lt hbeta) f e =
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
      H beta (le_of_lt hbeta) f e := by
  unfold p4Q2GJ_originalWilsonSignedGapProjectionLinkMean
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
  apply integral_congr_ae
  filter_upwards with z
  exact p4Q2GL_originalWilsonSignedGap_projection_eq_square_div_contrast
    H beta hbeta f e z

/-- The original FULL finite physical spatial-link patch value of
the expectation-gap square / density-contrast variance. -/
noncomputable def p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  S.sum (p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
    H beta hbeta f)

/-- On an original physical link patch the GK source-projection mass
equals exactly the physically observable two-posterior expectation-gap
square / genuine Wilson density-contrast variance mass. -/
theorem p4Q2GL_originalWilsonSharpSignedGapSpatialMass_eq_squareDivVariance
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
      H beta (le_of_lt hbeta) f S =
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H beta (le_of_lt hbeta) f S := by
  unfold p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  apply Finset.sum_congr rfl
  intro e _he
  exact p4Q2GL_originalWilsonSharpSignedGapLinkMean_eq_gapSquareDivVariance
    H beta hbeta f e

/-- ACTUAL original finite Wilson physical energy is bounded below by the
exact difference of TRUE posterior expectations squared divided by
their positive Haar L² density-row separation. No alpha is needed. -/
theorem p4Q2GL_originalPhysicalPatchEnergy_ge_gapSquareDivVariance
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta) *
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H beta (le_of_lt hbeta) f S) ≤
      p4Q2FD_originalPhysicalRestrictedLinkEnergy
        H 2 (by norm_num) beta (le_of_lt hbeta) f S := by
  have h := p4Q2GK_originalPhysicalPatchEnergy_ge_sharpSignedGapProjection
    H beta hbeta f S
  rw [p4Q2GL_originalWilsonSharpSignedGapSpatialMass_eq_squareDivVariance
    H beta hbeta f S] at h
  exact h

/-- The original Wilson finite-family signed physical Gram Rayleigh
is bounded below by a TRUE two-posterior physical expectation-gap
square / genuine density contrast L² mass, with no auxiliary alpha. -/
theorem p4Q2GL_originalWilsonPhysicalGram_rayleigh_ge_gapSquareDivVariance
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta) *
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := by
  have h := p4Q2GK_originalWilsonPhysicalGram_rayleigh_ge_sharpSignedGap
    H beta hbeta f a
  rw [p4Q2GL_originalWilsonSharpSignedGapSpatialMass_eq_squareDivVariance
    H beta hbeta (∑ i : ι, a i • f i)
    (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))] at h
  exact h

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GL_originalWilsonSignedGap_projection_eq_square_div_contrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GL_originalWilsonSharpSignedGapLinkMean_eq_gapSquareDivVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GL_originalWilsonSharpSignedGapSpatialMass_eq_squareDivVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GL_originalPhysicalPatchEnergy_ge_gapSquareDivVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GL_originalWilsonPhysicalGram_rayleigh_ge_gapSquareDivVariance

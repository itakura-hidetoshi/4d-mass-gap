import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalExpectationGapSquareContrastVarianceV5_GL
import Mathlib.Tactic

/-!
# P4-Q2-GM: exact physical signed two-Wilson-posterior detection null locus

GL established an integrable, nonnegative, true-Wilson observable
  sum_e integral Delta_(beta,e,f)(z)^2 / Q_(beta,e)(z) d(pair-Haar)(z)
that bounds the original physical Gram Rayleigh from below.
For beta>0, GA/FX prove Q(z)>0 at every actual Wilson background.

This file proves, without any source-frame or injectivity assumption,
that the observable link mass vanishes exactly when the ACTUAL signed FF
physical-source gap between two interacting Wilson posteriors vanishes
pair-Haar almost everywhere. For a genuine finite physical link patch
the null locus is precisely the simultaneous a.e. null locus at each link.

The statements are instantiated on the ORIGINAL fine-right Krylov orbit
and fine-left three-mode source families, keeping beta(n+1) in their
definitions and frozen beta(n) in the Wilson receiver and posterior.
A non-a.e.-zero actual expectation gap at one link suffices for positive
Rayleigh, and zero Rayleigh forces every such gap to vanish.

This is an exact description of the detection obstruction; it does NOT
prove the obstruction is trivial, compute its rank, provide a positive
frame constant, spatial summability, or establish a continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

private noncomputable instance p4Q2GM_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact zero-mass criterion for a SINGLE true interacting two-Wilson-
posterior signed physical source response. This is not a Haar point
evaluation and uses GL's proved integrability, not an assumption. -/
theorem p4Q2GM_originalWilsonGapSquareLinkMean_zero_iff_gapAE
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
        H beta (le_of_lt hbeta) f e = 0 ↔
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta (le_of_lt hbeta) f e z = 0 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let D := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H beta (le_of_lt hbeta) f e
  let Q := fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H beta (le_of_lt hbeta) z.2 e
  have hInt : Integrable (fun z => D z ^ 2 / Q z) μ :=
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
      H beta hbeta f e
  have hNonneg : ∀ᵐ z ∂μ, 0 ≤ D z ^ 2 / Q z :=
    Filter.Eventually.of_forall (fun z =>
      div_nonneg (sq_nonneg (D z))
        (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
          H beta hbeta z.2 e).le)
  have hIntegral :
      (∫ z, D z ^ 2 / Q z ∂μ) = 0 ↔
        (fun z => D z ^ 2 / Q z) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
    integral_eq_zero_iff_of_nonneg_ae hNonneg hInt
  change (∫ z, D z ^ 2 / Q z ∂μ) = 0 ↔
    ∀ᵐ z ∂μ, D z = 0
  constructor
  · intro hZero
    have hAE := hIntegral.mp hZero
    filter_upwards [hAE] with z hz
    have hQ : Q z ≠ 0 :=
      (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
        H beta hbeta z.2 e).ne'
    have hSq : D z ^ 2 = 0 := by
      calc
        D z ^ 2 = (D z ^ 2 / Q z) * Q z :=
          (div_mul_cancel₀ _ hQ).symm
        _ = 0 := by rw [hz, zero_mul]
    exact sq_eq_zero_iff.mp hSq
  · intro hAE
    apply hIntegral.mpr
    filter_upwards [hAE] with z hz
    simp [hz]

/-- The GL observable has nonnegative link mass for every actual
physical source, with the unchanged original Wilson inner law. -/
theorem p4Q2GM_originalWilsonGapSquareLinkMean_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
      H beta (le_of_lt hbeta) f e := by
  rw [← p4Q2GL_originalWilsonSharpSignedGapLinkMean_eq_gapSquareDivVariance
    H beta hbeta f e]
  exact p4Q2GK_originalWilsonSignedGapProjectionLinkMean_nonneg
    H beta hbeta f e

/-- Exact intersection-of-a.e.-null-loci theorem for every finite genuine
spatial patch. No independence or source-frame assumption is hidden. -/
theorem p4Q2GM_originalWilsonGapSquarePatch_zero_iff_allLinks_gapAE
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H beta (le_of_lt hbeta) f S = 0 ↔
      ∀ e ∈ S,
        ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H beta (le_of_lt hbeta) f e z = 0 := by
  unfold p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ =>
    p4Q2GM_originalWilsonGapSquareLinkMean_nonneg H beta hbeta f e)]
  constructor
  · intro h e he
    exact (p4Q2GM_originalWilsonGapSquareLinkMean_zero_iff_gapAE
      H beta hbeta f e).mp (h e he)
  · intro h e he
    exact (p4Q2GM_originalWilsonGapSquareLinkMean_zero_iff_gapAE
      H beta hbeta f e).mpr (h e he)

/-- The exact physical gap-square detection mass is nonnegative on an
arbitrary finite actual link patch. -/
theorem p4Q2GM_originalWilsonGapSquarePatch_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤ p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H beta (le_of_lt hbeta) f S := by
  unfold p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  exact Finset.sum_nonneg (fun e _ =>
    p4Q2GM_originalWilsonGapSquareLinkMean_nonneg H beta hbeta f e)

/-- Sharp witness criterion: positive GL mass iff there is an actual
spatial link with a nonzero genuine Wilson posterior response gap on a
set of positive outer pair-Haar measure. -/
theorem p4Q2GM_originalWilsonGapSquarePatch_pos_iff_exists_gapWitness
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H beta (le_of_lt hbeta) f S ↔
      ∃ e ∈ S,
        ¬ ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H beta (le_of_lt hbeta) f e z = 0 := by
  classical
  have hNonneg :=
    p4Q2GM_originalWilsonGapSquarePatch_nonneg H beta hbeta f S
  constructor
  · intro hPos
    by_contra hNo
    push Not at hNo
    have hZero :=
      (p4Q2GM_originalWilsonGapSquarePatch_zero_iff_allLinks_gapAE
        H beta hbeta f S).mpr hNo
    exact (ne_of_gt hPos) hZero
  · rintro ⟨e, he, hGap⟩
    have hNe :
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H beta (le_of_lt hbeta) f S ≠ 0 := by
      intro hZero
      exact hGap
        ((p4Q2GM_originalWilsonGapSquarePatch_zero_iff_allLinks_gapAE
          H beta hbeta f S).mp hZero e he)
    exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Exact measurable detection-null criterion on the original adjacent
fine-right Krylov source sum, retaining the frozen beta(n) posterior. -/
theorem p4Q2GM_actualFineRightKrylovDetectionMass_zero_iff_gapAE
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) = 0 ↔
      ∀ e : Link,
        ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 := by
  simpa only [Finset.mem_univ, forall_const] using
    (p4Q2GM_originalWilsonGapSquarePatch_zero_iff_allLinks_gapAE
      Hn (beta n) hFrozen
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link))

/-- Exact measurable detection-null criterion for the real fine-left
Gram-Schmidt three-mode source sum, with no surrogate input family. -/
theorem p4Q2GM_actualFineLeftThreeModeDetectionMass_zero_iff_gapAE
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        (Finset.univ : Finset Link) = 0 ↔
      ∀ e : Link,
        ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            Hn (beta n) (hbeta n)
            (∑ k : Fin 3, a k • LeftFactor n r k) e z = 0 := by
  simpa only [Finset.mem_univ, forall_const] using
    (p4Q2GM_originalWilsonGapSquarePatch_zero_iff_allLinks_gapAE
      Hn (beta n) hFrozen
      (∑ k : Fin 3, a k • LeftFactor n r k)
      (Finset.univ : Finset Link))

/-- If an actual fine-right Krylov Gram Rayleigh vanishes, every genuine
two-Wilson-posterior signed response expectation gap vanishes a.e.
This is one-way; the converse is not currently established. -/
theorem p4Q2GM_actualFineRightKrylovGram_zero_implies_gapAE
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (hZero : star a ⬝ᵥ Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a = 0) :
    ∀ e : Link,
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 := by
  have hOriginal : star a ⬝ᵥ Matrix.mulVec
      (pairHaarSpatialLinkResidualGram Hn 2 Pos (beta n) (hbeta n)
        (fun j : Fin (r + 1) =>
          normalizedPhysicalOneSlabPairHaarReceiver
            Hn 2 Pos (beta n) (hbeta n) (RightFactor n (j : ℕ)))) a = 0 := by
    simpa only [fineRightKrylovPairHaarResidualGram] using hZero
  exact p4Q2GI_originalWilsonGram_zero_implies_allLinkExpectationGap_ae_zero
    Hn (beta n) hFrozen
    (fun j : Fin (r + 1) => RightFactor n (j : ℕ)) a hOriginal

/-- The corresponding necessary true-Wilson response obstruction
for the original fine-left physical three-mode Gram. -/
theorem p4Q2GM_actualFineLeftThreeModeGram_zero_implies_gapAE
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ)
    (hZero : star a ⬝ᵥ Matrix.mulVec
      (fineLeftThreeModePairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a = 0) :
    ∀ e : Link,
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n)
          (∑ k : Fin 3, a k • LeftFactor n r k) e z = 0 := by
  have hOriginal : star a ⬝ᵥ Matrix.mulVec
      (pairHaarSpatialLinkResidualGram Hn 2 Pos (beta n) (hbeta n)
        (fun k : Fin 3 =>
          normalizedPhysicalOneSlabPairHaarReceiver
            Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k))) a = 0 := by
    simpa only [fineLeftThreeModePairHaarResidualGram] using hZero
  exact p4Q2GI_originalWilsonGram_zero_implies_allLinkExpectationGap_ae_zero
    Hn (beta n) hFrozen
    (fun k : Fin 3 => LeftFactor n r k) a hOriginal

/-- A genuine positive-measure posterior expectation-gap witness
forces strict ACTUAL adjacent fine-right physical Gram positivity. -/
theorem p4Q2GM_actualFineRightKrylovGram_pos_of_gapWitness
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (e : Link)
    (hGap : ¬ ∀ᵐ z
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0) :
    0 < star a ⬝ᵥ Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a := by
  simpa only [fineRightKrylovPairHaarResidualGram] using
    (p4Q2GI_originalWilsonPhysicalGram_pos_of_oneLink_expectationGap_notAEZero
      Hn (beta n) hFrozen
      (fun j : Fin (r + 1) => RightFactor n (j : ℕ)) a e hGap)

/-- The same witness criterion for ACTUAL adjacent fine-left three modes. -/
theorem p4Q2GM_actualFineLeftThreeModeGram_pos_of_gapWitness
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ)
    (e : Link)
    (hGap : ¬ ∀ᵐ z
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k) e z = 0) :
    0 < star a ⬝ᵥ Matrix.mulVec
      (fineLeftThreeModePairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a := by
  simpa only [fineLeftThreeModePairHaarResidualGram] using
    (p4Q2GI_originalWilsonPhysicalGram_pos_of_oneLink_expectationGap_notAEZero
      Hn (beta n) hFrozen
      (fun k : Fin 3 => LeftFactor n r k) a e hGap)

end ActualAdjacentOrbit
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_originalWilsonGapSquareLinkMean_zero_iff_gapAE
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_originalWilsonGapSquareLinkMean_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_originalWilsonGapSquarePatch_zero_iff_allLinks_gapAE
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_originalWilsonGapSquarePatch_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_originalWilsonGapSquarePatch_pos_iff_exists_gapWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_actualFineRightKrylovDetectionMass_zero_iff_gapAE
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_actualFineLeftThreeModeDetectionMass_zero_iff_gapAE
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_actualFineRightKrylovGram_zero_implies_gapAE
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_actualFineLeftThreeModeGram_zero_implies_gapAE
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_actualFineRightKrylovGram_pos_of_gapWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GM_actualFineLeftThreeModeGram_pos_of_gapWitness

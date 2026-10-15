import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIJointSourceKernelV5_HD
import Mathlib.Tactic

/-!
# P4-Q2-HE: exact original GI detector mass rank-one law and physical Gram floor

HD gave a conditional strict-positive Gram criterion under a TRUE
two-original-Wilson-posterior GI anchor detector, but did not yet
quantify the observed detector energy.

At ACTUAL fine beta(n+1)=0 the signed fine-right Krylov source equals
  F_a = (sum_j a_j) * u
with u the normalized physical constant unit. HC proved the genuine
two-Wilson-posterior gap obeys pointwise
  Delta_{F_a}(e,z) = (sum_j a_j) * Delta_u(e,z).

This file transports that identity through the ORIGINAL integrable GL
observable with the *actual positive Wilson density-distance* Q:
  M_GL(F_a,e) = (sum_j a_j)^2 * M_GL(u,e),
  M_GL(F_a,S) = (sum_j a_j)^2 * M_GL(u,S).

The exact null-locus and a *quantitative* original physical Gram
Rayleigh floor follow, with no fictitious independence assumptions,
no postulated lower frame and no replacement of the inner interacting
Wilson posteriors by reference Haar. The physical finite-rank kernel
is a true zero-sum coefficient hyperplane, and whether the GI anchor
mass is strictly positive remains an explicitly isolated condition.

No positive fine-beta beta(n+1) injectivity, uniform volume/scale
coercivity, H1-C3 reconstruction or continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2700000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2HE_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HE_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HE_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HE_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HE_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HE_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualFineZero

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The literal original GL link expectation-gap squared mass scales by
the SQUARE of the signed physical Krylov coefficient sum when the ACTUAL
FINE coupling vanishes. The frozen interacting Wilson law and Q
denominator are left unchanged. This is an equality of real integrals. -/
theorem p4Q2HE_fineZero_originalGLLinkMass_eq_coeffSum_sq_mul
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) (e : Link) :
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e =
      (∑ j : Fin (r + 1), a j) ^ 2 *
        p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
          Hn (beta n) (hbeta n) (RightFactor n 0) e := by
  let ν := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2
  let c : ℝ := ∑ j : Fin (r + 1), a j
  let F := ∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)
  let u := RightFactor n 0
  let Q := fun z : Cfg × Cfg =>
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      Hn (beta n) (hbeta n) z.2 e
  let D := fun (f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2)
      (z : Cfg × Cfg) =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) f e z
  change (∫ z : Cfg × Cfg, (D F z) ^ 2 / Q z ∂ν) =
    c ^ 2 * (∫ z : Cfg × Cfg, (D u z) ^ 2 / Q z ∂ν)
  calc
    (∫ z : Cfg × Cfg, (D F z) ^ 2 / Q z ∂ν) =
        ∫ z : Cfg × Cfg, c ^ 2 * ((D u z) ^ 2 / Q z) ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      have hFactor :
          D F z = c * D u z := by
        exact p4Q2HC_fineZero_originalGIExpectationGap_eq_sum_mul
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r hFineZero a e z
      rw [hFactor]
      ring
    _ = c ^ 2 * (∫ z : Cfg × Cfg, (D u z) ^ 2 / Q z ∂ν) := by
      exact integral_const_mul _ _

/-- The SAME rank-one quadratic scaling holds after summing every
actual physical link of an arbitrary finite patch. There is no
invented coefficient-independent link detector. -/
theorem p4Q2HE_fineZero_originalGLPatchMass_eq_coeffSum_sq_mul
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) (S : Finset Link) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) S =
      (∑ j : Fin (r + 1), a j) ^ 2 *
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          Hn (beta n) (hbeta n) (RightFactor n 0) S := by
  unfold p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  exact p4Q2HE_fineZero_originalGLLinkMass_eq_coeffSum_sq_mul
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a e

/-- The precise finite-patch original interacting Wilson GI detection
mass null locus is a rank-one dichotomy: either the genuine physical
source coefficients sum to zero, or the original zero-depth anchor
itself has zero GL detection mass on this patch. This needs no anchor
positivity premise. -/
theorem p4Q2HE_fineZero_originalGLPatchMass_zero_iff
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) (S : Finset Link) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) S = 0 ↔
      (∑ j : Fin (r + 1), a j) = 0 ∨
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n) (RightFactor n 0) S = 0 := by
  rw [p4Q2HE_fineZero_originalGLPatchMass_eq_coeffSum_sq_mul
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a S, mul_eq_zero, sq_eq_zero_iff]

/-- An actually POSITIVE original GI anchor mass on a true finite
physical link patch yields a strict positive GL detection mass in
every nonzero genuine rank-one physical source direction. The source
coefficient sum is the only spectral input here. -/
theorem p4Q2HE_fineZero_originalGLPatchMass_pos_of_anchor_pos
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (hSum : (∑ j : Fin (r + 1), a j) ≠ 0)
    (S : Finset Link)
    (hAnchor :
      0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n) (RightFactor n 0) S) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) S := by
  rw [p4Q2HE_fineZero_originalGLPatchMass_eq_coeffSum_sq_mul
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a S]
  have hCoeffPos : 0 < (∑ j : Fin (r + 1), a j) ^ 2 := by
    exact sq_pos_of_ne_zero hSum
  exact mul_pos hCoeffPos hAnchor

/-- QUANTITATIVE original physical Gram floor in the genuine 1-D
fine-beta-zero Krylov quotient: it has the actual frozen-Wilson GL
zero-depth mass multiplied by the square of the signed coefficient
sum, with every Wilson normalization and thermal factor retained.
Importantly the mass may be zero; no positivity is conjectured. -/
theorem p4Q2HE_fineZero_actualPhysicalKrylovGram_ge_anchorMass_mul_sumSq
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          Hn 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta n) *
        ((∑ j : Fin (r + 1), a j) ^ 2 *
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n) (RightFactor n 0)
            (Finset.univ : Finset Link))) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
  have hGram :=
    p4Q2GL_originalWilsonPhysicalGram_rayleigh_ge_gapSquareDivVariance
      Hn (beta n) hFrozen
      (fun j : Fin (r + 1) => RightFactor n (j : ℕ)) a
  rw [p4Q2HE_fineZero_originalGLPatchMass_eq_coeffSum_sq_mul
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a (Finset.univ : Finset Link)] at hGram
  simpa only [fineRightKrylovPairHaarResidualGram] using hGram

end ActualFineZero
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HE_fineZero_originalGLLinkMass_eq_coeffSum_sq_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HE_fineZero_originalGLPatchMass_eq_coeffSum_sq_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HE_fineZero_originalGLPatchMass_zero_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HE_fineZero_originalGLPatchMass_pos_of_anchor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HE_fineZero_actualPhysicalKrylovGram_ge_anchorMass_mul_sumSq

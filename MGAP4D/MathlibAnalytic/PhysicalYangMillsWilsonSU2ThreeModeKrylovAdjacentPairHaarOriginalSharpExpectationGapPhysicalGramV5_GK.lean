import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSharpExpectationGapConditionalRMSV5_GJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalActualAdjacentKrylovSourceProjectionV5_GG
import Mathlib.Tactic

/-!
# P4-Q2-GK — sharp ORIGINAL two-Wilson-posterior expectation gap in physical Gram

GJ proves that the exact original-Wilson conditional RMS of the actual
signed physical FF response dominates exp(-16 beta) times the TRUE
two-Wilson-posterior expectation gap times the original physical-source
projection coefficient.

Here this sharper local quantitative certificate is integrated and
transferred without loss to:
* the original physical finite-link patch energy,
* the ORIGINAL Wilson physical signed-source finite-family Gram Rayleigh,
* the ACTUAL adjacent-scale fine-right Krylov and left-three-mode Grams.

The sharp positive gap/projection link mass dominates the older GA
beta^2*exp(-32 beta)*V_SU2 source projection certificate, so none of
GE/GG's genuine finite-H physical coercive information is discarded.

The inner resampling law is always the interacting Wilson posterior;
Haar is only the outer pair-reference and the exact density comparison
law. No unproved source-frame floor, H-/scale-uniform spatial summability,
C1/C2/C3, H2/H3/H4, or continuum Yang–Mills mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

private noncomputable instance p4Q2GK_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The true-Wilson two-posterior physical signed gap/projection mass,
retaining each original spatial link and the complete physical source. -/
noncomputable def p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  S.sum (p4Q2GJ_originalWilsonSignedGapProjectionLinkMean H beta hbeta f)

/-- The sharp true-Wilson signed expectation-gap contribution is
nonnegative because GJ identifies it with Q(z)*alpha(z)^2. -/
theorem p4Q2GK_originalWilsonSignedGapProjectionLinkMean_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2GJ_originalWilsonSignedGapProjectionLinkMean
      H beta (le_of_lt hbeta) f e := by
  unfold p4Q2GJ_originalWilsonSignedGapProjectionLinkMean
  exact integral_nonneg (fun z =>
    p4Q2GJ_originalWilsonSignedGap_mul_projection_nonneg H beta hbeta f e z)

/-- The sharp original two-Wilson-posterior expectation-gap link mean
dominates the coarser GA universal beta-squared projected-source mass.
In particular GJ cannot weaken the preceding GE/GG certificates. -/
theorem p4Q2GK_originalWilsonSignedGapProjectionLinkMean_ge_uniform
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (Real.exp (-32 * beta) *
      (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)) *
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
        H beta (le_of_lt hbeta) f e ≤
      p4Q2GJ_originalWilsonSignedGapProjectionLinkMean
        H beta (le_of_lt hbeta) f e := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let alpha := p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    H beta (le_of_lt hbeta) f e
  let Delta := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H beta (le_of_lt hbeta) f e
  let Q := fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H beta (le_of_lt hbeta) z.2 e
  let A := fun z => (alpha z) ^ 2
  let G := fun z => Delta z * alpha z
  let c : ℝ := Real.exp (-32 * beta) *
    (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)
  have hA : Integrable A μ :=
    p4Q2GD_originalPhysicalSourceProjection_sq_integrable
      H beta hbeta f e
  have hG : Integrable G μ :=
    p4Q2GJ_originalWilsonSignedGapProjection_pairHaar_integrable
      H beta hbeta f e
  have hPoint (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
      c * A z ≤ G z := by
    have hQ : c ≤ Q z :=
      p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
        H beta (le_of_lt hbeta) z.2 e
    calc
      c * A z ≤ Q z * A z :=
        mul_le_mul_of_nonneg_right hQ (sq_nonneg (alpha z))
      _ = Delta z * alpha z := by
        rw [p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
          H beta hbeta f e z]
        ring
  change c * (∫ z, A z ∂μ) ≤ ∫ z, G z ∂μ
  calc
    c * (∫ z, A z ∂μ) =
        ∫ z, c * A z ∂μ := by rw [integral_const_mul]
    _ ≤ ∫ z, G z ∂μ := by
      apply integral_mono (hA.const_mul _) hG
      intro z
      exact hPoint z

/-- Exact finite-patch nonnegativity, without assuming a source frame. -/
theorem p4Q2GK_originalWilsonSharpSignedGapSpatialMass_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤ p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
      H beta (le_of_lt hbeta) f S := by
  unfold p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
  exact Finset.sum_nonneg (fun e _ =>
    p4Q2GK_originalWilsonSignedGapProjectionLinkMean_nonneg H beta hbeta f e)

/-- On any genuine finite physical patch the sharp signed expectation-gap
mass quantitatively improves the former GA-only projected mass. -/
theorem p4Q2GK_originalWilsonSharpSignedGapSpatialMass_ge_uniform
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (Real.exp (-32 * beta) *
      (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)) *
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
        H beta (le_of_lt hbeta) f S ≤
      p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
        H beta (le_of_lt hbeta) f S := by
  unfold p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
    p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun e _ =>
    p4Q2GK_originalWilsonSignedGapProjectionLinkMean_ge_uniform H beta hbeta f e)

/-- For the EXACT original physical finite-link Wilson defect,
the GJ quantitative expectation-gap certificate holds with its
unmodified frozen physical transfer-norm normalization. -/
theorem p4Q2GK_originalPhysicalPatchEnergy_ge_sharpSignedGapProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta) *
        p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
          H beta (le_of_lt hbeta) f S) ≤
      p4Q2FD_originalPhysicalRestrictedLinkEnergy
        H 2 (by norm_num) beta (le_of_lt hbeta) f S := by
  let lambdaInvSq : ℝ :=
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2
  let scale : ℝ := (1 / 2 : ℝ) * lambdaInvSq
  have hScale : 0 ≤ scale := mul_nonneg (by norm_num) (sq_nonneg _)
  have hSums :
      Real.exp (-16 * beta) *
        p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
          H beta (le_of_lt hbeta) f S ≤
      p4Q2FH_originalWilsonSpatialRMSMass
        H 2 (by norm_num) beta (le_of_lt hbeta) f S := by
    unfold p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
      p4Q2FH_originalWilsonSpatialRMSMass
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _ =>
      p4Q2GJ_originalWilsonLinkRMS_ge_sharpSignedGapProjection
        H beta hbeta f e)
  have hEnergy :=
    p4Q2FH_originalPhysicalPatchEnergy_eq_spatialRMSMass
      H 2 (by norm_num) beta (le_of_lt hbeta) f S
  change scale *
      (Real.exp (-16 * beta) *
        p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
          H beta (le_of_lt hbeta) f S) ≤
    p4Q2FD_originalPhysicalRestrictedLinkEnergy
      H 2 (by norm_num) beta (le_of_lt hbeta) f S
  calc
    scale * (Real.exp (-16 * beta) *
        p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
          H beta (le_of_lt hbeta) f S) ≤
      scale * p4Q2FH_originalWilsonSpatialRMSMass
        H 2 (by norm_num) beta (le_of_lt hbeta) f S :=
      mul_le_mul_of_nonneg_left hSums hScale
    _ = p4Q2FD_originalPhysicalRestrictedLinkEnergy
          H 2 (by norm_num) beta (le_of_lt hbeta) f S := hEnergy.symm

/-- Arbitrary finite physical source family: the ORIGINAL signed Wilson
Gram Rayleigh is bounded below by the SHARP true two-posterior
expectation-gap mass of the SAME actual combined physical input. -/
theorem p4Q2GK_originalWilsonPhysicalGram_rayleigh_ge_sharpSignedGap
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta) *
        p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := by
  classical
  let F := ∑ i : ι, a i • f i
  let S := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hPatch :=
    p4Q2GK_originalPhysicalPatchEnergy_ge_sharpSignedGapProjection
      H beta hbeta F S
  have hPhys :=
    p4Q2FG_originalPhysicalRestrictedEnergy_eq_pairHaarConditionalRMSPatch
      H 2 (by norm_num) beta (le_of_lt hbeta) F S
  have hRay :=
    p4Q2FG_originalWilsonPhysicalGram_rayleigh_eq_pairHaarConditionalRMS
      H 2 (by norm_num) beta (le_of_lt hbeta) f a
  calc
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta) *
        p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
          H beta (le_of_lt hbeta) F S) ≤
      p4Q2FD_originalPhysicalRestrictedLinkEnergy
        H 2 (by norm_num) beta (le_of_lt hbeta) F S := hPatch
    _ = p4Q2FG_originalWilsonPairHaarConditionalRMSPatchEnergy
      H 2 (by norm_num) beta (le_of_lt hbeta) F S := hPhys
    _ = star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := hRay.symm

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

/-- Actual adjacent-scale right Krylov Gram, with ORIGINAL fine beta(n+1)
in the orbit and frozen beta(n) in the real physical Wilson law,
inherits the sharp TRUE two-posterior source expectation-gap floor. -/
theorem p4Q2GK_actualFineRightKrylovGram_ge_sharpSignedGap
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        Hn 2 Pos (beta n) (hbeta n)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta n) *
        p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
          (Finset.univ : Finset Link)) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
  simpa only [fineRightKrylovPairHaarResidualGram] using
    (p4Q2GK_originalWilsonPhysicalGram_rayleigh_ge_sharpSignedGap
      Hn (beta n) hFrozen
      (fun j : Fin (r + 1) => RightFactor n (j : ℕ)) a)

/-- Actual adjacent-scale left three physical modes, without changing
the fine dynamics or the frozen posterior, inherit the same SHARP floor. -/
theorem p4Q2GK_actualFineLeftThreeModeGram_ge_sharpSignedGap
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        Hn 2 Pos (beta n) (hbeta n)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta n) *
        p4Q2GK_originalWilsonSharpSignedGapProjectionSpatialMass
          Hn (beta n) (hbeta n)
          (∑ k : Fin 3, a k • LeftFactor n r k)
          (Finset.univ : Finset Link)) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (fineLeftThreeModePairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
  simpa only [fineLeftThreeModePairHaarResidualGram] using
    (p4Q2GK_originalWilsonPhysicalGram_rayleigh_ge_sharpSignedGap
      Hn (beta n) hFrozen
      (fun k : Fin 3 => LeftFactor n r k) a)

end ActualAdjacentOrbit
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GK_originalWilsonSignedGapProjectionLinkMean_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GK_originalWilsonSignedGapProjectionLinkMean_ge_uniform
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GK_originalWilsonSharpSignedGapSpatialMass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GK_originalWilsonSharpSignedGapSpatialMass_ge_uniform
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GK_originalPhysicalPatchEnergy_ge_sharpSignedGapProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GK_originalWilsonPhysicalGram_rayleigh_ge_sharpSignedGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GK_actualFineRightKrylovGram_ge_sharpSignedGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GK_actualFineLeftThreeModeGram_ge_sharpSignedGap

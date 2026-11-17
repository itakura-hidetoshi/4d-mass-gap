import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTimeOneOSNullSpaceStrictnessV5_PZ37ANK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANL — quantitative original Wilson OS boundary-variance identity

For the unmodified original full-periodic SU(2) Wilson time-one two-mode cylinder,
upgrade ANK's qualitative OS null-space equivalence to an exact variance
decomposition of its SAME original boundary Haar Gram moment. Its integrability
and square-integrability are theorems already established in ANK.

The resulting beta-zero lower bound uses ANJ's exact original boundary mean
sqrt(Z_H(0)^(-1)) * c0, not an assumed physical-excitation coefficient.
No positivity for the actual physical top-orthogonal choice, H-uniform gap,
one-slab intertwining, or continuum four-dimensional mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANL_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANL_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANL_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANL_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANL_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANL_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

-- The named ORIGINAL boundary Haar, not an interacting or replacement measure,
-- is a finite product of normalized compact SU(2) Haar probabilities.
local instance p4Q2PZ37ANL_boundaryProbability (H : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

/-- Algebraic L² variance identity on any probability measure. No Jensen
regularity premise is introduced: both L¹ and the actual square integral
are available separately. -/
theorem p4Q2PZ37ANL_realIntegralSq_eq_meanSq_add_centeredSq
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : Integrable f μ)
    (h2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ^ 2 ∂μ) =
      (∫ x, f x ∂μ) ^ 2 +
        ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  let a : ℝ := ∫ x, f x ∂μ
  have hg : Integrable (fun x => (2 * a) * f x) μ := hf.const_mul _
  have hc : Integrable (fun _ : α => a ^ 2) μ := integrable_const _
  have hcenter :
      (∫ x, (f x - a) ^ 2 ∂μ) =
        (∫ x, f x ^ 2 ∂μ) - (2 * a) * (∫ x, f x ∂μ) + a ^ 2 := by
    calc
      (∫ x, (f x - a) ^ 2 ∂μ) =
          ∫ x, (f x ^ 2 - (2 * a) * f x + a ^ 2) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, f x ^ 2 ∂μ) - (2 * a) * (∫ x, f x ∂μ) + a ^ 2 := by
        rw [integral_add (h2.sub hg) hc, integral_sub h2 hg,
          integral_const_mul]
        simp
  have ha : a = ∫ x, f x ∂μ := rfl
  calc
    (∫ x, f x ^ 2 ∂μ) =
        a ^ 2 + ∫ x, (f x - a) ^ 2 ∂μ := by
      rw [hcenter, ha]
      ring
    _ = (∫ x, f x ∂μ) ^ 2 +
        ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by rw [ha]

/-- Exact variance decomposition for the ORIGINAL full-periodic Wilson Gibbs
OS quadratic form and its original boundary Haar moment, at every beta ≥ 0. -/
theorem p4Q2PZ37ANL_originalTimeOneWilsonOSQuadratic_variance_identity
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 =
      (∫ b, p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta c0 c1 b
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)) ^ 2 +
      ∫ b,
        (p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
          H beta hbeta c0 c1 b -
          ∫ a, p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
            H beta hbeta c0 c1 a
            ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)) ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let M := p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
    H beta hbeta c0 c1
  have hf : Integrable M μ :=
    p4Q2PZ37ANK_originalTimeOneBoundaryMoment_integrable H beta hbeta c0 c1
  have h2 : Integrable (fun b => M b ^ 2) μ :=
    (p4Q2PZ37ANK_originalTimeOneBoundaryMoment_memLp_two
      H beta hbeta c0 c1).integrable_sq
  have hvar := p4Q2PZ37ANL_realIntegralSq_eq_meanSq_add_centeredSq μ M hf h2
  rw [p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_eq_boundaryGramMoment_sq]
  simpa only [μ, M, Real.norm_eq_abs, sq_abs] using hvar

/-- Quantitative lower bound for the SAME original Wilson OS form,
with no assumed nonzero class or nonvanishing physical coefficient. -/
theorem p4Q2PZ37ANL_originalTimeOneWilsonOSQuadratic_meanSq_le
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    (∫ b, p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
       H beta hbeta c0 c1 b
       ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)) ^ 2 ≤
      p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 := by
  rw [p4Q2PZ37ANL_originalTimeOneWilsonOSQuadratic_variance_identity]
  apply le_add_of_nonneg_right
  exact integral_nonneg (fun b => sq_nonneg _)

/-- At beta zero the original ANJ first moment supplies an explicit
partition-normalized quadratic lower bound for the exact OS form. -/
theorem p4Q2PZ37ANL_originalBetaZeroWilsonOSQuadratic_sqrtZc0_sq_le
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ) :
    (Real.sqrt
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) 0
        (by norm_num)).base.partitionFunction⁻¹) * c0) ^ 2 ≤
      p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
        H 0 (by norm_num) c0 c1 := by
  have h := p4Q2PZ37ANL_originalTimeOneWilsonOSQuadratic_meanSq_le
    H 0 (by norm_num) c0 c1
  rw [p4Q2PZ37ANJ_originalBetaZeroBoundaryGramMoment_boundaryHaarMean] at h
  exact h

/-- The same lower bound without the square-root notation. Its coefficient
is the ORIGINAL positive finite Wilson beta-zero partition inverse. -/
theorem p4Q2PZ37ANL_originalBetaZeroWilsonOSQuadratic_invZ_c0sq_le
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ) :
    ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) 0
        (by norm_num)).base.partitionFunction⁻¹) * c0 ^ 2 ≤
      p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
        H 0 (by norm_num) c0 c1 := by
  have h := p4Q2PZ37ANL_originalBetaZeroWilsonOSQuadratic_sqrtZc0_sq_le
    H c0 c1
  have hs := p4Q2PZ37ANH_originalWilsonBetaZeroGramScalar_pos H
  have hinv : 0 ≤
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) 0
        (by norm_num)).base.partitionFunction⁻¹ :=
    le_of_lt (Real.sqrt_pos.mp hs)
  have hr := Real.sq_sqrt hinv
  nlinarith [h, hr]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANL_realIntegralSq_eq_meanSq_add_centeredSq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANL_originalTimeOneWilsonOSQuadratic_variance_identity
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANL_originalTimeOneWilsonOSQuadratic_meanSq_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANL_originalBetaZeroWilsonOSQuadratic_sqrtZc0_sq_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANL_originalBetaZeroWilsonOSQuadratic_invZ_c0sq_le

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTimeOneClosureHaarMeanV5_PZ37ANJ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalTransfer
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANK — original Wilson OS null space and beta-zero strictness

For the EXACT original ANF time-one two-mode cylinder and boundary Gram
moment, prove integrability and square-integrability on original boundary
Haar. This discharges the integrability needed for an exact OS null-space
criterion; it is not assumed as another certificate field.

At every beta >= 0, Q_OS = 0 iff its actual boundary Gram moment is zero
boundary-Haar almost everywhere. A nonzero first boundary moment therefore
forces strict OS positivity. At beta = 0, ANJ computes that first moment
as sqrt(Z_H(0)^(-1))*c0, yielding strict positivity when c0 is nonzero.

The physical top-eigenspace-orthogonal coefficients are NOT asserted to
have c0 != 0. No fixed-boundary mean-zero assertion, beta-positive physical
excitation witness, OS quotient identification, intertwining, uniform gap,
or continuum Yang--Mills gap follows from this finite-volume statement.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANK_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANK_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANK_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANK_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANK_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANK_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

-- Expose BOTH native finite Haar factors before invoking Fubini; do not
-- rely on synthesis through the named measure wrappers.
local instance p4Q2PZ37ANK_boundaryFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance
local instance p4Q2PZ37ANK_openFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- Original finite-volume Wilson bound; the original partition function
and the two unchanged Wilson mode norms are retained literally. -/
noncomputable def p4Q2PZ37ANK_originalTimeOneGramBound
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) : ℝ :=
  Real.sqrt
    ((periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta).base.partitionFunction⁻¹) *
    (|c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
      |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖)

/-- Pointwise bound on the actual boundary-fibered original Gram feature
multiplied by the same time-one observable. -/
theorem p4Q2PZ37ANK_originalTimeOneGramFeature_norm_le
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 (by norm_num) beta hbeta b x *
      p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1 (b, x)‖ ≤
      p4Q2PZ37ANK_originalTimeOneGramBound H beta hbeta c0 c1 := by
  have hg0 := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
    H 2 (by norm_num) beta hbeta b x
  have hg :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
      H 2 (by norm_num) beta hbeta b x
  have hf := p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_norm_le
    H c0 c1 (b, x)
  unfold p4Q2PZ37ANK_originalTimeOneGramBound
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hg0]
  exact mul_le_mul hg hf (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Joint integrability is derived from actual joint Wilson-kernel
measurability, ANF observability and finite original product Haar. -/
theorem p4Q2PZ37ANK_originalTimeOneGramFeature_joint_integrable
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    Integrable
      (fun z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H 2 =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 (by norm_num) beta hbeta z.1 z.2 *
        p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1 z)
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) := by
  have hm :=
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_joint_measurable
      H 2 (by norm_num) beta hbeta).mul
      (p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_measurable H c0 c1)
  apply Integrable.of_bound hm.aestronglyMeasurable
    (p4Q2PZ37ANK_originalTimeOneGramBound H beta hbeta c0 c1)
  exact Filter.Eventually.of_forall fun z =>
    p4Q2PZ37ANK_originalTimeOneGramFeature_norm_le H beta hbeta c0 c1 z.1 z.2

/-- The actual original time-one boundary moment is integrable on original
boundary Haar, by joint finite-Haar integrability and Fubini. -/
theorem p4Q2PZ37ANK_originalTimeOneBoundaryMoment_integrable
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    Integrable
      (p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1)
      (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  have hjoint := p4Q2PZ37ANK_originalTimeOneGramFeature_joint_integrable
    H beta hbeta c0 c1
  simpa only [p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment,
    periodicHypercubicEvenBoundaryObservableGramFeature] using
    hjoint.integral_prod_left

/-- A uniform bound in b, retaining the exact open-half Haar mass to avoid
silently substituting a normalized/interacting measure. -/
theorem p4Q2PZ37ANK_originalTimeOneBoundaryMoment_norm_le
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1 b‖ ≤
      p4Q2PZ37ANK_originalTimeOneGramBound H beta hbeta c0 c1 *
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2).real Set.univ := by
  unfold p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
  apply norm_integral_le_of_norm_le_const
  exact Filter.Eventually.of_forall fun x =>
    p4Q2PZ37ANK_originalTimeOneGramFeature_norm_le H beta hbeta c0 c1 b x

/-- Boundary-Haar MemLp 2 is a theorem about the actual original moment,
not an added hypothesis and not a different OS Hilbert carrier. -/
theorem p4Q2PZ37ANK_originalTimeOneBoundaryMoment_memLp_two
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    MemLp
      (p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1)
      2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  have hi := p4Q2PZ37ANK_originalTimeOneBoundaryMoment_integrable
    H beta hbeta c0 c1
  apply MemLp.of_bound hi.aestronglyMeasurable
    (p4Q2PZ37ANK_originalTimeOneGramBound H beta hbeta c0 c1 *
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2).real Set.univ)
  exact Filter.Eventually.of_forall
    (p4Q2PZ37ANK_originalTimeOneBoundaryMoment_norm_le H beta hbeta c0 c1)

/-- The squared boundary moment in ANF's exact OS identity is genuinely
integrable. Thus a zero Bochner integral cannot be an integrability default. -/
theorem p4Q2PZ37ANK_originalTimeOneBoundaryMoment_norm_sq_integrable
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    Integrable
      (fun b => ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta c0 c1 b‖ ^ 2)
      (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  have hm := p4Q2PZ37ANK_originalTimeOneBoundaryMoment_memLp_two
    H beta hbeta c0 c1
  -- Fix both factors to the original real moment before simplifying its norm.
  have hmul : Integrable
      (fun b => p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
          H beta hbeta c0 c1 b *
        p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1 b)
      (periodicHypercubicEvenBoundaryHaarMeasure H 2) := hm.integrable_mul hm
  -- Transfer integrability through a.e. equality, avoiding dependent rewriting.
  have hAE :
      (fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
        p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1 b *
          p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1 b)
        =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H 2]
      (fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
        ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
          H beta hbeta c0 c1 b‖ ^ 2) := by
    filter_upwards [] with b
    rw [Real.norm_eq_abs, sq_abs, pow_two]
  exact hmul.congr hAE

/-- Exact null-space criterion for the ORIGINAL full-periodic Wilson OS
form. Both directions use the actual boundary moment with square
integrability proved above, rather than ordinary Gibbs/Haar L2 nonzero. -/
theorem p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_zero_iff_boundaryMoment_ae_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 = 0 ↔
      (p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1
        =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H 2] (fun _ => (0 : ℝ))) := by
  rw [p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_eq_boundaryGramMoment_sq]
  have hi := p4Q2PZ37ANK_originalTimeOneBoundaryMoment_norm_sq_integrable
    H beta hbeta c0 c1
  have hn : ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2),
      0 ≤ ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta c0 c1 b‖ ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  constructor
  · intro hz
    have hs := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    filter_upwards [hs] with b hb
    simpa only [sq_eq_zero_iff, norm_eq_zero] using hb
  · intro hz
    have hs : (fun b => ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta c0 c1 b‖ ^ 2) =ᵐ[
          periodicHypercubicEvenBoundaryHaarMeasure H 2] (fun _ => (0 : ℝ)) := by
      filter_upwards [hz] with b hb
      simp only [hb, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact (integral_congr_ae hs).trans (by simp)

/-- Strict OS positivity iff the actual original boundary moment is not
boundary-Haar almost-everywhere zero, valid for every beta >= 0. -/
theorem p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_pos_iff_boundaryMoment_not_ae_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    0 < p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 ↔
      ¬ (p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1
        =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H 2] (fun _ => (0 : ℝ))) := by
  have hzero :=
    p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_zero_iff_boundaryMoment_ae_zero
      H beta hbeta c0 c1
  constructor
  · intro hpos hz
    exact (ne_of_gt hpos) (hzero.mpr hz)
  · intro hne
    have hqne : p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 ≠ 0 := by
      intro hz
      exact hne (hzero.mp hz)
    exact lt_of_le_of_ne
      (p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_nonneg H beta hbeta c0 c1)
      (Ne.symm hqne)

/-- Nonzero FIRST boundary moment suffices for genuine strict OS positivity;
the original square-integrability/null-space bridge is now discharged. -/
theorem p4Q2PZ37ANK_originalTimeOneOSQuadratic_pos_of_boundaryMean_ne_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ)
    (hMean : (∫ b,
      p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1 b
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)) ≠ 0) :
    0 < p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 := by
  apply (p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_pos_iff_boundaryMoment_not_ae_zero
    H beta hbeta c0 c1).mpr
  intro hz
  apply hMean
  exact (integral_congr_ae hz).trans (by simp)

/-- For the unchanged original two-mode time-one Wilson cylinder at beta=0,
nonzero c0 gives strict OS positivity for EVERY finite H, including H=0.
This is not a claim about c0 of the physical top-orthogonal witness. -/
theorem p4Q2PZ37ANK_originalBetaZeroOSQuadratic_pos_of_c0_ne_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ) (hc0 : c0 ≠ 0) :
    0 < p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H 0 (by norm_num) c0 c1 := by
  apply p4Q2PZ37ANK_originalTimeOneOSQuadratic_pos_of_boundaryMean_ne_zero
  rw [p4Q2PZ37ANJ_originalBetaZeroBoundaryGramMoment_boundaryHaarMean]
  exact mul_ne_zero
    (ne_of_gt (p4Q2PZ37ANH_originalWilsonBetaZeroGramScalar_pos H)) hc0

/-- Therefore an OS-null original time-one two-mode cylinder at beta=0
must have c0=0. The converse is deliberately NOT asserted: boundary-fixed
H=0 differs from strict interior H>0 and still needs geometric analysis. -/
theorem p4Q2PZ37ANK_originalBetaZeroOSQuadratic_zero_implies_c0_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ)
    (hz : p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H 0 (by norm_num) c0 c1 = 0) :
    c0 = 0 := by
  by_contra hc0
  have hp := p4Q2PZ37ANK_originalBetaZeroOSQuadratic_pos_of_c0_ne_zero H c0 c1 hc0
  rw [hz] at hp
  exact (lt_irrefl (0 : ℝ)) hp

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneGramFeature_norm_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneGramFeature_joint_integrable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneBoundaryMoment_integrable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneBoundaryMoment_norm_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneBoundaryMoment_memLp_two
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneBoundaryMoment_norm_sq_integrable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_zero_iff_boundaryMoment_ae_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_pos_iff_boundaryMoment_not_ae_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalTimeOneOSQuadratic_pos_of_boundaryMean_ne_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalBetaZeroOSQuadratic_pos_of_c0_ne_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANK_originalBetaZeroOSQuadratic_zero_implies_c0_zero

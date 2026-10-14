import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTransferFiberDetectorKernelV5_GN
import Mathlib.Tactic

/-!
# P4-Q2-GO: true Wilson Hellinger separation and physical-source positive cone

GN expresses the exact two-Wilson-posterior physical source response via the
original one-slab transfer integral and genuine interacting density contrast.
Here strengthen the underlying genuine posterior geometry, still at finite
volume and the original Wilson coupling beta.

For each true spatial link, compare the genuine normalized posterior density
rows p0 and p1 via their squared Hellinger (square-root L²) separation.
The original Wilson FK density upper bound implies

   Q_beta,e(B) <= 4 exp(16 beta) HellingerSq_beta,e(B).

As FX already proves Q > 0 for beta > 0, this gives a strictly positive
Hellinger separation, without assuming nondegeneracy of any source.
At beta = 0 both posterior rows coincide and HellingerSq = 0.

For actual signed physical sources, also give a positive-Wilson-receiver
weighted square-root contrast theorem, together with a sufficient condition
phrased directly using the original Wilson transfer integral. These are
positive-cone certificates, not a proof that the original signed GI/ GN
expectation-gap detector is injective. The remaining bridge requires keeping
the left-response boundary dependence of the true joint half-density.

No fictitious Haar posterior, arbitrary finite source frame, Dobrushin,
volume-uniform Gram frame, C1/C2/C3, H2/H3/H4 or continuum gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 720000

local instance p4Q2GO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2GO_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

private theorem p4Q2GO_trueWilsonPosteriorDensity_continuous
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta hbeta left right e) := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  change Continuous
    (continuousNormalizedExp μ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) beta hbeta left right e))
  exact continuous_continuousNormalizedExp μ _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) beta hbeta left right e)

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μ" => normalizedCompactHaar Gauge
local notation "P0" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
  H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H)
local notation "P1" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
  H 2 (by norm_num) beta hbeta

/-- Squared Hellinger distance between the SAME two original, interacting
Wilson posterior densities appearing in FX/GA/GN. Haar is the reference
integration measure only, not a substitute for the conditional laws. -/
noncomputable def p4Q2GO_originalWilsonTwoPosteriorHellingerSq
    (right : Cfg) (e : Link) : ℝ :=
  ∫ g : Gauge,
    (Real.sqrt (P0 right e g) -
      Real.sqrt (P1 (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g)) ^ 2 ∂μ

/-- The true posterior square-root difference is automatically integrable
at every finite physical background, by compact SU(2) continuity. -/
theorem p4Q2GO_originalWilsonHellingerIntegrable
    (right : Cfg) (e : Link) :
    Integrable
      (fun g : Gauge =>
        (Real.sqrt (P0 right e g) -
          Real.sqrt (P1 (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g)) ^ 2) μ := by
  have h0 := p4Q2GO_trueWilsonPosteriorDensity_continuous
    H beta hbeta (originalWilsonExplicitIdentityBoundary H) right e
  have h1 := p4Q2GO_trueWilsonPosteriorDensity_continuous
    H beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  have hCont :
      Continuous (fun g : Gauge =>
        (Real.sqrt (P0 right e g) -
          Real.sqrt (P1 (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g)) ^ 2) :=
    ((Real.continuous_sqrt.comp h0).sub (Real.continuous_sqrt.comp h1)).pow 2
  exact hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Nonnegative original Wilson posterior Hellinger mass. -/
theorem p4Q2GO_originalWilsonHellinger_nonneg
    (right : Cfg) (e : Link) :
    0 ≤ p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e := by
  unfold p4Q2GO_originalWilsonTwoPosteriorHellingerSq
  exact integral_nonneg (fun g => sq_nonneg _)

/-- Quantitative comparison: the ORIGINAL Wilson posterior squared
density-row distance Q is controlled by its squared Hellinger distance.
The coefficient is independent of the physical volume, link and background. -/
theorem p4Q2GO_originalWilsonContrastQ_le_fourExp_mul_Hellinger
    (right : Cfg) (e : Link) :
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H beta hbeta right e ≤
      (4 * Real.exp (16 * beta)) *
        p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e := by
  let R : Gauge → ℝ := P0 right e
  let S : Gauge → ℝ := P1 (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  let F : Gauge → ℝ := fun g => (R g - S g) ^ 2
  let G : Gauge → ℝ := fun g => (Real.sqrt (R g) - Real.sqrt (S g)) ^ 2
  let C : ℝ := 4 * Real.exp (16 * beta)
  have hR : Continuous R := p4Q2GO_trueWilsonPosteriorDensity_continuous
    H beta hbeta (originalWilsonExplicitIdentityBoundary H) right e
  have hS : Continuous S := p4Q2GO_trueWilsonPosteriorDensity_continuous
    H beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  have hFInt : Integrable F μ :=
    ((hR.sub hS).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hGInt : Integrable G μ :=
    (((Real.continuous_sqrt.comp hR).sub
      (Real.continuous_sqrt.comp hS)).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPoint (g : Gauge) : F g ≤ C * G g := by
    have hRBounds := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e g
    have hSBounds := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g
    have hRNonneg : 0 ≤ R g :=
      (Real.exp_pos (-16 * beta)).le.trans hRBounds.1
    have hSNonneg : 0 ≤ S g :=
      (Real.exp_pos (-16 * beta)).le.trans hSBounds.1
    let x : ℝ := Real.sqrt (R g)
    let y : ℝ := Real.sqrt (S g)
    have hx : x ^ 2 = R g := Real.sq_sqrt hRNonneg
    have hy : y ^ 2 = S g := Real.sq_sqrt hSNonneg
    have hxle : x ^ 2 ≤ Real.exp (16 * beta) := by simpa only [hx] using hRBounds.2
    have hyle : y ^ 2 ≤ Real.exp (16 * beta) := by simpa only [hy] using hSBounds.2
    have hSum : (x + y) ^ 2 ≤ C := by
      dsimp [C]
      nlinarith [sq_nonneg (x - y)]
    change (R g - S g) ^ 2 ≤ C * (x - y) ^ 2
    calc
      (R g - S g) ^ 2 = (x - y) ^ 2 * (x + y) ^ 2 := by
        rw [← hx, ← hy]
        ring
      _ ≤ (x - y) ^ 2 * C :=
        mul_le_mul_of_nonneg_left hSum (sq_nonneg _)
      _ = C * (x - y) ^ 2 := by ring
  change (∫ g, F g ∂μ) ≤ C * (∫ g, G g ∂μ)
  calc
    (∫ g, F g ∂μ) ≤ ∫ g, C * G g ∂μ := by
      apply integral_mono hFInt (hGInt.const_mul _)
      intro g
      exact hPoint g
    _ = C * (∫ g, G g ∂μ) := by rw [integral_const_mul]

/-- The genuine Wilson square-root separation has an explicit bound below
by the original source-independent Q certificate, without a frame input. -/
theorem p4Q2GO_originalWilsonHellinger_ge_Q_div_fourExp
    (right : Cfg) (e : Link) :
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H beta hbeta right e /
        (4 * Real.exp (16 * beta)) ≤
      p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e := by
  have hC : 0 < 4 * Real.exp (16 * beta) :=
    mul_pos (by norm_num) (Real.exp_pos _)
  apply (div_le_iff₀ hC).2
  simpa only [mul_comm] using
    (p4Q2GO_originalWilsonContrastQ_le_fourExp_mul_Hellinger H beta hbeta right e)

/-- At positive frozen Wilson coupling, both true original conditional
posterior laws have a strictly positive Hellinger separation on EVERY
actual physical link and for EVERY physical right environment. -/
theorem p4Q2GO_originalWilsonHellinger_pos
    (hpos : 0 < beta) (right : Cfg) (e : Link) :
    0 < p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e := by
  have hQ : 0 < p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H beta hbeta right e :=
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos H beta hpos right e
  have hC : 0 ≤ (4 * Real.exp (16 * beta)) := by positivity
  have hBound := p4Q2GO_originalWilsonContrastQ_le_fourExp_mul_Hellinger
    H beta hbeta right e
  by_contra hNot
  have hHle : p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e ≤ 0 :=
    le_of_not_gt hNot
  have hCh : (4 * Real.exp (16 * beta)) *
      p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hC hHle
  exact (not_le_of_gt hQ) (hBound.trans hCh)

/-- As frozen beta tends to zero a uniform strictly-positive Hellinger
claim cannot extend to beta = 0: the original two posterior rows coincide. -/
theorem p4Q2GO_originalWilsonHellinger_beta_zero
    (right : Cfg) (e : Link) :
    p4Q2GO_originalWilsonTwoPosteriorHellingerSq H 0 (le_refl 0) right e = 0 := by
  unfold p4Q2GO_originalWilsonTwoPosteriorHellingerSq
  have hPoint (g : Gauge) :
      (Real.sqrt
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
            H 2 (by norm_num) 0 (le_refl 0) (originalWilsonExplicitIdentityBoundary H)
            right e g) -
        Real.sqrt
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
            H 2 (by norm_num) 0 (le_refl 0)
              (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g)) ^ 2 = 0 := by
    rw [p4Q2FK_originalWilsonPosteriorConditionalDensity_beta_zero
        H 2 (by norm_num) (originalWilsonExplicitIdentityBoundary H) right e g,
      p4Q2FK_originalWilsonPosteriorConditionalDensity_beta_zero
        H 2 (by norm_num) (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g]
    ring
  simp only [hPoint, integral_zero]


/-- The genuine physical signed Wilson receiver, not an arbitrary
coefficient family, weights the squared Hellinger contrast for the
two actual interacting left-boundary conditional distributions. -/
noncomputable def p4Q2GO_originalPhysicalReceiverWeightedHellingerMass
    (f : Phys) (left right : Cfg) (e : Link) : ℝ :=
  ∫ g : Gauge,
    normalizedPhysicalOneSlabJointReceiverProductBCF
      H 2 (by norm_num) beta hbeta f (left, Function.update right e g) *
      (Real.sqrt (P0 right e g) -
        Real.sqrt (P1 (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g)) ^ 2 ∂μ

/-- For a physical source whose ORIGINAL signed Wilson receiver is
strictly positive on a true right-link insertion fiber, the square-root
separation carries positive SOURCE-WEIGHTED Haar mass. This is a
positive-cone result, not yet a GI expectation-gap injectivity theorem. -/
theorem p4Q2GO_originalPhysicalReceiverWeightedHellinger_pos
    (hpos : 0 < beta) (f : Phys) (left right : Cfg) (e : Link)
    (hReceiver :
      ∀ g : Gauge, 0 <
        normalizedPhysicalOneSlabJointReceiverProductBCF
          H 2 (by norm_num) beta hbeta f (left, Function.update right e g)) :
    0 < p4Q2GO_originalPhysicalReceiverWeightedHellingerMass
      H beta hbeta f left right e := by
  let R : Gauge → ℝ := P0 right e
  let S : Gauge → ℝ := P1 (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF
    H 2 (by norm_num) beta hbeta f
  let F : Gauge → ℝ := fun g =>
    O (left, Function.update right e g) *
      (Real.sqrt (R g) - Real.sqrt (S g)) ^ 2
  have hUp : Continuous (fun g : Gauge => (left, Function.update right e g)) := by
    fun_prop
  have hR : Continuous R := p4Q2GO_trueWilsonPosteriorDensity_continuous
    H beta hbeta (originalWilsonExplicitIdentityBoundary H) right e
  have hS : Continuous S := p4Q2GO_trueWilsonPosteriorDensity_continuous
    H beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  have hFCont : Continuous F :=
    (O.continuous.comp hUp).mul
      (((Real.continuous_sqrt.comp hR).sub
        (Real.continuous_sqrt.comp hS)).pow 2)
  have hFInt : Integrable F μ :=
    hFCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFNonneg (g : Gauge) : 0 ≤ F g :=
    mul_nonneg (hReceiver g).le (sq_nonneg _)
  have hDifferent :
      R (1 : Gauge) ≠ S 1 ∨
      R (specialUnitaryTwoRotation Real.pi) ≠
        S (specialUnitaryTwoRotation Real.pi) := by
    exact p4Q2FS_originalSU2EveryLinkTruePosteriorDensity_leftSensitive
      H beta hpos right e
  obtain ⟨g, hDifferentAtG⟩ : ∃ g : Gauge, R g ≠ S g := by
    rcases hDifferent with hOne | hRot
    · exact ⟨1, hOne⟩
    · exact ⟨specialUnitaryTwoRotation Real.pi, hRot⟩
  have hRNonneg : 0 ≤ R g := by
    have h := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
        (originalWilsonExplicitIdentityBoundary H) right e g
    exact (Real.exp_pos _).le.trans h.1
  have hSNonneg : 0 ≤ S g := by
    have h := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g
    exact (Real.exp_pos _).le.trans h.1
  have hSqrtDifferent : Real.sqrt (R g) ≠ Real.sqrt (S g) := by
    intro hEq
    apply hDifferentAtG
    calc
      R g = (Real.sqrt (R g)) ^ 2 := (Real.sq_sqrt hRNonneg).symm
      _ = (Real.sqrt (S g)) ^ 2 := by rw [hEq]
      _ = S g := Real.sq_sqrt hSNonneg
  have hFNe : F g ≠ 0 := by
    exact mul_ne_zero (hReceiver g).ne'
      (pow_ne_zero 2 (sub_ne_zero.mpr hSqrtDifferent))
  have hSupportOpen : IsOpen (Function.support F) := by
    change IsOpen (F ⁻¹' ({0} : Set ℝ)ᶜ)
    exact isClosed_singleton.isOpen_compl.preimage hFCont
  have hSupportPos : 0 < μ (Function.support F) :=
    hSupportOpen.measure_pos μ ⟨g, hFNe⟩
  change 0 < ∫ g, F g ∂μ
  rw [integral_pos_iff_support_of_nonneg]
  · exact hSupportPos
  · exact hFNonneg
  · exact hFInt

/-- Replace a hypothetical source-detection/frame assumption by a
checkable ORIGINAL Wilson physical transfer positivity condition.
For such a physical input, the genuine receiver-weighted two-posterior
Hellinger certificate is strictly positive. This remains distinct from
the signed GI detector and is not misreported as its injectivity. -/
theorem p4Q2GO_originalPhysicalTransferPositive_implies_weightedHellinger_pos
    (hpos : 0 < beta) (f : Phys) (left right : Cfg) (e : Link)
    (hTransfer :
      ∀ g : Gauge, 0 <
        decomposableOneSliceTransferIntegral H 2 beta f
          (Function.update right e g)) :
    0 < p4Q2GO_originalPhysicalReceiverWeightedHellingerMass
      H beta hbeta f left right e := by
  have hL : 0 <
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖⁻¹ :=
    inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) beta hbeta)
  have hReceiver (g : Gauge) : 0 <
      normalizedPhysicalOneSlabJointReceiverProductBCF
        H 2 (by norm_num) beta hbeta f
        (left, Function.update right e g) := by
    rw [p4Q2GN_originalReceiver_eq_transferIntegral]
    exact div_pos
      (mul_pos (pow_pos hL 2) (hTransfer g))
      (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta
        (left, Function.update right e g))
  exact p4Q2GO_originalPhysicalReceiverWeightedHellinger_pos
    H beta hbeta hpos f left right e hReceiver

end Frozen

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GO_originalWilsonHellingerIntegrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GO_originalWilsonHellinger_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GO_originalWilsonContrastQ_le_fourExp_mul_Hellinger
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GO_originalWilsonHellinger_ge_Q_div_fourExp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GO_originalWilsonHellinger_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GO_originalWilsonHellinger_beta_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GO_originalPhysicalReceiverWeightedHellinger_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GO_originalPhysicalTransferPositive_implies_weightedHellinger_pos

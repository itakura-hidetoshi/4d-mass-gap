import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointHalfDensityRatioGIEnvelopeV5_LU
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkWeightHarnack
import Mathlib.Tactic

/-!
# P4-Q2-LV — original physical Wilson joint density one-link Harnack

LU represents the exact original interacting-Wilson JH GI detector by
the genuine one-link joint half-density ratio
  R(e,z,g) = s(z) / s(z.left, update z.right e g).

Here we join two PRE-EXISTING genuinely physical Wilson results:
  (a) the original canonical continuous-vacuum joint density is the
      original Perron Ω(left) K_beta(left,right) Ω(right) / ||T||;
  (b) the actual complete Wilson kernel and continuous Perron vacuum
      each obey a volume-independent one-link comparison exp(8b).

Their product is the true pointwise joint-density Harnack factor exp(16b).
Taking the positive square root yields
  0 < R(e,z,g) <= exp(8b),
  ||R(e,z,.)||∞ <= exp(8b)
for EVERY finite volume H, true context/link and SU(2) insertion.

Thus LU improves to the ACTUAL physical JH operator envelope
  ||G(e,z)|| <= ||T||⁻¹ exp(8b) [exp(16b)-exp(-16b)],
with no joint-half-density supremum or context/link-dependent ratio.

LR/LQ/LP then yield genuine local physical finite-H coercivity with
denominator 10 N_H² [||T||⁻¹ exp(8b) contrast]², strict positivity
derived from the original nonzero physical GI determinant.

The factor exp(8b) is truly volume-independent; the remaining transfer
normalization ||T||⁻¹, original global GI minor and N_H can depend on H.
NO H-uniform κ, H1-C3 strong limit, continuum YM or mass gap is asserted.

No independent-Haar posterior, artificial source/rank, Dobrushin,
sorry/admit, or additional axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num) b hb
local notation "G" => p4Q2JH_originalGIResponseCLM H b hb
local notation "B" => p4Q2LU_originalGIContextRatioEnvelope H b hb

/-- Pointwise Harnack inequality for the LITERAL original normalized
physical Perron/Wilson joint density under a single right-link change.
Its exp(16b) constant comes from TWO genuine original exp(8b) factors:
the full Wilson slab kernel and the continuous physical Perron vacuum.
No artificial probability law and no factor counting lattice volume. -/
theorem p4Q2LV_originalJointDensity_rightLink_harnack
    (left right : Cfg) (e : Link) (g h : Gauge) :
    rho (left, Function.update right e g) ≤
      Real.exp (16 * b) * rho (left, Function.update right e h) := by
  have hweight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal_update_right_le_exp_sixteen_mul_update_right
      H 2 (by norm_num) b hb left right e g h
  change rho (left, Function.update right e g) ≤
    Real.exp (16 * b) * rho (left, Function.update right e h) at hweight
  exact hweight

/-- The original physical continuous joint half-density squares to the
original normalized interacting Wilson/Perron joint density, pointwise. -/
theorem p4Q2LV_originalJointHalfDensity_sq_eq_jointDensity
    (z : Cfg × Cfg) :
    (s z)^2 = rho z := by
  change (Real.sqrt (rho z))^2 = rho z
  exact Real.sq_sqrt
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb z).le

/-- POSITIVE original one-link joint square-root ratios are bounded by
exp(8b), independently of H, the boundary, and the actual physical link. -/
theorem p4Q2LV_originalJointHalfDensityRatio_pointwise_le_exp_eight
    (e : Link) (z : Cfg × Cfg) (g : Gauge) :
    p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z g ≤
      Real.exp (8 * b) := by
  have hself : Function.update z.2 e (z.2 e) = z.2 := by
    classical
    funext link
    by_cases h : link = e
    · subst link
      simp
    · simp [h]
  have hDensity :=
    p4Q2LV_originalJointDensity_rightLink_harnack
      H b hb z.1 z.2 e (z.2 e) g
  rw [hself] at hDensity
  have hSq0 := p4Q2LV_originalJointHalfDensity_sq_eq_jointDensity H b hb z
  have hSq1 :=
    p4Q2LV_originalJointHalfDensity_sq_eq_jointDensity H b hb
      (z.1, Function.update z.2 e g)
  have hExp : (Real.exp (8 * b))^2 = Real.exp (16 * b) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hTargetEq :
      (Real.exp (8 * b) * s (z.1, Function.update z.2 e g))^2 =
        Real.exp (16 * b) * rho (z.1, Function.update z.2 e g) := by
    rw [mul_pow, hExp, hSq1]
  have hSq :
      (s z)^2 ≤ (Real.exp (8 * b) * s (z.1, Function.update z.2 e g))^2 := by
    calc
      (s z)^2 = rho z := hSq0
      _ ≤ Real.exp (16 * b) * rho (z.1, Function.update z.2 e g) :=
        hDensity
      _ = (Real.exp (8 * b) * s (z.1, Function.update z.2 e g))^2 :=
        hTargetEq.symm
  have h0 : 0 ≤ s z :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb z).le
  have h1 : 0 ≤ Real.exp (8 * b) * s (z.1, Function.update z.2 e g) :=
    mul_nonneg (Real.exp_pos _).le
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
        (z.1, Function.update z.2 e g)).le
  have hBound : s z ≤ Real.exp (8 * b) *
      s (z.1, Function.update z.2 e g) := by
    nlinarith [hSq]
  rw [p4Q2LU_originalJointHalfDensityUpdateRatio_apply]
  exact (div_le_iff₀
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
      (z.1, Function.update z.2 e g))).2 hBound

/-- Genuine volume-independent sup bound for LU's exact right-link
half-density ratio, using genuine original Wilson/Perron Harnack. -/
theorem p4Q2LV_originalJointHalfDensityRatio_norm_le_exp_eight
    (e : Link) (z : Cfg × Cfg) :
    ‖p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z‖ ≤
      Real.exp (8 * b) := by
  let R : C(Gauge, ℝ) := p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z
  change ‖R‖ ≤ Real.exp (8 * b)
  apply (ContinuousMap.norm_le R (Real.exp_pos _).le).2
  intro g
  have hPos : 0 < R g := by
    rw [p4Q2LU_originalJointHalfDensityUpdateRatio_apply]
    exact div_pos
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb z)
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
        (z.1, Function.update z.2 e g))
  have hBound :
      R g ≤ Real.exp (8 * b) :=
    p4Q2LV_originalJointHalfDensityRatio_pointwise_le_exp_eight H b hb e z g
  simpa only [Real.norm_eq_abs, abs_of_pos hPos] using hBound

/-- Actual Wilson JH detector envelope, uniform over the PHYSICAL link
and boundary context at fixed H,b. Note that the actual ||T|| inverse
has not been shown uniformly bounded over lattice volumes H. -/
noncomputable def p4Q2LV_originalUniformContextGIEnvelope : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ *
    (Real.exp (8 * b) * p4Q2LS_originalPosteriorContrastEnvelope b)

local notation "C" => p4Q2LV_originalUniformContextGIEnvelope H b hb

/-- The original LU physical detector envelope is controlled by the
genuinely volume-independent right-link Harnack factor exp(8b). -/
theorem p4Q2LV_originalGIContextRatioEnvelope_le_uniformContext
    (e : Link) (z : Cfg × Cfg) :
    B e z ≤ C := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb
  let R := p4Q2LU_originalJointHalfDensityUpdateRatio H b hb e z
  let E := p4Q2LS_originalPosteriorContrastEnvelope b
  have hR : ‖R‖ ≤ Real.exp (8 * b) :=
    p4Q2LV_originalJointHalfDensityRatio_norm_le_exp_eight H b hb e z
  have hE : 0 ≤ E := p4Q2LS_originalPosteriorContrastEnvelope_nonneg b hb
  have hT : 0 ≤ ‖T‖⁻¹ := inv_nonneg.mpr (norm_nonneg T)
  change ‖T‖⁻¹ * (‖R‖ * E) ≤ ‖T‖⁻¹ * (Real.exp (8 * b) * E)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hR hE) hT

/-- True interacting-posterior JH functional norm has NO pointwise
half-density factor left. Its only remaining potentially H-dependent
envelope factor is the actual transfer operator inverse norm. -/
theorem p4Q2LV_originalGIResponse_norm_le_uniformContext
    (e : Link) (z : Cfg × Cfg) :
    ‖G e z‖ ≤ C := by
  exact (p4Q2LU_originalGIResponse_norm_le_contextRatioEnvelope H b hb e z).trans
    (p4Q2LV_originalGIContextRatioEnvelope_le_uniformContext H b hb e z)

/-- Same context-independent Harnack envelope bounds the pair of actual
original JH detector norms, with LR's exact 1²+2²=5 local source loss. -/
theorem p4Q2LV_originalGIOpNormSq_sum_le_uniformEnvelopeSq
    (e e' : Link) (z z' : Cfg × Cfg) :
    5 * (‖G e z‖^2 + ‖G e' z'‖^2) ≤ 10 * C^2 := by
  have h1 := p4Q2LV_originalGIResponse_norm_le_uniformContext H b hb e z
  have h2 := p4Q2LV_originalGIResponse_norm_le_uniformContext H b hb e' z'
  have hC : 0 ≤ C := (norm_nonneg (G e z)).trans h1
  have hs1 : ‖G e z‖^2 ≤ C^2 := by
    have hp : 0 ≤ (C - ‖G e z‖) * (C + ‖G e z‖) :=
      mul_nonneg (sub_nonneg.mpr h1)
        (add_nonneg hC (norm_nonneg _))
    nlinarith [hp]
  have hs2 : ‖G e' z'‖^2 ≤ C^2 := by
    have hp : 0 ≤ (C - ‖G e' z'‖) * (C + ‖G e' z'‖) :=
      mul_nonneg (sub_nonneg.mpr h2)
        (add_nonneg hC (norm_nonneg _))
    nlinarith [hp]
  nlinarith [hs1, hs2]

/-- Exact original four-entry local GI Frobenius denominator is controlled
by the explicit volume-independent SU(2) half-density ratio exponent. -/
theorem p4Q2LV_originalLocalGIFrobeniusSq_le_ten_uniformEnvelopeSq
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p ≤
      10 * C^2 := by
  exact (p4Q2LR_originalLocalGIFrobeniusSq_le_five_opNormSq
    H b hb e e' z z' p).trans
      (p4Q2LV_originalGIOpNormSq_sum_le_uniformEnvelopeSq
        H b hb e e' z z')

/-- No new nonvanishing assumption: the original physical GI local
minor forces the new 10 C² denominator strictly positive. -/
theorem p4Q2LV_originalGI_uniformEnvelopeSq_pos_of_local_minor
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    0 < 10 * C^2 := by
  exact (p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
    H b hb e e' z z' p hminor).trans_le
      (p4Q2LV_originalGIOpNormSq_sum_le_uniformEnvelopeSq
        H b hb e e' z z')

/-- Quantitative authentic physical local Wilson GI lower bound with
NO joint inverse-density or selected-context ratio in its denominator:
  κ_p >= Δ_total² / [10 N_H² C(H,b)²].
C retains exactly the true physical transfer normalization. -/
theorem p4Q2LV_originalLocalGI_coercivity_ge_global_uniformContext_floor
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0)
    (hcount : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ))
    (hAvg : |p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'| /
      (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ≤
      |p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p|) :
    (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
      ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
        (10 * C^2)) ≤
      p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb e e' z z' p := by
  let total := p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'
  let n : ℝ := (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
  let D : ℝ := 5 * (‖G e z‖^2 + ‖G e' z'‖^2)
  let M : ℝ := 10 * C^2
  have hD : 0 < D :=
    p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
      H b hb e e' z z' p hminor
  have hDM : D ≤ M :=
    p4Q2LV_originalGIOpNormSq_sum_le_uniformEnvelopeSq H b hb e e' z z'
  have hM : 0 < M := lt_of_lt_of_le hD hDM
  have hn2 : 0 < n^2 := sq_pos_of_pos hcount
  have hDden : 0 < n^2 * D := mul_pos hn2 hD
  have hMden : 0 < n^2 * M := mul_pos hn2 hM
  have hden : n^2 * D ≤ n^2 * M :=
    mul_le_mul_of_nonneg_left hDM (sq_nonneg n)
  have hDiv : total^2 / (n^2 * M) ≤ total^2 / (n^2 * D) :=
    (div_le_div_iff₀ hMden hDden).2
      (mul_le_mul_of_nonneg_left hden (sq_nonneg total))
  exact hDiv.trans
    (p4Q2LR_originalLocalGI_coercivity_ge_global_opNorm_floor
      H b hb e e' z z' p hminor hcount hAvg)

/-- Original finite-volume Gauss-law two-source witness after eliminating
all true context/link half-density factors from the upper denominator.
Remaining H-dependence: ||T||⁻¹, original Δ_total and real N_H. -/
theorem p4Q2LV_originalPhysicalLocalGI_exists_uniformContext_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
      0 < 10 * C^2 ∧
      0 < p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p ∧
      (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
        ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
          (10 * C^2)) ≤
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb e e' z z' p ∧
      ∀ x y : ℝ,
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hpos e e' left₀ right₀
  have hlocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0 := by
    intro hz
    simp [hz] at hpPos
  have hMpos :=
    p4Q2LV_originalGI_uniformEnvelopeSq_pos_of_local_minor
      H b hb e e' z z' p hlocal
  obtain ⟨hκ, hBound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hlocal
  have hFloor :=
    p4Q2LV_originalLocalGI_coercivity_ge_global_uniformContext_floor
      H b hb e e' z z' p hlocal hn hAvg
  exact ⟨z, z', p, hp, hn, hMpos, hκ, hFloor, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalJointDensity_rightLink_harnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalJointHalfDensity_sq_eq_jointDensity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalJointHalfDensityRatio_pointwise_le_exp_eight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalJointHalfDensityRatio_norm_le_exp_eight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalGIContextRatioEnvelope_le_uniformContext
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalGIResponse_norm_le_uniformContext
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalGIOpNormSq_sum_le_uniformEnvelopeSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalLocalGIFrobeniusSq_le_ten_uniformEnvelopeSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalGI_uniformEnvelopeSq_pos_of_local_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalLocalGI_coercivity_ge_global_uniformContext_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LV_originalPhysicalLocalGI_exists_uniformContext_floor

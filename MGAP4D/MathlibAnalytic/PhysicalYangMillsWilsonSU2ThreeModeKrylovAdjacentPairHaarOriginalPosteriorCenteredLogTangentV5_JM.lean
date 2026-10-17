import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorWeakFrozenNoGoV5_JL
import Mathlib.Tactic

/-!
# P4-Q2-JM: exact strong Haar-L2 tangent of the genuine centered Wilson posterior log ratio

The ORIGINAL two interacting Wilson conditional posterior densities at a
physical SU(2) spatial link are kept unchanged. The frozen physical vacuum
and the two normalizing partition functions need NOT be differentiable in
beta. FR and GA already establish that the difference of logarithmic
posterior row ratios at two SU(2) link insertions cancels those
nonlocal/normalizing factors EXACTLY.

Here both genuine logarithmic posterior densities are continuous on the
physical compact SU(2) group by their true positive Wilson normalization.
Centering their difference by normalized reference Haar annihilates the
unobservable additive constant. We obtain an EXACT identity in the
Banach space of continuous functions, for EVERY nonnegative frozen beta:

  centered(log p0_beta - log p1_beta) = -beta * centered(D_SU2).

The same equality in the actual compact SU(2) Haar L2 provides a strong,
coupling-independent nonzero difference quotient for every beta>0.
The squared Haar norm of this genuine centered log contrast is exactly
beta^2 times the original strictly positive SU(2) Wilson variance.

These are physical log-posterior contrasts, NOT a claim that the UNLOGGED
density contrast or the original JK spatial Wilson GI detector has
been differentiated. No independent posterior, H1-C3 closure, continuum
Yang-Mills construction or mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "L" => ContinuousMap.toLp 2 nu ℝ

/-- Genuine physical interacting-Wilson POSTERIOR log-row difference,
as a continuous function on the actual compact SU(2) link group. -/
noncomputable def p4Q2JM_originalPosteriorLogContrastContinuous
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    C(Gauge, ℝ) := by
  let p0 : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) b hb
      (originalWilsonExplicitIdentityBoundary H) right e
  let p1 : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  have hp0 : Continuous p0 := by
    change Continuous (continuousNormalizedExp nu
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) b hb
        (originalWilsonExplicitIdentityBoundary H) right e))
    exact continuous_continuousNormalizedExp nu _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) b hb
        (originalWilsonExplicitIdentityBoundary H) right e)
  have hp1 : Continuous p1 := by
    change Continuous (continuousNormalizedExp nu
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) b hb
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
    exact continuous_continuousNormalizedExp nu _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) b hb
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)
  have h0 (g : Gauge) : p0 g ≠ 0 :=
    ((Real.exp_pos _).trans_le
      (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
        H 2 (by norm_num) b hb
        (originalWilsonExplicitIdentityBoundary H) right e g).1).ne'
  have h1 (g : Gauge) : p1 g ≠ 0 :=
    ((Real.exp_pos _).trans_le
      (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
        H 2 (by norm_num) b hb
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g).1).ne'
  refine ⟨p4Q2GA_originalSU2WilsonPosteriorLeftLogDensityContrast
    H b hb right e, ?_⟩
  change Continuous (fun g => Real.log (p0 g) - Real.log (p1 g))
  exact (hp0.log h0).sub (hp1.log h1)

/-- The true temporal one-link SU(2) crossing-Wilson action difference,
continuous on the whole physical link group. -/
noncomputable def p4Q2JM_temporalWilsonContinuous : C(Gauge, ℝ) :=
  ⟨p4Q2FZ_originalSU2TemporalWilsonContrast,
    p4Q2FZ_originalSU2TemporalWilsonContrast_continuous⟩

/-- Actual normalized-Haar-centered SU(2) temporal Wilson contrast. -/
noncomputable def p4Q2JM_temporalWilsonCentered : C(Gauge, ℝ) :=
  p4Q2JM_temporalWilsonContinuous -
    (∫ g : Gauge, p4Q2JM_temporalWilsonContinuous g ∂nu) •
      (1 : C(Gauge, ℝ))

/-- Actual normalized-Haar-centered log difference of the TWO ORIGINAL
interacting SU(2) Wilson conditional posterior densities. -/
noncomputable def p4Q2JM_originalPosteriorLogCentered
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    C(Gauge, ℝ) :=
  p4Q2JM_originalPosteriorLogContrastContinuous H b hb right e -
    (∫ g : Gauge,
      p4Q2JM_originalPosteriorLogContrastContinuous H b hb right e g ∂nu) •
      (1 : C(Gauge, ℝ))

/-- EXACT genuine physical equality in the SU(2) Banach continuous-map
carrier. All unknown Perron vacuum and Wilson posterior normalizers
cancel WITHOUT differentiating any of them. -/
theorem p4Q2JM_originalPosteriorLogCentered_eq_negBeta_WilsonCentered
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    p4Q2JM_originalPosteriorLogCentered H b hb right e =
      (-b) • p4Q2JM_temporalWilsonCentered := by
  let F := p4Q2JM_originalPosteriorLogContrastContinuous H b hb right e
  let T := p4Q2JM_temporalWilsonContinuous
  let k : ℝ := F (1 : Gauge) + b * T (1 : Gauge)
  have hF (g : Gauge) : F g = (-b) * T g + k := by
    have hRel :=
      p4Q2GA_originalSU2WilsonPosteriorLogContrast_relative_exact
        H b hb right e g (1 : Gauge)
    change F g - F 1 = -b * (T g - T 1) at hRel
    dsimp only [k]
    nlinarith [hRel]
  have hTInt : Integrable (fun g : Gauge => T g) nu :=
    T.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegral :
      (∫ g : Gauge, F g ∂nu) =
        (-b) * (∫ g : Gauge, T g ∂nu) + k := by
    calc
      (∫ g : Gauge, F g ∂nu) =
          ∫ g : Gauge, ((-b) * T g + k) ∂nu := by
        apply integral_congr_ae
        filter_upwards with g
        exact hF g
      _ = (-b) * (∫ g : Gauge, T g ∂nu) + k := by
        rw [integral_add (hTInt.const_mul _) (integrable_const _)]
        rw [integral_const_mul]
        simp
  ext g
  change F g - (∫ x : Gauge, F x ∂nu) =
    (-b) * (T g - (∫ x : Gauge, T x ∂nu))
  rw [hF g, hIntegral]
  ring

/-- Exactly quadratic Haar squared norm of the ACTUAL original
centered log posterior contrast; the coefficient is the genuine,
strictly positive SU(2) temporal Wilson Haar variance from FZ. -/
theorem p4Q2JM_originalPosteriorLogCentered_HaarSq_exact
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    (∫ g : Gauge,
      (p4Q2JM_originalPosteriorLogCentered H b hb right e g) ^ 2 ∂nu) =
      b ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance := by
  rw [p4Q2JM_originalPosteriorLogCentered_eq_negBeta_WilsonCentered]
  let D := p4Q2JM_temporalWilsonCentered
  change (∫ g : Gauge, ((-b) * D g) ^ 2 ∂nu) =
    b ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance
  calc
    (∫ g : Gauge, ((-b) * D g) ^ 2 ∂nu) =
        ∫ g : Gauge, b ^ 2 * (D g) ^ 2 ∂nu := by
      apply integral_congr_ae
      filter_upwards with g
      ring
    _ = b ^ 2 * (∫ g : Gauge, (D g) ^ 2 ∂nu) := by
      rw [integral_const_mul]
    _ = b ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance := rfl

/-- The actual Haar-centered temporal Wilson action is nonzero as a
continuous observable: its values at the two literal SU(2) insertions
remain separated by FOUR, regardless of subtracting the Haar mean. -/
theorem p4Q2JM_temporalWilsonCentered_ne_zero :
    p4Q2JM_temporalWilsonCentered ≠ 0 := by
  intro hz
  have h0 := congrArg (fun f : C(Gauge, ℝ) => f (1 : Gauge)) hz
  have hR := congrArg
    (fun f : C(Gauge, ℝ) => f (specialUnitaryTwoRotation Real.pi)) hz
  change p4Q2FZ_originalSU2TemporalWilsonContrast 1 -
    (∫ g : Gauge, p4Q2FZ_originalSU2TemporalWilsonContrast g ∂nu) = 0 at h0
  change p4Q2FZ_originalSU2TemporalWilsonContrast
    (specialUnitaryTwoRotation Real.pi) -
    (∫ g : Gauge, p4Q2FZ_originalSU2TemporalWilsonContrast g ∂nu) = 0 at hR
  rw [p4Q2FZ_originalSU2TemporalWilsonContrast_one] at h0
  rw [p4Q2FZ_originalSU2TemporalWilsonContrast_rotation] at hR
  linarith

/-- The ACTUAL normalized compact Haar has full support, so the
nonconstant centered SU(2) Wilson observable has a nonzero Haar-L2
representative; no point evaluation of L2 equivalence classes. -/
theorem p4Q2JM_temporalWilsonCentered_HaarLp_ne_zero :
    L p4Q2JM_temporalWilsonCentered ≠ 0 := by
  intro h
  have h0 : p4Q2JM_temporalWilsonCentered = 0 :=
    (ContinuousMap.toLp_injective (p := 2) (μ := nu) (𝕜 := ℝ))
      (by simpa only [map_zero] using h)
  exact p4Q2JM_temporalWilsonCentered_ne_zero h0

/-- EXACT strong Haar-L2 relation, not merely a pointwise derivative
and not an operator-norm claim about the full Wilson transfer. -/
theorem p4Q2JM_originalPosteriorLogCentered_HaarLp_eq
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    L (p4Q2JM_originalPosteriorLogCentered H b hb right e) =
      (-b) • L p4Q2JM_temporalWilsonCentered := by
  rw [p4Q2JM_originalPosteriorLogCentered_eq_negBeta_WilsonCentered,
    map_smul]

/-- At strictly positive frozen beta, even the TRUE normalized
interacting posterior CENTERED LOG RATIO has a nonzero Haar-L2 vector.
This differs from the JK unlogged spatial Wilson GI visibility problem. -/
theorem p4Q2JM_originalPosteriorLogCentered_HaarLp_ne_zero_of_pos
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    L (p4Q2JM_originalPosteriorLogCentered H b hb.le right e) ≠ 0 := by
  rw [p4Q2JM_originalPosteriorLogCentered_HaarLp_eq]
  exact smul_ne_zero (neg_ne_zero.mpr hb.ne')
    p4Q2JM_temporalWilsonCentered_HaarLp_ne_zero

/-- Full STRONG Haar-L2 difference quotient of the centered genuine
log posterior contrast. The actual Wilson slope is precisely the
nonzero universal temporal crossing action, independent of the
volume, the selected physical link and the right context. -/
theorem p4Q2JM_originalPosteriorLogCentered_HaarLp_quotient_exact
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    b⁻¹ • L (p4Q2JM_originalPosteriorLogCentered H b hb.le right e) =
      -L p4Q2JM_temporalWilsonCentered := by
  rw [p4Q2JM_originalPosteriorLogCentered_HaarLp_eq, smul_smul]
  have hs : b⁻¹ * (-b) = -1 := by
    field_simp [hb.ne']
    ring
  rw [hs]
  exact neg_one_smul ℝ _

/-- The SAME exact original normalized interacting Wilson posterior
log-odds crossing, evaluated at the two genuine SU(2) insertions:
a universal, volume/link/context-independent 4*b. -/
theorem p4Q2JM_originalPosteriorLogCrossing_one_rotation_eq_fourBeta
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    p4Q2JM_originalPosteriorLogContrastContinuous H b hb right e
        (1 : Gauge) -
      p4Q2JM_originalPosteriorLogContrastContinuous H b hb right e
        (specialUnitaryTwoRotation Real.pi) = 4 * b := by
  have h :=
    p4Q2GA_originalSU2WilsonPosteriorLogContrast_relative_exact
      H b hb right e (1 : Gauge) (specialUnitaryTwoRotation Real.pi)
  change
    p4Q2JM_originalPosteriorLogContrastContinuous H b hb right e 1 -
    p4Q2JM_originalPosteriorLogContrastContinuous H b hb right e
      (specialUnitaryTwoRotation Real.pi) =
      -b * (p4Q2FZ_originalSU2TemporalWilsonContrast 1 -
        p4Q2FZ_originalSU2TemporalWilsonContrast
          (specialUnitaryTwoRotation Real.pi)) at h
  rw [p4Q2FZ_originalSU2TemporalWilsonContrast_one,
      p4Q2FZ_originalSU2TemporalWilsonContrast_rotation] at h
  nlinarith [h]

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JM_originalPosteriorLogCentered_eq_negBeta_WilsonCentered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JM_originalPosteriorLogCentered_HaarSq_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JM_temporalWilsonCentered_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JM_temporalWilsonCentered_HaarLp_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JM_originalPosteriorLogCentered_HaarLp_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JM_originalPosteriorLogCentered_HaarLp_ne_zero_of_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JM_originalPosteriorLogCentered_HaarLp_quotient_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JM_originalPosteriorLogCrossing_one_rotation_eq_fourBeta

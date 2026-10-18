import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverTemporalCovarianceV5_JQ
import Mathlib.Tactic

/-!
# P4-Q2-JS: original physical GI receiver span versus literal SU(2) posterior detection

JP proves that the TWO original interacting Wilson posteriors strictly detect
the literal SU(2) temporal Wilson contrast D for every coupling in one
volume-independent small positive interval. JQ identifies their test gap
with the real Gauss-law physical Wilson receiver of every actual physical
Hilbert source, including its original strictly positive joint weight.

Here we form the actual real linear span of the ORIGINAL physical source
receivers at ONE fixed right boundary and physical link (allowing all
physical Hilbert sources and original left boundaries), plus the constant
receiver which is invisible to normalized posterior differences.

We do NOT assume a hypothetical rank, a source frame, density, or an
independent-Haar conditional posterior. We prove the following precise
obstruction, directly from the original Wilson physical formulas:

If every original physical GI expectation gap vanishes at that link and
right context, then the genuine temporal Wilson contrast D CANNOT lie
in the algebraic span of the available physical receivers and constants.

Equivalently, representation of D by actual physical receivers modulo
constants is sufficient to force SOME ORIGINAL physical GI response
nonzero. The representation itself is NOT asserted and remains a concrete
physical Wilson receiver obstruction, particularly for the distinct
spatial-action two-context minor of JK.

No H1-C3 closure, scale-independent mass floor, or continuum YM gap
is claimed. No sorry, admit, or newly postulated axiom is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen

variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge

/-- The TRUE difference of the two original normalized interacting Wilson
posteriors, integrated against a test, is a real linear map. -/
noncomputable def p4Q2JS_originalPosteriorTestLinearMap
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    C(Gauge, ℝ) →ₗ[ℝ] ℝ := by
  let P : C(Gauge, ℝ) :=
    p4Q2JN2_originalPosteriorDensityContrastContinuous H b hb right e
  refine
    { toFun := fun F => ∫ g : Gauge, F g * P g ∂nu
      map_add' := ?_
      map_smul' := ?_ }
  · intro F G
    have hFI : Integrable (fun g : Gauge => F g * P g) nu :=
      (F.continuous.mul P.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hGI : Integrable (fun g : Gauge => G g * P g) nu :=
      (G.continuous.mul P.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    change (∫ g : Gauge, (F + G) g * P g ∂nu) =
      (∫ g : Gauge, F g * P g ∂nu) +
        (∫ g : Gauge, G g * P g ∂nu)
    simp only [ContinuousMap.add_apply]
    calc
      (∫ g : Gauge, (F g + G g) * P g ∂nu) =
          ∫ g : Gauge, F g * P g + G g * P g ∂nu := by
            apply integral_congr_ae
            filter_upwards with g
            ring
      _ = (∫ g : Gauge, F g * P g ∂nu) +
          (∫ g : Gauge, G g * P g ∂nu) :=
        integral_add hFI hGI
  · intro c F
    change (∫ g : Gauge, (c • F) g * P g ∂nu) =
      c • (∫ g : Gauge, F g * P g ∂nu)
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    calc
      (∫ g : Gauge, (c * F g) * P g ∂nu) =
          ∫ g : Gauge, c * (F g * P g) ∂nu := by
            apply integral_congr_ae
            filter_upwards with g
            ring
      _ = c * (∫ g : Gauge, F g * P g ∂nu) :=
        integral_const_mul c _

/-- This is not an abstract test functional: exactly the JP gap of
the two original normalized interacting Wilson conditional laws. -/
theorem p4Q2JS_originalPosteriorTestLinearMap_eq_JP
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) :
    p4Q2JS_originalPosteriorTestLinearMap H b hb right e F =
      p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e F := by
  rfl

/-- The scalar constant direction is invisible because BOTH actual
interacting Wilson posteriors have total normalized mass one. -/
theorem p4Q2JS_originalPosteriorTestLinearMap_one_eq_zero
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    p4Q2JS_originalPosteriorTestLinearMap H b hb right e
        (1 : C(Gauge, ℝ)) = 0 := by
  rw [p4Q2JS_originalPosteriorTestLinearMap_eq_JP]
  simpa only [p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap,
    ContinuousMap.one_apply, one_mul] using
    (p4Q2JP_originalPosteriorContrast_HaarMean_zero H b hb right e)

/-- The REAL physical receiver module at a fixed physical link and
right spatial SU(2) configuration. Sources are ACTUAL Gauss-law Hilbert
vectors; the left full spatial context is allowed to vary. Constants
are added because posterior differences kill them exactly. -/
noncomputable def p4Q2JS_originalPhysicalReceiverSpan
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    Submodule ℝ C(Gauge, ℝ) :=
  Submodule.span ℝ (Set.insert (1 : C(Gauge, ℝ))
    (Set.range (fun p : Phys × Cfg =>
      p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb p.1 e (p.2, right))))

/-- Without adding ANY physical-frame/rank hypothesis, prove that
vanishing of all genuine physical GI expectations forces the entire
span of actual physical SU(2) receivers (and the constant mode) into
the actual interacting Wilson posterior test kernel. -/
theorem p4Q2JS_originalPhysicalReceiverSpan_le_actualPosteriorKernel
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (hzero : ∀ f : Phys, ∀ left : Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb f e (left, right) = 0) :
    p4Q2JS_originalPhysicalReceiverSpan H b hb right e ≤
      (p4Q2JS_originalPosteriorTestLinearMap H b hb right e).ker := by
  apply Submodule.span_le.mpr
  intro F hF
  rcases Set.mem_insert_iff.mp hF with hOne | hRange
  · subst F
    change p4Q2JS_originalPosteriorTestLinearMap H b hb right e
      (1 : C(Gauge, ℝ)) = 0
    exact p4Q2JS_originalPosteriorTestLinearMap_one_eq_zero H b hb right e
  · rcases hRange with ⟨⟨f, left⟩, rfl⟩
    have hq : p4Q2JQ_originalPhysicalGIDensityWeight H b hb
        (left, right) ≠ 0 :=
      (p4Q2JQ_originalPhysicalGIDensityWeight_pos H b hb
        (left, right)).ne'
    have hGI := p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div
      H b hb f e (left, right)
    rw [hzero f left] at hGI
    have hMoment :
        p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
          H b hb right e
          (p4Q2JQ_originalPhysicalSourceLinkReceiver
            H b hb f e (left, right)) = 0 := by
      field_simp [hq] at hGI
      linarith
    change p4Q2JS_originalPosteriorTestLinearMap H b hb right e
      (p4Q2JQ_originalPhysicalSourceLinkReceiver
        H b hb f e (left, right)) = 0
    rw [p4Q2JS_originalPosteriorTestLinearMap_eq_JP]
    exact hMoment

/-- UNCONDITIONAL physical obstruction implication in the authentic
weak-coupling Wilson posterior model: if the original physical GI
detector is identically blind to all its actual source receivers, D
is NOT representable by those receivers even after adding constants. -/
theorem p4Q2JS_temporalWilson_not_mem_physicalReceiverSpan_of_allGI_zero
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link)
    (hzero : ∀ f : Phys, ∀ left : Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e (left, right) = 0) :
    p4Q2JM_temporalWilsonContinuous ∉
      p4Q2JS_originalPhysicalReceiverSpan H b hb.le right e := by
  intro hMember
  have hKer :=
    p4Q2JS_originalPhysicalReceiverSpan_le_actualPosteriorKernel
      H b hb.le right e hzero hMember
  have hGapZero :
      p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb.le right e p4Q2JM_temporalWilsonContinuous = 0 := by
    simpa only [p4Q2JS_originalPosteriorTestLinearMap_eq_JP] using hKer
  have hStrict :=
    (p4Q2JP_originalWilsonTemporalTestGap_strictNegative_uniform
      H b hb hwindow right e).2
  exact (ne_of_lt hStrict) hGapZero

/-- Explicit ACTUAL-PHYSICAL-SOURCE witness theorem. A representation
of the physical SU(2) temporal Wilson contrast by original Gauss-law
receivers modulo constants would force a genuinely nonzero original
physical GI expectation. No such representation is assumed to exist. -/
theorem p4Q2JS_exists_nonzeroOriginalPhysicalGI_of_temporalWilson_mem_span
    (b : ℝ) (hb : 0 < b)
    (hwindow : b < p4Q2JP_originalWilsonTemporalDetectionRadius)
    (right : Cfg) (e : Link)
    (hRepresentable : p4Q2JM_temporalWilsonContinuous ∈
      p4Q2JS_originalPhysicalReceiverSpan H b hb.le right e) :
    ∃ f : Phys, ∃ left : Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e (left, right) ≠ 0 := by
  by_contra hn
  push Not at hn
  exact
    (p4Q2JS_temporalWilson_not_mem_physicalReceiverSpan_of_allGI_zero
      H b hb hwindow right e hn) hRepresentable

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JS_originalPosteriorTestLinearMap_eq_JP
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JS_originalPosteriorTestLinearMap_one_eq_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JS_originalPhysicalReceiverSpan_le_actualPosteriorKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JS_temporalWilson_not_mem_physicalReceiverSpan_of_allGI_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JS_exists_nonzeroOriginalPhysicalGI_of_temporalWilson_mem_span
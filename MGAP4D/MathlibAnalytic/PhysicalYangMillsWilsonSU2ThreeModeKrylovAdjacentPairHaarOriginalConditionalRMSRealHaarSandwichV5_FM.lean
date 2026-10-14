import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalPosteriorHaarSandwichV5_FL
import Mathlib.Tactic

/-!
# P4-Q2-FM: the actual FG real conditional RMS is sandwiched by genuine Haar moments

FL proves a volume-uniform measure comparison for the TRUE normalized Wilson
posterior and its Haar reference.  Here we act on the LITERAL signed physical
FG/FF source-dependent response R(e,f,z,g), with frozen beta and full joint
boundary z unchanged.

Define H2(e,f,z) := integral_Haar R(e,f,z,g)^2.
Then for each actual physical link e, pair z and gauge-invariant physical f,

  exp(-16 beta) * H2(e,f,z) <= M2_Wilson(e,f,z)
      <= exp(16 beta) * H2(e,f,z).

These are REAL Bochner integrals, not only ENNReal envelopes, and M2_Wilson
is definitionally the original FG conditional square under its true posterior.
Consequently M2_Wilson = 0 IFF H2 = 0.

The proof uses the exact tilted-measure integral identity and the FK posterior
density bound; it NEVER changes the original inner posterior to Haar. No
unproved geometric decay, per-link lower frame constant, summability or
Yang--Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2FM_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FM_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FM_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FM_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FM_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorJoint

/-- The source/link/context-resolved HAAR comparison of the literal FF
signed original-Wilson relative response. The genuine posterior response
is still FG's M2, NOT this comparison function. -/
noncomputable def p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
    (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H N hN beta hbeta f e (z,g)) ^ 2
    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)

theorem p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤ p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
      H N hN beta hbeta f e z := by
  unfold p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
  exact integral_nonneg (fun g => sq_nonneg _)

/-- Pointwise in the PHYSICAL pair-Haar context, the TRUE interacting
Wilson conditional real RMS is quantitatively equivalent to the real
Haar squared moment of its EXACT signed response, with constants
independent of spatial link count and volume. -/
theorem p4Q2FM_originalWilsonConditionalRMS_real_haar_sandwich
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Real.exp (-16 * beta) *
      p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
        H N hN beta hbeta f e z ≤
      p4Q2FG_originalWilsonRelativeResponseConditionalSquare
        H N hN beta hbeta f e z ∧
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare
        H N hN beta hbeta f e z ≤
      Real.exp (16 * beta) *
        p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
          H N hN beta hbeta f e z := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let L : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H N hN beta hbeta z.1 z.2 e
  let p : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    continuousNormalizedExp μ L
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H N hN beta hbeta f e
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g => (B (z,g)) ^ 2
  have hXcont : Continuous X := by
    dsimp [X]
    exact (B.continuous.comp (continuous_const.prodMk continuous_id)).pow 2
  have hLcont : Continuous L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H N hN beta hbeta z.1 z.2 e
  have hpcont : Continuous p :=
    continuous_continuousNormalizedExp μ L hLcont
  have hXint : Integrable X μ :=
    hXcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpXint : Integrable (fun g => p g * X g) μ :=
    (hpcont.mul hXcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp : ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      Real.exp (-16 * beta) ≤ p g ∧ p g ≤ Real.exp (16 * beta) := by
    intro g
    simpa [p, μ, L,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity]
      using
        p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
          H N hN beta hbeta z.1 z.2 e g
  have hExact :
      p4Q2FG_originalWilsonRelativeResponseConditionalSquare
        H N hN beta hbeta f e z =
      ∫ g, p g * X g ∂μ := by
    change (∫ g, X g ∂μ.tilted L) = _
    rw [integral_tilted]
    rfl
  have hLow :
      Real.exp (-16 * beta) * (∫ g, X g ∂μ) ≤
      ∫ g, p g * X g ∂μ := by
    calc
      Real.exp (-16 * beta) * (∫ g, X g ∂μ) =
        ∫ g, Real.exp (-16 * beta) * X g ∂μ := by rw [integral_const_mul]
      _ ≤ ∫ g, p g * X g ∂μ := by
        apply integral_mono (hXint.const_mul _) hpXint
        intro g
        exact mul_le_mul_of_nonneg_right (hp g).1 (sq_nonneg _)
  have hUp :
      (∫ g, p g * X g ∂μ) ≤
      Real.exp (16 * beta) * (∫ g, X g ∂μ) := by
    calc
      (∫ g, p g * X g ∂μ) ≤
          ∫ g, Real.exp (16 * beta) * X g ∂μ := by
            apply integral_mono hpXint (hXint.const_mul _)
            intro g
            exact mul_le_mul_of_nonneg_right (hp g).2 (sq_nonneg _)
      _ = Real.exp (16 * beta) * (∫ g, X g ∂μ) := by
            rw [integral_const_mul]
  constructor
  · calc
      Real.exp (-16 * beta) *
        p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
          H N hN beta hbeta f e z =
          Real.exp (-16 * beta) * (∫ g, X g ∂μ) := rfl
      _ ≤ (∫ g, p g * X g ∂μ) := hLow
      _ = p4Q2FG_originalWilsonRelativeResponseConditionalSquare
          H N hN beta hbeta f e z := hExact.symm
  · calc
      p4Q2FG_originalWilsonRelativeResponseConditionalSquare
          H N hN beta hbeta f e z =
        (∫ g, p g * X g ∂μ) := hExact
      _ ≤ Real.exp (16 * beta) * (∫ g, X g ∂μ) := hUp
      _ = Real.exp (16 * beta) *
          p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
            H N hN beta hbeta f e z := rfl

/-- The EXACT true Wilson conditional RMS vanishes precisely when the
source-dependent original signed FF response has Haar squared-moment zero.
This statement is POINTWISE IN z; no global source support is invented. -/
theorem p4Q2FM_originalWilsonConditionalRMS_zero_iff_haarSquaredMoment_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare
      H N hN beta hbeta f e z = 0 ↔
    p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
      H N hN beta hbeta f e z = 0 := by
  have hb := p4Q2FM_originalWilsonConditionalRMS_real_haar_sandwich
    H N hN beta hbeta f e z
  have hHaarNonneg := p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment_nonneg
    H N hN beta hbeta f e z
  have hRMSNonneg := p4Q2FG_originalWilsonRelativeResponseConditionalSquare_nonneg
    H N hN beta hbeta f e z
  constructor
  · intro hzero
    have hprodLe :
        Real.exp (-16 * beta) *
          p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
            H N hN beta hbeta f e z ≤ 0 := by
      simpa [hzero] using hb.1
    have hprodNonneg :
        0 ≤ Real.exp (-16 * beta) *
          p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
            H N hN beta hbeta f e z :=
      mul_nonneg (Real.exp_pos _).le hHaarNonneg
    have hprodEq := le_antisymm hprodLe hprodNonneg
    exact (mul_eq_zero.mp hprodEq).resolve_left (Real.exp_pos _).ne'
  · intro hzero
    have hRMSLe :
        p4Q2FG_originalWilsonRelativeResponseConditionalSquare
          H N hN beta hbeta f e z ≤ 0 := by
      simpa [hzero] using hb.2
    exact le_antisymm hRMSLe hRMSNonneg

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FM_originalWilsonConditionalRMS_real_haar_sandwich
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FM_originalWilsonConditionalRMS_zero_iff_haarSquaredMoment_zero

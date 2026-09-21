import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszProjectorBetaContinuity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Fixed-contour Riesz idempotence under Wilson-coupling perturbation

This file proves the genuinely local spectral statement needed after fixed-contour
beta continuity.  Once the canonical beta0 circle remains in the resolvent set
at a nearby beta, the corresponding fixed-contour Riesz integral is idempotent.

No continuity of the excited-sector gap is used.  The proof uses only:

* compactness of the spectrum, to thicken the radial resolvent gap around the
  fixed circle;
* contour deformation inside that local annulus;
* the two-parameter resolvent identity;
* Fubini for the separated inner/outer circles;
* the scalar Cauchy integral formula.

The proof is pointwise on the physical Hilbert space whenever an operator-valued
integral is evaluated, avoiding extra topological-algebra instance search on the
operator algebra itself.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology Metric
open scoped InnerProductSpace Ring Topology Interval Real

noncomputable section

set_option maxHeartbeats 7000000
set_option synthInstance.maxHeartbeats 1000000

local instance fixedContourRieszIdempotenceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedContourRieszIdempotenceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedContourRieszIdempotenceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedContourRieszIdempotenceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedContourRieszIdempotenceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedContourRieszIdempotenceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance fixedContourRieszIdempotenceRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance fixedContourRieszIdempotenceComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- Two-point resolvent identity in pointwise form, with the spectral-parameter
sign convention used by Mathlib's `spectrum.resolvent`. -/
private theorem complexContinuousLinearMap_resolvent_mul_apply_eq
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    {z w : ℂ}
    (hz : z ∈ resolventSet ℂ S)
    (hw : w ∈ resolventSet ℂ S)
    (hzw : z ≠ w)
    (x : E) :
    (resolvent S z * resolvent S w) x =
      (w - z)⁻¹ • (resolvent S z x - resolvent S w x) := by
  have hInv :
      resolvent S z - resolvent S w =
        resolvent S z *
          ((algebraMap ℂ (E →L[ℂ] E) w - S) -
            (algebraMap ℂ (E →L[ℂ] E) z - S)) *
          resolvent S w := by
    simpa only [resolvent] using
      (Ring.inverse_sub_inverse
        (show
          IsUnit (algebraMap ℂ (E →L[ℂ] E) z - S) ↔
            IsUnit (algebraMap ℂ (E →L[ℂ] E) w - S) from
          iff_of_true hz hw))
  have hshift :
      ((algebraMap ℂ (E →L[ℂ] E) w - S) -
          (algebraMap ℂ (E →L[ℂ] E) z - S)) =
        (w - z) • (1 : E →L[ℂ] E) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    module
  have hDiff :
      resolvent S z - resolvent S w =
        (w - z) • (resolvent S z * resolvent S w) := by
    calc
      resolvent S z - resolvent S w =
          resolvent S z *
            ((algebraMap ℂ (E →L[ℂ] E) w - S) -
              (algebraMap ℂ (E →L[ℂ] E) z - S)) *
            resolvent S w := hInv
      _ = resolvent S z * ((w - z) • (1 : E →L[ℂ] E)) *
            resolvent S w := by rw [hshift]
      _ = (w - z) • (resolvent S z * resolvent S w) := by
        rw [mul_smul_comm, mul_one, smul_mul_assoc]
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
  have hScaled :=
    congrArg
      (fun T : E →L[ℂ] E => (w - z)⁻¹ • T)
      hDiff
  have hOperator :
      (w - z)⁻¹ • (resolvent S z - resolvent S w) =
        resolvent S z * resolvent S w := by
    simpa [smul_smul, hwz] using hScaled
  have hApply := congrArg (fun T : E →L[ℂ] E => T x) hOperator.symm
  simpa only [
    ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply
  ] using hApply

/-- Evaluating an operator-valued circle integral agrees with integrating the
pointwise evaluation. -/
private theorem circleIntegral_apply_continuousLinearMap
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    {f : ℂ → E →L[ℂ] E}
    {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r)
    (x : E) :
    (∮ z in C(c, r), f z) x =
      ∮ z in C(c, r), f z x := by
  unfold circleIntegral
  calc
    (∫ theta in (0 : ℝ)..2 * Real.pi,
        deriv (circleMap c r) theta • f (circleMap c r theta)) x =
      ∫ theta in (0 : ℝ)..2 * Real.pi,
        (deriv (circleMap c r) theta • f (circleMap c r theta)) x := by
          exact
            ContinuousLinearMap.intervalIntegral_apply
              (𝕜 := ℂ) hf.out x
    _ =
      ∫ theta in (0 : ℝ)..2 * Real.pi,
        deriv (circleMap c r) theta • f (circleMap c r theta) x := by
          apply intervalIntegral.integral_congr
          intro theta htheta
          change
            (deriv (circleMap c r) theta • f (circleMap c r theta)) x =
              deriv (circleMap c r) theta • f (circleMap c r theta) x
          simpa only [ContinuousLinearMap.smul_apply]

/-- A fixed continuous linear map can be moved through a vector-valued circle
integral. -/
private theorem continuousLinearMap_circleIntegral_comp
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    {g : ℂ → E}
    {c : ℂ} {r : ℝ}
    (hg : CircleIntegrable g c r)
    (L : E →L[ℂ] E) :
    L (∮ z in C(c, r), g z) =
      ∮ z in C(c, r), L (g z) := by
  unfold circleIntegral
  calc
    L
        (∫ theta in (0 : ℝ)..2 * Real.pi,
          deriv (circleMap c r) theta • g (circleMap c r theta)) =
      ∫ theta in (0 : ℝ)..2 * Real.pi,
        L (deriv (circleMap c r) theta • g (circleMap c r theta)) := by
          exact
            (ContinuousLinearMap.intervalIntegral_comp_comm
              (𝕜 := ℂ) L hg.out).symm
    _ =
      ∫ theta in (0 : ℝ)..2 * Real.pi,
        deriv (circleMap c r) theta • L (g (circleMap c r theta)) := by
          apply intervalIntegral.integral_congr
          intro theta htheta
          exact L.map_smul _ _

/-- The scalar radial values attained by the spectrum form a compact subset of
the real line. -/
private theorem radialSpectrum_isCompact
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ) :
    IsCompact ((fun z : ℂ => dist z c) '' spectrum ℂ S) := by
  exact
    (spectrum.isCompact S).image
      (continuous_id.dist continuous_const)

/-- If a whole circle lies in the resolvent set, then its radius is separated
from the compact set of spectral radii. -/
private theorem radius_not_mem_radialSpectrum
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ) {r : ℝ}
    (hres : Metric.sphere c r ⊆ resolventSet ℂ S) :
    r ∉ ((fun z : ℂ => dist z c) '' spectrum ℂ S) := by
  intro hrmem
  rcases hrmem with ⟨z, hzSpec, hzRad⟩
  have hzSphere : z ∈ Metric.sphere c r := by
    rw [Metric.mem_sphere]
    exact hzRad
  have hzRes := hres hzSphere
  exact hzSpec hzRes

/-- A compact radial spectral gap produces a positive epsilon on both sides of
the fixed contour radius. -/
private theorem exists_radial_resolvent_margin
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ) {r : ℝ}
    (hres : Metric.sphere c r ⊆ resolventSet ℂ S) :
    ∃ eps : ℝ, 0 < eps ∧
      Metric.ball r eps ∩
        ((fun z : ℂ => dist z c) '' spectrum ℂ S) = ∅ := by
  let K : Set ℝ := (fun z : ℂ => dist z c) '' spectrum ℂ S
  have hKcompact : IsCompact K := radialSpectrum_isCompact S c
  have hrnot : r ∉ K := radius_not_mem_radialSpectrum S c hres
  have hopen : IsOpen Kᶜ := hKcompact.isClosed.isOpen_compl
  have hrcompl : r ∈ Kᶜ := by simpa using hrnot
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopen r hrcompl
  refine ⟨eps, heps, ?_⟩
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  exact (hball hx.1) hx.2

/-- Any point whose radial distance lies in the protected epsilon-window belongs
to the resolvent set. -/
private theorem mem_resolventSet_of_radial_mem_ball
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ) {r eps : ℝ}
    (hgap :
      Metric.ball r eps ∩
        ((fun z : ℂ => dist z c) '' spectrum ℂ S) = ∅)
    {z : ℂ}
    (hz : dist z c ∈ Metric.ball r eps) :
    z ∈ resolventSet ℂ S := by
  by_contra hzRes
  have hzSpec : z ∈ spectrum ℂ S := by
    simpa [spectrum, Set.mem_compl_iff] using hzRes
  have hradSpec :
      dist z c ∈ (fun w : ℂ => dist w c) '' spectrum ℂ S :=
    ⟨z, hzSpec, rfl⟩
  have hinter :
      dist z c ∈
        Metric.ball r eps ∩
          ((fun w : ℂ => dist w c) '' spectrum ℂ S) :=
    ⟨hz, hradSpec⟩
  simpa [hgap] using hinter

/-- Resolvent differentiability at every point of a radial annulus protected
by the radial spectral margin.  The pointwise `DifferentiableAt` conclusion is
the form required by Mathlib's annulus contour-deformation theorem. -/
private theorem resolvent_differentiableAt_of_mem_radial_annulus
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ)
    {r eps rin rout : ℝ}
    (hgap :
      Metric.ball r eps ∩
        ((fun z : ℂ => dist z c) '' spectrum ℂ S) = ∅)
    (hinner : r - eps < rin)
    (houter : rout < r + eps)
    {z : ℂ}
    (hz : z ∈ Metric.ball c rout \ Metric.closedBall c rin) :
    DifferentiableAt ℂ (resolvent S) z := by
  have hzBounds : rin < dist z c ∧ dist z c < rout := by
    constructor
    · have hzNotClosed := hz.2
      rw [Metric.mem_closedBall] at hzNotClosed
      exact lt_of_not_ge hzNotClosed
    · simpa [Metric.mem_ball] using hz.1
  have hzRad : dist z c ∈ Metric.ball r eps := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hzRes : z ∈ resolventSet ℂ S :=
    mem_resolventSet_of_radial_mem_ball S c hgap hzRad
  exact (spectrum.hasDerivAt_resolvent_const_left hzRes).differentiableAt

/-- Resolvent continuity on the corresponding closed annulus. -/
private theorem resolvent_continuousOn_closed_radial_annulus
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ)
    {r eps rin rout : ℝ}
    (hgap :
      Metric.ball r eps ∩
        ((fun z : ℂ => dist z c) '' spectrum ℂ S) = ∅)
    (hinner : r - eps < rin)
    (houter : rout < r + eps) :
    ContinuousOn (resolvent S)
      (Metric.closedBall c rout \ Metric.ball c rin) := by
  intro z hz
  have hzBounds : rin ≤ dist z c ∧ dist z c ≤ rout := by
    constructor
    · have hzNotBall := hz.2
      rw [Metric.mem_ball] at hzNotBall
      exact le_of_not_gt hzNotBall
    · simpa [Metric.mem_closedBall] using hz.1
  have hzRad : dist z c ∈ Metric.ball r eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith
  have hzRes : z ∈ resolventSet ℂ S :=
    mem_resolventSet_of_radial_mem_ball S c hgap hzRad
  exact
    (spectrum.hasDerivAt_resolvent_const_left hzRes).continuousAt.continuousWithinAt

/-- Within a protected radial spectral window, the resolvent circle integral is
independent of the chosen positive radius. -/
private theorem circleIntegral_resolvent_eq_of_radii_in_radial_gap
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ)
    {r eps rsmall rlarge : ℝ}
    (hgap :
      Metric.ball r eps ∩
        ((fun z : ℂ => dist z c) '' spectrum ℂ S) = ∅)
    (hsmall : 0 < rsmall)
    (hsmallWin : r - eps < rsmall)
    (hle : rsmall ≤ rlarge)
    (hlargeWin : rlarge < r + eps) :
    (∮ z in C(c, rlarge), resolvent S z) =
      ∮ z in C(c, rsmall), resolvent S z := by
  apply
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hsmall hle (s := (∅ : Set ℂ))
  · exact Set.countable_empty
  · exact
      resolvent_continuousOn_closed_radial_annulus
        S c hgap hsmallWin hlargeWin
  · intro z hz
    exact
      resolvent_differentiableAt_of_mem_radial_annulus
        S c hgap hsmallWin hlargeWin hz.1


/-- Pinned-mathlib backport of the two-interval Fubini wrapper.  The project is
pinned before `MeasureTheory.intervalIntegral_intervalIntegral_swap` was added,
so we derive exactly that statement from the already available one-interval
Fubini theorem instead of depending on a newer API name. -/
private theorem intervalIntegral_intervalIntegral_swap_pinned
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {F : ℝ → ℝ → E}
    {a b c d : ℝ}
    (h : MeasureTheory.IntegrableOn F.uncurry
      (Set.uIoc a b ×ˢ Set.uIoc c d)) :
    (∫ x in a..b, ∫ y in c..d, F x y) =
      ∫ y in c..d, ∫ x in a..b, F x y := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
    ← MeasureTheory.intervalIntegral_integral_swap,
    ← intervalIntegral.integral_smul]
  · simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  · rwa [← MeasureTheory.integrable_swap_iff, Measure.prod_restrict,
      ← Measure.volume_eq_prod, ← MeasureTheory.IntegrableOn]

/-- Fubini for two circle integrals, reduced explicitly to Mathlib's Fubini
theorem for interval integrals.  The hypothesis is stated on the actual
parameter-space integrand so no hidden circle-integrability inference is
required. -/
private theorem circleIntegral_circleIntegral_swap_of_integrable_parameter
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (f : ℂ → ℂ → E)
    (c : ℂ)
    (r₁ r₂ : ℝ)
    (hInt :
      MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ =>
          (deriv (circleMap c r₁) p.1 *
              deriv (circleMap c r₂) p.2) •
            f (circleMap c r₁ p.1) (circleMap c r₂ p.2))
        (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.uIoc 0 (2 * Real.pi))) :
    (∮ z in C(c, r₁), ∮ w in C(c, r₂), f z w) =
      ∮ w in C(c, r₂), ∮ z in C(c, r₁), f z w := by
  unfold circleIntegral
  simp_rw [← intervalIntegral.integral_smul, smul_smul]
  simpa only [mul_comm] using
    (intervalIntegral_intervalIntegral_swap_pinned
      (F := fun theta phi =>
        (deriv (circleMap c r₁) theta *
            deriv (circleMap c r₂) phi) •
          f (circleMap c r₁ theta) (circleMap c r₂ phi))
      hInt)

end

end MathlibAnalytic
end MGAP4D

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
  · rwa [← MeasureTheory.integrable_swap_iff,
      MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod,
      ← MeasureTheory.IntegrableOn]

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


/-- If the pole lies outside the closed disk, the scalar Cauchy kernel has zero
circle integral. -/
private theorem circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
    {c z : ℂ}
    {r : ℝ}
    (hr : 0 ≤ r)
    (hz : z ∉ Metric.closedBall c r) :
    (∮ w in C(c, r), (w - z)⁻¹) = 0 := by
  apply
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hr (s := (∅ : Set ℂ)) Set.countable_empty
  · exact
      (continuousOn_id.sub continuousOn_const).inv₀
        (fun w hw =>
          sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz))
  · intro w hw
    have hwne : w ≠ z :=
      ne_of_mem_of_not_mem (Metric.ball_subset_closedBall hw.1) hz
    exact
      (((hasDerivAt_id w).sub_const z).inv (sub_ne_zero.mpr hwne)).differentiableAt

/-- Vector-valued version of the exterior-pole Cauchy kernel integral. -/
private theorem circleIntegral_sub_inv_smul_eq_zero_of_not_mem_closedBall
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    {c z : ℂ}
    {r : ℝ}
    (hr : 0 ≤ r)
    (hz : z ∉ Metric.closedBall c r)
    (x : E) :
    (∮ w in C(c, r), (w - z)⁻¹ • x) = 0 := by
  rw [circleIntegral.integral_smul_const]
  rw [circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall hr hz]
  exact zero_smul ℂ x

/-- With the pole inside the disk, the reversed kernel `(w-z)⁻¹` contributes
the expected minus sign. -/
private theorem circleIntegral_inv_sub_smul_const_of_mem_ball
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    {c w : ℂ}
    {r : ℝ}
    (hw : w ∈ Metric.ball c r)
    (x : E) :
    (∮ z in C(c, r), (w - z)⁻¹ • x) =
      -(2 * Real.pi * Complex.I : ℂ) • x := by
  calc
    (∮ z in C(c, r), (w - z)⁻¹ • x) =
        ∮ z in C(c, r), (-1 : ℂ) • ((z - w)⁻¹ • x) := by
          apply circleIntegral.integral_congr (le_of_lt (dist_nonneg.trans_lt hw))
          intro z hz
          change
            (w - z)⁻¹ • x =
              (-1 : ℂ) • ((z - w)⁻¹ • x)
          have hsub : w - z = -(z - w) := by ring
          rw [hsub, inv_neg, neg_smul, neg_one_smul]
    _ = (-1 : ℂ) • (∮ z in C(c, r), (z - w)⁻¹ • x) := by
          rw [circleIntegral.integral_smul]
    _ = (-1 : ℂ) • ((∮ z in C(c, r), (z - w)⁻¹) • x) := by
          rw [circleIntegral.integral_smul_const]
    _ = -(2 * Real.pi * Complex.I : ℂ) • x := by
          rw [circleIntegral.integral_sub_inv_of_mem_ball hw]
          rw [smul_smul]
          congr 1
          ring


/-- The parameter-space integrand needed to Fubini-swap the separated-circle
resolvent Cauchy kernel is integrable.  Separation of the two radii removes the
only possible scalar-kernel singularity. -/
private theorem separatedCircle_resolventKernel_parameter_integrable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ)
    {rin rout : ℝ}
    (hrin : 0 ≤ rin)
    (hrout : 0 ≤ rout)
    (hlt : rin < rout)
    (hcontIn :
      ContinuousOn (fun w : ℂ => resolvent S w) (Metric.sphere c rin))
    (x : E) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ =>
        (deriv (circleMap c rout) p.1 *
            deriv (circleMap c rin) p.2) •
          ((circleMap c rin p.2 - circleMap c rout p.1)⁻¹ •
            resolvent S (circleMap c rin p.2) x))
      (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.uIoc 0 (2 * Real.pi)) := by
  have houterCircle :
      Continuous (fun p : ℝ × ℝ => circleMap c rout p.1) :=
    (continuous_circleMap c rout).comp continuous_fst
  have hinnerCircle :
      Continuous (fun p : ℝ × ℝ => circleMap c rin p.2) :=
    (continuous_circleMap c rin).comp continuous_snd
  have hsep :
      ∀ p : ℝ × ℝ,
        circleMap c rin p.2 - circleMap c rout p.1 ≠ 0 := by
    intro p
    apply sub_ne_zero.mpr
    intro heq
    have hin :
        dist (circleMap c rin p.2) c = rin :=
      Metric.mem_sphere.mp (circleMap_mem_sphere c hrin p.2)
    have hout :
        dist (circleMap c rout p.1) c = rout :=
      Metric.mem_sphere.mp (circleMap_mem_sphere c hrout p.1)
    rw [heq] at hin
    linarith
  have hkernel :
      Continuous
        (fun p : ℝ × ℝ =>
          (circleMap c rin p.2 - circleMap c rout p.1)⁻¹) :=
    Continuous.inv₀ (hinnerCircle.sub houterCircle) hsep
  have hresCurve :
      Continuous (fun theta : ℝ => resolvent S (circleMap c rin theta)) := by
    apply ContinuousOn.comp_continuous hcontIn (continuous_circleMap c rin)
    exact fun theta => circleMap_mem_sphere c hrin theta
  have hvecCurve :
      Continuous (fun theta : ℝ => resolvent S (circleMap c rin theta) x) :=
    (ContinuousLinearMap.apply ℂ E x).continuous.comp hresCurve
  have hvec :
      Continuous
        (fun p : ℝ × ℝ => resolvent S (circleMap c rin p.2) x) :=
    hvecCurve.comp continuous_snd
  have hkernelVec :
      Continuous
        (fun p : ℝ × ℝ =>
          (circleMap c rin p.2 - circleMap c rout p.1)⁻¹ •
            resolvent S (circleMap c rin p.2) x) :=
    hkernel.smul hvec
  have hdout :
      Continuous (fun theta : ℝ => deriv (circleMap c rout) theta) := by
    have hderivEq :
        (fun theta : ℝ => deriv (circleMap c rout) theta) =
          fun theta : ℝ => circleMap 0 rout theta * Complex.I := by
      funext theta
      exact deriv_circleMap c rout theta
    rw [hderivEq]
    exact (continuous_circleMap 0 rout).mul_const Complex.I
  have hdin :
      Continuous (fun theta : ℝ => deriv (circleMap c rin) theta) := by
    have hderivEq :
        (fun theta : ℝ => deriv (circleMap c rin) theta) =
          fun theta : ℝ => circleMap 0 rin theta * Complex.I := by
      funext theta
      exact deriv_circleMap c rin theta
    rw [hderivEq]
    exact (continuous_circleMap 0 rin).mul_const Complex.I
  have hderiv :
      Continuous
        (fun p : ℝ × ℝ =>
          deriv (circleMap c rout) p.1 *
            deriv (circleMap c rin) p.2) :=
    (hdout.comp continuous_fst).mul (hdin.comp continuous_snd)
  have hparam :
      Continuous
        (fun p : ℝ × ℝ =>
          (deriv (circleMap c rout) p.1 *
              deriv (circleMap c rin) p.2) •
            ((circleMap c rin p.2 - circleMap c rout p.1)⁻¹ •
              resolvent S (circleMap c rin p.2) x)) :=
    hderiv.smul hkernelVec
  have hcompact :
      IsCompact
        (Set.uIcc 0 (2 * Real.pi) ×ˢ Set.uIcc 0 (2 * Real.pi)) :=
    isCompact_uIcc.prod isCompact_uIcc
  exact
    (hparam.continuousOn.integrableOn_compact hcompact).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)


/-- On two strictly separated resolvent circles, the iterated resolvent product
integral collapses to one factor of the inner resolvent integral.  This is the
algebraic core of Riesz-projector idempotence. -/
private theorem separatedCircle_doubleResolvent_apply_eq
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (c : ℂ)
    {rin rout : ℝ}
    (hrin : 0 ≤ rin)
    (hrout : 0 ≤ rout)
    (hlt : rin < rout)
    (hresIn : Metric.sphere c rin ⊆ resolventSet ℂ S)
    (hresOut : Metric.sphere c rout ⊆ resolventSet ℂ S)
    (hcontIn :
      ContinuousOn (fun w : ℂ => resolvent S w) (Metric.sphere c rin))
    (x : E) :
    (∮ z in C(c, rout),
        ∮ w in C(c, rin),
          resolvent S z (resolvent S w x)) =
      (2 * Real.pi * Complex.I : ℂ) •
        (∮ w in C(c, rin), resolvent S w x) := by
  have hvecIn :
      CircleIntegrable
        (fun w : ℂ => resolvent S w x)
        c rin := by
    have hxCont :
        ContinuousOn
          (fun w : ℂ => resolvent S w x)
          (Metric.sphere c rin) := by
      simpa [Function.comp_def] using
        (ContinuousLinearMap.apply ℂ E x).continuous.comp_continuousOn hcontIn
    exact hxCont.circleIntegrable hrin
  have hsep :
      ∀ z ∈ Metric.sphere c rout,
        ∀ w ∈ Metric.sphere c rin,
          z ≠ w := by
    intro z hz w hw hzw
    subst w
    have hzOut : dist z c = rout := Metric.mem_sphere.mp hz
    have hzIn : dist z c = rin := Metric.mem_sphere.mp hw
    linarith
  have hinner :
      ∀ z ∈ Metric.sphere c rout,
        (∮ w in C(c, rin),
            resolvent S z (resolvent S w x)) =
          -(∮ w in C(c, rin),
              (w - z)⁻¹ • resolvent S w x) := by
    intro z hz
    have hzOutside : z ∉ Metric.closedBall c rin := by
      intro hzClosed
      have hzOut : dist z c = rout := Metric.mem_sphere.mp hz
      have hzLe : dist z c ≤ rin := Metric.mem_closedBall.mp hzClosed
      linarith
    have hzNotSphere : z ∉ Metric.sphere c |rin| := by
      rw [abs_of_nonneg hrin]
      intro hzIn
      exact hzOutside (Metric.sphere_subset_closedBall hzIn)
    have hconst :
        CircleIntegrable
          (fun _ : ℂ => resolvent S z x)
          c rin :=
      continuousOn_const.circleIntegrable hrin
    have hA :
        CircleIntegrable
          (fun w : ℂ => (w - z)⁻¹ • resolvent S z x)
          c rin := by
      simpa only [zpow_neg_one] using
        hconst.sub_zpow_smul (-1 : ℤ) hzNotSphere
    have hB :
        CircleIntegrable
          (fun w : ℂ => (w - z)⁻¹ • resolvent S w x)
          c rin := by
      simpa only [zpow_neg_one] using
        hvecIn.sub_zpow_smul (-1 : ℤ) hzNotSphere
    calc
      (∮ w in C(c, rin),
          resolvent S z (resolvent S w x)) =
        ∮ w in C(c, rin),
          ((w - z)⁻¹ • resolvent S z x) -
            ((w - z)⁻¹ • resolvent S w x) := by
              apply circleIntegral.integral_congr hrin
              intro w hw
              have hres :=
                complexContinuousLinearMap_resolvent_mul_apply_eq
                  S (hresOut hz) (hresIn hw) (hsep z hz w hw) x
              simpa only [smul_sub] using hres
      _ =
        (∮ w in C(c, rin), (w - z)⁻¹ • resolvent S z x) -
          (∮ w in C(c, rin), (w - z)⁻¹ • resolvent S w x) := by
              exact circleIntegral.integral_sub hA hB
      _ = 0 -
          (∮ w in C(c, rin), (w - z)⁻¹ • resolvent S w x) := by
              rw [
                circleIntegral_sub_inv_smul_eq_zero_of_not_mem_closedBall
                  hrin hzOutside (resolvent S z x)
              ]
      _ = -(∮ w in C(c, rin), (w - z)⁻¹ • resolvent S w x) := by
              rw [zero_sub]
  have hFubini :
      (∮ z in C(c, rout),
          ∮ w in C(c, rin),
            (w - z)⁻¹ • resolvent S w x) =
        ∮ w in C(c, rin),
          ∮ z in C(c, rout),
            (w - z)⁻¹ • resolvent S w x := by
    exact
      circleIntegral_circleIntegral_swap_of_integrable_parameter
        (fun z w : ℂ => (w - z)⁻¹ • resolvent S w x)
        c rout rin
        (separatedCircle_resolventKernel_parameter_integrable
          S c hrin hrout hlt hcontIn x)
  have houterKernel :
      ∀ w ∈ Metric.sphere c rin,
        (∮ z in C(c, rout),
            (w - z)⁻¹ • resolvent S w x) =
          -(2 * Real.pi * Complex.I : ℂ) • resolvent S w x := by
    intro w hw
    have hwBall : w ∈ Metric.ball c rout := by
      rw [Metric.mem_ball]
      rw [Metric.mem_sphere] at hw
      rw [hw]
      exact hlt
    exact
      circleIntegral_inv_sub_smul_const_of_mem_ball
        hwBall (resolvent S w x)
  calc
    (∮ z in C(c, rout),
        ∮ w in C(c, rin),
          resolvent S z (resolvent S w x)) =
      ∮ z in C(c, rout),
        (-1 : ℂ) •
          (∮ w in C(c, rin),
            (w - z)⁻¹ • resolvent S w x) := by
              apply circleIntegral.integral_congr hrout
              intro z hz
              rw [hinner z hz]
              exact (neg_one_smul ℂ _).symm
    _ = (-1 : ℂ) •
        (∮ z in C(c, rout),
          ∮ w in C(c, rin),
            (w - z)⁻¹ • resolvent S w x) := by
              rw [circleIntegral.integral_smul]
    _ = (-1 : ℂ) •
        (∮ w in C(c, rin),
          ∮ z in C(c, rout),
            (w - z)⁻¹ • resolvent S w x) := by
              rw [hFubini]
    _ = (-1 : ℂ) •
        (∮ w in C(c, rin),
          (-(2 * Real.pi * Complex.I : ℂ)) • resolvent S w x) := by
              congr 1
              apply circleIntegral.integral_congr hrin
              intro w hw
              exact houterKernel w hw
    _ = (-1 : ℂ) •
        ((-(2 * Real.pi * Complex.I : ℂ)) •
          (∮ w in C(c, rin), resolvent S w x)) := by
              rw [circleIntegral.integral_smul]
    _ = (2 * Real.pi * Complex.I : ℂ) •
        (∮ w in C(c, rin), resolvent S w x) := by
              rw [smul_smul]
              congr 1
              ring

end

end MathlibAnalytic
end MGAP4D

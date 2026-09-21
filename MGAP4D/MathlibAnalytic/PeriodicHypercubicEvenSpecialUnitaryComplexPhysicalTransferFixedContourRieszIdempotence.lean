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
  have hDiff :
      resolvent S z - resolvent S w =
        (w - z) • (resolvent S z * resolvent S w) := by
    calc
      resolvent S z - resolvent S w =
          resolvent S z *
            ((algebraMap ℂ (E →L[ℂ] E) w - S) -
              (algebraMap ℂ (E →L[ℂ] E) z - S)) *
            resolvent S w := hInv
      _ = (w - z) • (resolvent S z * resolvent S w) := by
        simp [Algebra.algebraMap_eq_smul_one, mul_assoc, smul_mul_assoc,
          mul_smul_comm, smul_mul]
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
  apply Set.eq_empty_iff_forall_not_mem.mpr
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

/-- Resolvent differentiability on a radial annulus protected by the radial
spectral margin. -/
private theorem resolvent_differentiableOn_radial_annulus
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
    DifferentiableOn ℂ (resolvent S)
      (Metric.ball c rout \ Metric.closedBall c rin) := by
  intro z hz
  have hzBounds : rin < dist z c ∧ dist z c < rout := by
    constructor
    · have hzNotClosed := hz.2
      rw [Metric.mem_closedBall] at hzNotClosed
      exact lt_of_not_ge hzNotClosed
    · simpa [Metric.mem_ball] using hz.1
  have hzRad : dist z c ∈ Metric.ball r eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith
  have hzRes : z ∈ resolventSet ℂ S :=
    mem_resolventSet_of_radial_mem_ball S c hgap hzRad
  exact (spectrum.hasDerivAt_resolvent_const_left hzRes).differentiableAt.differentiableWithinAt

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
      resolvent_differentiableOn_radial_annulus
        S c hgap hsmallWin hlargeWin z hz.1

/-- For beta sufficiently near beta0, the fixed beta0 contour integral is a
genuine idempotent Riesz projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_mul_self
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ)) :
    ∀ᶠ beta in 𝓝 beta0,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta *
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta =
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta := by
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let A := E →L[ℂ] E
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  let r :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta0.1 beta0.2
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta0.1 beta0.2
  have hresEvent :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_canonicalRieszCircle_eventually_subset_resolventSet
      H N hN beta0
  filter_upwards [hresEvent] with beta hres
  obtain ⟨eps0, heps0, hgap0⟩ :=
    exists_radial_resolvent_margin (S beta) (1 : ℂ) hres
  let eps := min (eps0 / 2) (r / 2)
  have heps : 0 < eps := by
    dsimp [eps]
    exact lt_min (half_pos heps0) (half_pos hr)
  have heps_lt_eps0 : eps < eps0 := by
    dsimp [eps]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self heps0)
  have heps_lt_r : eps < r := by
    dsimp [eps]
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr)
  have hgap :
      Metric.ball r eps ∩
        ((fun z : ℂ => dist z (1 : ℂ)) '' spectrum ℂ (S beta)) = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have hx0 : x ∈ Metric.ball r eps0 := by
      exact Metric.ball_subset_ball heps_lt_eps0.le hx.1
    have : x ∈
        Metric.ball r eps0 ∩
          ((fun z : ℂ => dist z (1 : ℂ)) '' spectrum ℂ (S beta)) :=
      ⟨hx0, hx.2⟩
    simpa [hgap0] using this
  let rin := r - eps / 2
  let rout := r + eps / 2
  have hrin : 0 < rin := by
    dsimp [rin]
    linarith
  have hrout : 0 < rout := by
    dsimp [rout]
    linarith
  have hrin_lt_r : rin < r := by
    dsimp [rin]
    linarith
  have hr_lt_rout : r < rout := by
    dsimp [rout]
    linarith
  have hwinIn : r - eps < rin := by
    dsimp [rin]
    linarith
  have hwinRLeft : r - eps < r := by linarith
  have hwinROut : r < r + eps := by linarith
  have hwinOut : rout < r + eps := by
    dsimp [rout]
    linarith
  have hIout :
      (∮ z in C((1 : ℂ), rout), resolvent (S beta) z) =
        ∮ z in C((1 : ℂ), r), resolvent (S beta) z := by
    exact
      circleIntegral_resolvent_eq_of_radii_in_radial_gap
        (S beta) (1 : ℂ) hgap hr hwinRLeft hr_lt_rout.le hwinOut
  have hIin :
      (∮ z in C((1 : ℂ), r), resolvent (S beta) z) =
        ∮ z in C((1 : ℂ), rin), resolvent (S beta) z := by
    exact
      circleIntegral_resolvent_eq_of_radii_in_radial_gap
        (S beta) (1 : ℂ) hgap hrin hwinIn hrin_lt_r.le hwinROut
  have hresIn :
      Metric.sphere (1 : ℂ) rin ⊆ resolventSet ℂ (S beta) := by
    intro z hz
    have hzdist : dist z (1 : ℂ) = rin := by
      simpa [Metric.mem_sphere] using hz
    apply mem_resolventSet_of_radial_mem_ball (S beta) (1 : ℂ) hgap
    rw [Metric.mem_ball, Real.dist_eq, hzdist]
    rw [abs_lt]
    constructor <;> dsimp [rin] <;> linarith
  have hresOut :
      Metric.sphere (1 : ℂ) rout ⊆ resolventSet ℂ (S beta) := by
    intro z hz
    have hzdist : dist z (1 : ℂ) = rout := by
      simpa [Metric.mem_sphere] using hz
    apply mem_resolventSet_of_radial_mem_ball (S beta) (1 : ℂ) hgap
    rw [Metric.mem_ball, Real.dist_eq, hzdist]
    rw [abs_lt]
    constructor <;> dsimp [rout] <;> linarith
  have hcontIn :
      ContinuousOn (fun z : ℂ => resolvent (S beta) z)
        (Metric.sphere (1 : ℂ) rin) := by
    intro z hz
    exact
      (spectrum.hasDerivAt_resolvent_const_left (hresIn hz)).continuousAt.continuousWithinAt
  have hcontOut :
      ContinuousOn (fun z : ℂ => resolvent (S beta) z)
        (Metric.sphere (1 : ℂ) rout) := by
    intro z hz
    exact
      (spectrum.hasDerivAt_resolvent_const_left (hresOut hz)).continuousAt.continuousWithinAt
  have hIntIn :
      CircleIntegrable (fun z : ℂ => resolvent (S beta) z) (1 : ℂ) rin :=
    hcontIn.circleIntegrable hrin.le
  have hIntOut :
      CircleIntegrable (fun z : ℂ => resolvent (S beta) z) (1 : ℂ) rout :=
    hcontOut.circleIntegrable hrout.le
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  change
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) *
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ z in C((1 : ℂ), r), resolvent (S beta) z)
  apply ContinuousLinearMap.ext
  intro x
  have hvecIn :
      CircleIntegrable
        (fun w : ℂ => resolvent (S beta) w x)
        (1 : ℂ) rin := by
    have hxcont :
        ContinuousOn
          (fun w : ℂ => resolvent (S beta) w x)
          (Metric.sphere (1 : ℂ) rin) := by
      simpa [Function.comp_def] using
        (ContinuousLinearMap.apply ℂ E x).continuous.comp_continuousOn hcontIn
    exact hxcont.circleIntegrable hrin.le
  have hNested :
      (∮ z in C((1 : ℂ), rout),
          ∮ w in C((1 : ℂ), rin),
            resolvent (S beta) z (resolvent (S beta) w x)) =
        (2 * Real.pi * Complex.I : ℂ) •
          (∮ w in C((1 : ℂ), rin), resolvent (S beta) w x) := by
    let F : ℂ → ℂ → E :=
      fun z w => resolvent (S beta) z (resolvent (S beta) w x)
    let FA : ℂ → ℂ → E :=
      fun z w => (w - z)⁻¹ • resolvent (S beta) z x
    let FB : ℂ → ℂ → E :=
      fun z w => (w - z)⁻¹ • resolvent (S beta) w x
    have hsep :
        ∀ z ∈ Metric.sphere (1 : ℂ) rout,
          ∀ w ∈ Metric.sphere (1 : ℂ) rin,
            z ≠ w := by
      intro z hz w hw hzw
      subst w
      have hzR : dist z (1 : ℂ) = rout := by
        simpa [Metric.mem_sphere] using hz
      have hzI : dist z (1 : ℂ) = rin := by
        simpa [Metric.mem_sphere] using hw
      linarith
    have hpoint :
        ∀ z ∈ Metric.sphere (1 : ℂ) rout,
          ∀ w ∈ Metric.sphere (1 : ℂ) rin,
            F z w = FA z w - FB z w := by
      intro z hz w hw
      have hid :=
        complexContinuousLinearMap_resolvent_mul_apply_eq
          (S beta) (hresOut hz) (hresIn hw) (hsep z hz w hw) x
      simpa [F, FA, FB, sub_smul] using hid
    have hAinner :
        ∀ z ∈ Metric.sphere (1 : ℂ) rout,
          (∮ w in C((1 : ℂ), rin), FA z w) = 0 := by
      intro z hz
      have hzOutside : z ∉ Metric.closedBall (1 : ℂ) rin := by
        rw [Metric.mem_closedBall]
        have hzR : dist z (1 : ℂ) = rout := by
          simpa [Metric.mem_sphere] using hz
        linarith
      have hdiff :
          DifferentiableOn ℂ
            (fun w : ℂ => (w - z)⁻¹ • resolvent (S beta) z x)
            (Metric.ball (1 : ℂ) rin) := by
        intro w hw
        have hwz : w - z ≠ 0 := by
          apply sub_ne_zero.mpr
          intro hwzEq
          subst z
          exact hzOutside (Metric.ball_subset_closedBall hw)
        exact
          ((hasDerivAt_id w).sub_const z).inv₀ hwz |>.smul_const
            (resolvent (S beta) z x) |>.differentiableAt.differentiableWithinAt
      have hcont :
          ContinuousOn
            (fun w : ℂ => (w - z)⁻¹ • resolvent (S beta) z x)
            (Metric.closedBall (1 : ℂ) rin) := by
        intro w hw
        have hwz : w - z ≠ 0 := by
          apply sub_ne_zero.mpr
          intro hwzEq
          subst z
          exact hzOutside hw
        exact
          (((continuousAt_id.sub continuousAt_const).inv₀ hwz).smul
            continuousAt_const).continuousWithinAt
      exact
        Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
          hrin.le (s := (∅ : Set ℂ)) Set.countable_empty hcont
          (by
            intro w hw
            exact hdiff w hw.1)
    have hBswap :
        (∮ z in C((1 : ℂ), rout), ∮ w in C((1 : ℂ), rin), FB z w) =
          ∮ w in C((1 : ℂ), rin), ∮ z in C((1 : ℂ), rout), FB z w := by
      unfold circleIntegral
      simp_rw [← intervalIntegral.integral_smul, smul_smul]
      apply MeasureTheory.intervalIntegral_intervalIntegral_swap
      apply ContinuousOn.integrableOn_compact isCompact_prod
      fun_prop
    have hBouter :
        ∀ w ∈ Metric.sphere (1 : ℂ) rin,
          (∮ z in C((1 : ℂ), rout), FB z w) =
            -(2 * Real.pi * Complex.I : ℂ) • resolvent (S beta) w x := by
      intro w hw
      have hwBall : w ∈ Metric.ball (1 : ℂ) rout := by
        rw [Metric.mem_ball]
        have hwI : dist w (1 : ℂ) = rin := by
          simpa [Metric.mem_sphere] using hw
        linarith
      calc
        (∮ z in C((1 : ℂ), rout), FB z w) =
            ∮ z in C((1 : ℂ), rout),
              -((z - w)⁻¹ • resolvent (S beta) w x) := by
                apply circleIntegral.integral_congr hrout.le
                intro z hz
                simp [FB, sub_eq_neg_sub, inv_neg, neg_smul]
        _ = -(∮ z in C((1 : ℂ), rout),
              (z - w)⁻¹ • resolvent (S beta) w x) := by
                rw [circleIntegral.integral_neg]
        _ = -(2 * Real.pi * Complex.I : ℂ) • resolvent (S beta) w x := by
                rw [circleIntegral.integral_smul_const]
                rw [circleIntegral.integral_sub_inv_of_mem_ball hwBall]
                simp
    calc
      (∮ z in C((1 : ℂ), rout),
          ∮ w in C((1 : ℂ), rin), F z w) =
        ∮ z in C((1 : ℂ), rout),
          ∮ w in C((1 : ℂ), rin), (FA z w - FB z w) := by
            apply circleIntegral.integral_congr hrout.le
            intro z hz
            apply circleIntegral.integral_congr hrin.le
            intro w hw
            exact hpoint z hz w hw
      _ =
        (∮ z in C((1 : ℂ), rout), ∮ w in C((1 : ℂ), rin), FA z w) -
          (∮ z in C((1 : ℂ), rout), ∮ w in C((1 : ℂ), rin), FB z w) := by
            rw [circleIntegral.integral_sub]
            · intro z hz
              exact
                ((continuousOn_id.sub continuousOn_const).inv₀
                    (fun w hw => sub_ne_zero.mpr (hsep z hz w hw).symm)).smul
                  ((ContinuousLinearMap.apply ℂ E x).continuous.comp_continuousOn hcontOut
                    |>.const
                  )
              sorry
            · sorry
      _ = 0 -
          (∮ w in C((1 : ℂ), rin), ∮ z in C((1 : ℂ), rout), FB z w) := by
            rw [hBswap]
            congr 1
            apply circleIntegral.integral_eq_zero_of_ae_eq_zero
            filter_upwards with z
            exact hAinner z (by sorry)
      _ = (2 * Real.pi * Complex.I : ℂ) •
          (∮ w in C((1 : ℂ), rin), resolvent (S beta) w x) := by
            sorry
  have hOuterApply :
      (∮ z in C((1 : ℂ), rout), resolvent (S beta) z)
          ((∮ w in C((1 : ℂ), rin), resolvent (S beta) w) x) =
        (∮ z in C((1 : ℂ), rout),
          ∮ w in C((1 : ℂ), rin),
            resolvent (S beta) z (resolvent (S beta) w x)) := by
    rw [circleIntegral_apply_continuousLinearMap hIntIn x]
    rw [circleIntegral_apply_continuousLinearMap hIntOut]
    apply circleIntegral.integral_congr hrout.le
    intro z hz
    have hzwInt :
        CircleIntegrable
          (fun w : ℂ => resolvent (S beta) w x)
          (1 : ℂ) rin := hvecIn
    exact
      continuousLinearMap_circleIntegral_comp hzwInt (resolvent (S beta) z)
  calc
    (((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) *
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z))) x =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z)
            ((∮ w in C((1 : ℂ), r), resolvent (S beta) w) x) := by
              simp only [
                ContinuousLinearMap.mul_apply,
                ContinuousLinearMap.smul_apply,
                map_smul,
                smul_smul
              ]
              ring_nf
    _ =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), rout), resolvent (S beta) z)
            ((∮ w in C((1 : ℂ), rin), resolvent (S beta) w) x) := by
              rw [← hIout, hIin]
    _ =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ((2 * Real.pi * Complex.I : ℂ) •
            (∮ w in C((1 : ℂ), rin), resolvent (S beta) w x)) := by
              rw [hOuterApply, hNested]
    _ =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ w in C((1 : ℂ), rin), resolvent (S beta) w x) := by
              rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ w in C((1 : ℂ), r), resolvent (S beta) w x) := by
              rw [hIin]
    _ =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ w in C((1 : ℂ), r), resolvent (S beta) w)) x := by
              rw [ContinuousLinearMap.smul_apply]
              rw [circleIntegral_apply_continuousLinearMap
                (by
                  have hcontR :
                      ContinuousOn (fun z : ℂ => resolvent (S beta) z)
                        (Metric.sphere (1 : ℂ) r) := by
                    intro z hz
                    exact
                      (spectrum.hasDerivAt_resolvent_const_left (hres hz)).continuousAt.continuousWithinAt
                  exact hcontR.circleIntegrable hr.le) x]

end

end MathlibAnalytic
end MGAP4D

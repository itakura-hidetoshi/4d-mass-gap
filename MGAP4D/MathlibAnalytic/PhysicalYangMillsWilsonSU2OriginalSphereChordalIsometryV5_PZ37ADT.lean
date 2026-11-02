import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereInverseV5_PZ37ADS
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADT — exact ADK genuine SU(2) chordal / S³ Euclidean isometry

ADS proved an actual equivalence Φ : original SU(2) ↔ genuine unit
three-sphere in real 4-dimensional Euclidean space. ADT proves that
its Euclidean distance is EXACTLY the preexisting ADK/ADM d_J,
which came from the original normalized real-eight Wilson matrix
feature J, and was calibrated against the genuine Wilson energy.

The new proof expands the actual normalized 2×2 matrix relative trace
in terms of ADR's quaternionic first-column reconstruction and shows
that the original trace kernel and the REAL FOUR coordinate inner
product coincide. Norm-sub-square then identifies the true ADK
chordal distance with the usual S³ Euclidean distance.

This discharges ADQ's original-ball inverse-image/isometry obligation.
The normalized original Haar → normalized S³ surface measure
pushforward remains UNPROVED and is not silently assumed.
No changes to physical Wilson receiver, sources, posterior pair-Haar,
theorem root or Lean/mathlib pins; no mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators ComplexConjugate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "J" => specialUnitaryTwoNormalizedTraceFeatureVector
local notation "V" => p4Q2PZ37ADR_originalFourCoordinates
local notation "Φ" => p4Q2PZ37ADR_originalSU2ToSphere
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance

/-- For the ACTUAL SU(2) matrices, the real trace of the
conjugate-transpose product is twice the real-four first-column
Euclidean inner product. Uses ADR's proven quaternion matrix shape. -/
theorem p4Q2PZ37ADT_genuineTrace_eq_twiceSphereInner (g h : G) :
    (Matrix.trace ((g : Mat).conjTranspose * (h : Mat))).re =
      2 * inner ℝ (V g) (V h) := by
  let a : ℂ := (g : Mat) 0 0
  let b : ℂ := (g : Mat) 1 0
  let c : ℂ := (h : Mat) 0 0
  let d : ℂ := (h : Mat) 1 0
  have hg : (g : Mat) = !![a, -conj b; b, conj a] := by
    simpa [a, b] using p4Q2PZ37ADR_originalMatrix_fromFirstColumn g
  have hh : (h : Mat) = !![c, -conj d; d, conj c] := by
    simpa [c, d] using p4Q2PZ37ADR_originalMatrix_fromFirstColumn h
  have hTrace :
      (Matrix.trace ((g : Mat).conjTranspose * (h : Mat))).re =
        2 * (a.re * c.re + a.im * c.im +
          b.re * d.re + b.im * d.im) := by
    rw [hg, hh]
    simp [Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.conj_re, Complex.conj_im] <;> ring
  have hFour :
      inner ℝ (V g) (V h) =
        a.re * c.re + a.im * c.im + b.re * d.re + b.im * d.im := by
    simp [p4Q2PZ37ADR_originalFourCoordinates,
      PiLp.inner_apply, Fin.sum_univ_four,
      realScalarInner_eq_mul, a, b, c, d] <;> ring
  rw [hTrace, hFour]

/-- The original normalized SU(2) real-trace RELATIVE kernel is
exactly the unit 3-sphere Euclidean inner product of real coordinates.
No replacement kernel or Haar measure is introduced. -/
theorem p4Q2PZ37ADT_originalRelativeTrace_eq_sphereInner (g h : G) :
    specialUnitaryNormalizedTraceRelativeKernel 2 g h =
      inner ℝ (V g) (V h) := by
  have hReal := p4Q2PZ37ADT_genuineTrace_eq_twiceSphereInner g h
  calc
    specialUnitaryNormalizedTraceRelativeKernel 2 g h =
        (Matrix.trace ((g : Mat).conjTranspose * (h : Mat))).re / 2 := by
          unfold specialUnitaryNormalizedTraceRelativeKernel
          rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div]
          rfl
    _ = inner ℝ (V g) (V h) := by
      rw [hReal]
      ring

/-- The squared ACTUAL normalized J-chord and the squared standard
S³ coordinate chord are equal. Every component is the original
SU(2) matrix, with no isometry premise. -/
theorem p4Q2PZ37ADT_originalChordal_sq_eq_sphereChord_sq (g h : G) :
    (dJ g h) ^ 2 = ‖V g - V h‖ ^ 2 := by
  have hInner :
      inner ℝ (J g) (J h) = inner ℝ (V g) (V h) := by
    calc
      inner ℝ (J g) (J h) =
          specialUnitaryNormalizedTraceRelativeKernel 2 g h :=
        (specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector g h).symm
      _ = inner ℝ (V g) (V h) :=
        p4Q2PZ37ADT_originalRelativeTrace_eq_sphereInner g h
  change ‖J g - J h‖ ^ 2 = ‖V g - V h‖ ^ 2
  rw [norm_sub_sq_real, norm_sub_sq_real,
    p4Q2PZ37ADK_trueFeature_norm_sq_one,
    p4Q2PZ37ADK_trueFeature_norm_sq_one,
    p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one,
    p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one,
    hInner]

/-- STRONG UNCONDITIONAL physical metric calibration:
the exact ADK original eight-real normalized Wilson chord is the
ordinary Euclidean distance between original first-column S³ points. -/
theorem p4Q2PZ37ADT_originalChordal_eq_sphereDist (g h : G) :
    dJ g h = dist (Φ g) (Φ h) := by
  have hSq := p4Q2PZ37ADT_originalChordal_sq_eq_sphereChord_sq g h
  have hDist : dist (Φ g) (Φ h) = ‖V g - V h‖ := by
    rfl
  rw [← hDist] at hSq
  have hNonneg : 0 ≤ dJ g h :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg g h
  have hNonnegDist : 0 ≤ dist (Φ g) (Φ h) :=
    dist_nonneg
  nlinarith only [hSq, hNonneg, hNonnegDist]

/-- ADQ's original-ball inverse-image requirement is now proved,
not hypothesized. It is valid for ALL real radii and centers. -/
theorem p4Q2PZ37ADT_originalBall_eq_sphereBallPreimage
    (a : G) (r : ℝ) :
    p4Q2PZ37ADK_trueChordalBall a r =
      Φ ⁻¹' Metric.ball (Φ a) r := by
  ext g
  change dJ a g < r ↔ dist (Φ a) (Φ g) < r
  rw [p4Q2PZ37ADT_originalChordal_eq_sphereDist]

/-- In particular the EXACT ADQ required original identity ball is the
inverse image of its genuine unit 3-sphere ball. -/
theorem p4Q2PZ37ADT_ADQ_ballCondition
    (r : ℝ) :
    p4Q2PZ37ADK_trueChordalBall (1 : G) r =
      Φ ⁻¹' Metric.ball (Φ (1 : G)) r :=
  p4Q2PZ37ADT_originalBall_eq_sphereBallPreimage (1 : G) r

/-- The ADS genuine SU(2)-S³ equivalence strictly preserves the
original ADK chordal distance, without any hypothesis. -/
theorem p4Q2PZ37ADT_genuineEquiv_distance (g h : G) :
    dJ g h =
      dist (p4Q2PZ37ADS_originalSU2EquivSphere g)
        (p4Q2PZ37ADS_originalSU2EquivSphere h) :=
  p4Q2PZ37ADT_originalChordal_eq_sphereDist g h

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADT_genuineTrace_eq_twiceSphereInner
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADT_originalRelativeTrace_eq_sphereInner
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADT_originalChordal_sq_eq_sphereChord_sq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADT_originalChordal_eq_sphereDist
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADT_originalBall_eq_sphereBallPreimage
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADT_ADQ_ballCondition
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADT_genuineEquiv_distance

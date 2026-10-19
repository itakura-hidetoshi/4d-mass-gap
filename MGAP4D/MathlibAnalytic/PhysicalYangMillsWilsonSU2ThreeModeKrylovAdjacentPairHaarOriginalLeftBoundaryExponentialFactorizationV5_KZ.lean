import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointSqrtFourCornerV5_KY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalUnitReceiverWilsonDetectionV5_KX
import Mathlib.Tactic

/-!
# P4-Q2-KZ — exact TRUE physical left-link inverse half-density factorization

KY proves the beta/4 four-corner identity of the actual Perron joint
half-density. Freeze an arbitrary actual reference left boundary L0,
right background R, physical link e, and one right-link anchor h.
Vary ONLY the left link value u and the right insertion g.

The reciprocal joint half-density separates exactly as

  1/s(L0[e:=u],R[e:=g]) =
       C(u) * A(g) * exp(-(beta/4)*<Phi(u),Phi(g)>)

where C(u), A(g) are both strictly POSITIVE and the latter does not
depend on u. This is an exact physical source factorization, not a
synthetic Wilson section. In particular KX's genuine constant physical
unit receiver has the same variable-crossing factor, multiplied by the
literal positive full-spatial kernel mass m0(R[e:=g]).

KZ does NOT yet assert a nonzero signed GI expectation gap. The
negative-coupling feature kernel still needs to be transported via the
genuine SU(2) central sign rotation to KV's positive-coupling
injectivity, followed by exact GN/JQ GI moment identification.
No independent-Haar posterior, rank assumption, sorry/admit, or
continuum result is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num)
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2

/-- Exact reciprocal version of KY's true interacting Perron
half-density four-corner identity. Only strictly positive factors
are divided out, for any actual SU(2) physical-link insertion. -/
theorem p4Q2KZ_originalLeftInverseHalfDensityCross
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (h u g : Gauge) :
    (s b hb (Function.update left₀ e u, Function.update right e g))⁻¹ =
      (s b hb (left₀, Function.update right e h) /
          s b hb (Function.update left₀ e u, Function.update right e h)) *
        Real.exp (-(b / 4) *
          inner ℝ (Phi u - Phi (left₀ e)) (Phi g - Phi h)) *
        (s b hb (left₀, Function.update right e g))⁻¹ := by
  let leftU : Cfg := Function.update left₀ e u
  let x : ℝ := s b hb (leftU, Function.update right e g)
  let y : ℝ := s b hb (left₀, Function.update right e g)
  let a : ℝ := s b hb (leftU, Function.update right e h)
  let c : ℝ := s b hb (left₀, Function.update right e h)
  let d : ℝ := (b / 4) * inner ℝ (Phi u - Phi (left₀ e)) (Phi g - Phi h)
  have hCross : x * c = Real.exp d * (a * y) := by
    dsimp [x, c, a, y, d, leftU]
    simpa using
      (p4Q2KY_originalJointHalfDensityFourCorner_eq_realFeatureExponential
        H b hb (Function.update left₀ e u) left₀ right e g h)
  have hx : x ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
      (leftU, Function.update right e g)).ne'
  have hy : y ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
      (left₀, Function.update right e g)).ne'
  have ha : a ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
      (leftU, Function.update right e h)).ne'
  have hNeg : -(b / 4) *
        inner ℝ (Phi u - Phi (left₀ e)) (Phi g - Phi h) = -d := by
    dsimp [d]
    ring
  rw [hNeg]
  change x⁻¹ = (c / a) * Real.exp (-d) * y⁻¹
  rw [Real.exp_neg]
  field_simp [hx, hy, ha, (Real.exp_pos d).ne']
  nlinarith [hCross]

/-- The strictly positive left-link scalar C(u). Its right-link
anchor h is frozen; C has NO dependence on the variable right g. -/
noncomputable def p4Q2KZ_originalLeftBoundaryScale
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (h u : Gauge) : ℝ :=
  (s b hb (left₀, Function.update right e h) /
      s b hb (Function.update left₀ e u, Function.update right e h)) *
    Real.exp ((b / 4) *
      inner ℝ (Phi u - Phi (left₀ e)) (Phi h))

/-- The strictly positive right-link scalar A(g) depends only on
the fixed reference left boundary, right background, and right g. -/
noncomputable def p4Q2KZ_originalRightLinkScale
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (g : Gauge) : ℝ :=
  Real.exp ((b / 4) * inner ℝ (Phi (left₀ e)) (Phi g)) /
    s b hb (left₀, Function.update right e g)

theorem p4Q2KZ_originalLeftBoundaryScale_pos
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (h u : Gauge) :
    0 < p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u := by
  unfold p4Q2KZ_originalLeftBoundaryScale
  exact mul_pos
    (div_pos
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
        (left₀, Function.update right e h))
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
        (Function.update left₀ e u, Function.update right e h)))
    (Real.exp_pos _)

theorem p4Q2KZ_originalRightLinkScale_pos
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (g : Gauge) :
    0 < p4Q2KZ_originalRightLinkScale H b hb left₀ right e g := by
  unfold p4Q2KZ_originalRightLinkScale
  exact div_pos (Real.exp_pos _)
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
      (left₀, Function.update right e g))

/-- SU(2) real-feature bilinearity gives the EXACT exponential
separation into left-only, right-only and crossing components.
The crossing exponent has the negative beta/4 sign. -/
theorem p4Q2KZ_originalLeftFeatureExponentialSplit
    (b : ℝ) (left₀ : Cfg) (e : Link) (h u g : Gauge) :
    Real.exp (-(b / 4) *
        inner ℝ (Phi u - Phi (left₀ e)) (Phi g - Phi h)) =
      (Real.exp ((b / 4) *
          inner ℝ (Phi u - Phi (left₀ e)) (Phi h)) *
        Real.exp ((b / 4) * inner ℝ (Phi (left₀ e)) (Phi g))) *
        Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- The exact separable left-boundary reciprocal Perron
half-density, with BOTH scalar factors derived and strictly
positive above. In particular A(g) is independent of u. -/
theorem p4Q2KZ_originalLeftBoundaryInverseHalfDensity_factorization
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (h u g : Gauge) :
    (s b hb (Function.update left₀ e u, Function.update right e g))⁻¹ =
      p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u *
        p4Q2KZ_originalRightLinkScale H b hb left₀ right e g *
          Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) := by
  rw [p4Q2KZ_originalLeftInverseHalfDensityCross H b hb left₀ right e h u g,
    p4Q2KZ_originalLeftFeatureExponentialSplit H b left₀ e h u g]
  unfold p4Q2KZ_originalLeftBoundaryScale p4Q2KZ_originalRightLinkScale
  simp only [div_eq_mul_inv]
  ring

/-- KX's LITERAL physical constant-unit receiver, at a genuine
left-link context u, has the KZ separable kernel form. The right
factor retains the genuine full-spatial Wilson kernel mass;
it is NOT a synthetic section or an independent-Haar posterior. -/
theorem p4Q2KZ_originalPhysicalUnitReceiver_leftBoundary_factorization
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (h u g : Gauge) :
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb U e
        (Function.update left₀ e u, right) g =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) b hb‖⁻¹ ^ 2 *
        p4Q2KB_originalSpatialWilsonKernelMass H b (Function.update right e g) *
        (p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u *
          p4Q2KZ_originalRightLinkScale H b hb left₀ right e g *
          Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g))) := by
  rw [p4Q2KX_originalPhysicalUnitReceiver_eq_originalKernelMass]
  rw [div_eq_mul_inv,
    p4Q2KZ_originalLeftBoundaryInverseHalfDensity_factorization
      H b hb left₀ right e h u g]
  try ring

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KZ_originalLeftInverseHalfDensityCross
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KZ_originalLeftBoundaryScale_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KZ_originalRightLinkScale_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KZ_originalLeftFeatureExponentialSplit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KZ_originalLeftBoundaryInverseHalfDensity_factorization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KZ_originalPhysicalUnitReceiver_leftBoundary_factorization

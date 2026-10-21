import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTemporalBanachTaylorMomentV5_NL
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceKernelFeature
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialFourLegInvariantContraction
import Mathlib.Tactic

/-!
# P4-Q2-NM — exact ORIGINAL SU(2) Wilson temporal kernel is a real-8 Gaussian

The existing canonical real matrix feature `specialUnitaryMatrixRealFeature 2`
is the REAL EIGHT-COORDINATE embedding of the actual fundamental
2-by-2 complex SU(2) matrices (four real and four imaginary entries).
It was already introduced and proved to realize the true relative
trace kernel in SpecialUnitaryNormalizedTraceKernelFeature.lean.
We REUSE that mathematics, rather than define a fake gauge space.

NM proves for the ORIGINAL physical SU(2) temporal link x,g:

    ‖J(g)‖² = 2
    chi(x⁻¹g) = ⟪J(x), J(g)⟫_ℝ / 2
              = 1 - ‖J(x)-J(g)‖² / 4
    k_b(x,g) = exp(b) * exp(-b/4 * ‖J(x)-J(g)‖²).

It also proves the original Wilson relative Boltzmann kernel (whose
temporal character exponential has the original factor exp(-b))
is exactly the Gaussian exp(-b/4 * chord²).

Crucially J is INJECTIVE on the actual SU(2) group, because the
already-existing real matrix feature has a genuine real-linear inverse
on all 2x2 complex matrices. Hence chord²>0 at any distinct true
group points, and for b>0 the corresponding genuine Wilson temporal
exponential is strictly smaller off the diagonal.

This is stronger than NK's two fixed sample-point determinant but
is NOT yet strict positivity for arbitrary finite Gram matrices or
full fixed-b linear span density; no signed posterior covariance,
GI nonzero, H1-C3 or continuum mass gap follows merely from this.
No Dobrushin, fake posterior, rank/injectivity axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "J" => specialUnitaryMatrixRealFeature 2
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter

/-- The original SU(2) identity relative trace gives a REAL eight
coordinate feature whose squared Euclidean length is exactly TWO. -/
theorem p4Q2NM_originalSU2RealEightFeature_norm_sq
    (g : Gauge) : ‖J g‖ ^ 2 = 2 := by
  have hIdentity :
      specialUnitaryNormalizedTraceRelativeKernel 2 g g = 1 := by
    unfold specialUnitaryNormalizedTraceRelativeKernel
    rw [inv_mul_cancel]
    exact normalizedSpecialUnitaryRealTrace_one 2 (by norm_num)
  have hScale :=
    specialUnitaryNormalizedTraceRelativeKernel_eq_scaled 2 g g
  rw [hIdentity, specialUnitaryRealTraceRelativeKernel_eq_inner] at hScale
  rw [real_inner_self_eq_norm_sq] at hScale
  norm_num at hScale
  linarith

/-- Exact original Wilson normalized real trace equals HALF the
real Hilbert-Schmidt inner product of its genuine complex-matrix
real-eight-coordinate features. -/
theorem p4Q2NM_originalSU2TemporalCharacter_eq_half_realEight_inner
    (x g : Gauge) :
    chi x g = inner ℝ (J x) (J g) / 2 := by
  calc
    chi x g = specialUnitaryRealTraceRelativeKernel 2 x g / 2 := by
      rw [p4Q2NG_originalSU2TemporalCharacter_eq_trace]
      rfl
    _ = inner ℝ (J x) (J g) / 2 := by
      rw [specialUnitaryRealTraceRelativeKernel_eq_inner]

/-- Exact SU(2) real-eight Gaussian chord identity.
No surrogate distance: the squared norm is taken in the existing
genuine real Hilbert matrix-feature space. -/
theorem p4Q2NM_originalSU2TemporalCharacter_eq_one_sub_realEight_chord_sq
    (x g : Gauge) :
    chi x g = 1 - ‖J x - J g‖ ^ 2 / 4 := by
  rw [p4Q2NM_originalSU2TemporalCharacter_eq_half_realEight_inner]
  rw [norm_sub_sq_real,
    p4Q2NM_originalSU2RealEightFeature_norm_sq x,
    p4Q2NM_originalSU2RealEightFeature_norm_sq g]
  ring

/-- ORIGINAL unnormalized genuine temporal Wilson matrix exponential
is EXACTLY exp(b) times an 8-dimensional real Gaussian in the
actual normalized complex SU(2) matrix-coordinate chord distance. -/
theorem p4Q2NM_originalSU2TemporalWilsonSection_eq_realEightGaussian
    (b : ℝ) (x g : Gauge) :
    p4Q2NJ_originalSU2WilsonTemporalSection b x g =
      Real.exp b * Real.exp (-(b/4) * ‖J x - J g‖ ^ 2) := by
  change Real.exp (b * chi x g) = _
  rw [p4Q2NM_originalSU2TemporalCharacter_eq_one_sub_realEight_chord_sq]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The original complete SU(2) one-link Wilson Boltzmann relative
factor is exactly the pure Gaussian on real-eight SU(2) coordinates.
The original constant exp(-b) is not discarded or renormalized. -/
theorem p4Q2NM_originalSU2WilsonRelativeKernel_eq_realEightGaussian
    (b : ℝ) (x g : Gauge) :
    specialUnitaryWilsonRelativeKernel 2 b x g =
      Real.exp (-(b/4) * ‖J x - J g‖ ^ 2) := by
  rw [specialUnitaryWilsonRelativeKernel_eq_trace]
  have hChi :
      specialUnitaryNormalizedTraceRelativeKernel 2 x g = chi x g := by
    rw [specialUnitaryNormalizedTraceRelativeKernel_eq_scaled,
      specialUnitaryRealTraceRelativeKernel_eq_inner,
      p4Q2NM_originalSU2TemporalCharacter_eq_half_realEight_inner]
    ring
  rw [hChi, p4Q2NM_originalSU2TemporalCharacter_eq_one_sub_realEight_chord_sq]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The ORIGINAL real-eight SU(2) feature is injective.
This follows from its ALREADY FORMALIZED actual real-linear inverse
on all complex 2x2 matrices, not from an assumed embedding axiom. -/
theorem p4Q2NM_originalSU2RealEightFeature_injective :
    Function.Injective (specialUnitaryMatrixRealFeature 2 :
      Gauge → SpecialUnitaryMatrixRealFeatureSpace 2) := by
  intro x g h
  have hMatrix := congrArg (realFeatureComplexMatrixLinearMap 2) h
  have hRaw :
      (x : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa only
      [realFeatureComplexMatrixLinearMap_specialUnitaryMatrixRealFeature]
      using hMatrix
  exact Subtype.ext hRaw

/-- No two distinct ACTUAL SU(2) elements have a vanishing squared
real-eight feature chord. -/
theorem p4Q2NM_originalSU2RealEightFeature_chord_sq_pos
    (x g : Gauge) (hneq : x ≠ g) :
    0 < ‖J x - J g‖ ^ 2 := by
  have hj : J x ≠ J g :=
    fun h => hneq (p4Q2NM_originalSU2RealEightFeature_injective h)
  exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hj)) 2

/-- Arbitrarily close but DISTINCT original SU(2) source/target
holonomies have strictly smaller temporal Wilson exponentials at
every genuine positive coupling. This is NOT an independent Haar
posterior or synthetic physical detector. -/
theorem p4Q2NM_originalSU2TemporalWilsonSection_strict_off_diagonal
    (b : ℝ) (hb : 0 < b) (x g : Gauge) (hneq : x ≠ g) :
    p4Q2NJ_originalSU2WilsonTemporalSection b x g < Real.exp b := by
  rw [p4Q2NM_originalSU2TemporalWilsonSection_eq_realEightGaussian]
  have hd : 0 < ‖J x - J g‖ ^ 2 :=
    p4Q2NM_originalSU2RealEightFeature_chord_sq_pos x g hneq
  have hneg : -(b / 4) * ‖J x - J g‖ ^ 2 < 0 := by
    apply mul_neg_of_neg_of_pos
    · linarith
    · exact hd
  have hExp : Real.exp (-(b/4) * ‖J x - J g‖ ^ 2) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hneg
  simpa only [mul_one] using
    (mul_lt_mul_of_pos_left hExp (Real.exp_pos b))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NM_originalSU2RealEightFeature_norm_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NM_originalSU2TemporalCharacter_eq_half_realEight_inner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NM_originalSU2TemporalCharacter_eq_one_sub_realEight_chord_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NM_originalSU2TemporalWilsonSection_eq_realEightGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NM_originalSU2WilsonRelativeKernel_eq_realEightGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NM_originalSU2RealEightFeature_injective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NM_originalSU2RealEightFeature_chord_sq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NM_originalSU2TemporalWilsonSection_strict_off_diagonal

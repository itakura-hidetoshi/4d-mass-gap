import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2FeatureTensorMonomialV5_KN
import Mathlib.Tactic

/-!
# P4-Q2-KQ — volume-independent actual SU(2) real-feature exponential envelopes

The original SU(2) Wilson plaquette energy has its actual range [0,2].
KH proves its EXACT realization
    E(g⁻¹*h) = 1 - (1/2)*<Phi(g),Phi(h)>
with the REAL matrix feature Phi of the physical SU(2) defining
representation. This immediately yields the actual sharp range
    -2 ≤ <Phi(g),Phi(h)> ≤ 2.

For any REAL parameter t (including the positive Wilson b/2),
the genuine real-feature exponential is uniformly bounded:
    exp(-2|t|) ≤ exp(t*<Phi(g),Phi(h)>) ≤ exp(2|t|)
for all g,h and independently of finite spatial volume H.

These fixed-parameter bounds are the simple, original-kernel
dominating functions needed before passing the finite homogeneous
Haar Gram Taylor series to its exact exponential limit.

No surrogate measure or posterior, rank assumption, sorry/axiom,
GI second context, H1-C3 or continuum 4d mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phi" => specialUnitaryMatrixRealFeature 2

/-- Uniform physical SU(2) matrix real-feature inner-product bound,
directly derived from the EXACT original Wilson energy [0,2]. -/
theorem p4Q2KQ_originalSU2RealFeatureInner_mem_Icc_two
    (g h : Gauge) :
    inner ℝ (Phi g) (Phi h) ∈ Set.Icc (-2 : ℝ) 2 := by
  have h0 :
      0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 (g⁻¹ * h) :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) _
  have h2 :
      specialUnitaryWilsonPlaquetteEnergy 2 (g⁻¹ * h) ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) _
  rw [p4Q2KH_originalSU2WilsonEnergy_eq_realFeatureInner] at h0 h2
  exact ⟨by nlinarith, by nlinarith⟩

/-- The actual SU(2) Wilson Euclidean matrix-feature inner product
has absolute value at most two, uniformly over BOTH SU(2) variables. -/
theorem p4Q2KQ_originalSU2RealFeatureInner_abs_le_two
    (g h : Gauge) :
    |inner ℝ (Phi g) (Phi h)| ≤ 2 :=
  abs_le.mpr (p4Q2KQ_originalSU2RealFeatureInner_mem_Icc_two g h)

/-- Uniform REAL exponent control at any frozen parameter,
independent of the actual physical SU(2) values. -/
theorem p4Q2KQ_originalSU2RealFeatureExponent_abs_le
    (t : ℝ) (g h : Gauge) :
    |t * inner ℝ (Phi g) (Phi h)| ≤ 2 * |t| := by
  rw [abs_mul]
  calc
    |t| * |inner ℝ (Phi g) (Phi h)| ≤ |t| * 2 :=
      mul_le_mul_of_nonneg_left
        (p4Q2KQ_originalSU2RealFeatureInner_abs_le_two g h)
        (abs_nonneg t)
    _ = 2 * |t| := by ring

/-- Strictly positive REAL Wilson feature exponential with an explicit
two-sided pointwise envelope, uniformly over the actual SU(2) variables. -/
theorem p4Q2KQ_originalSU2RealFeatureExponential_twoSided
    (t : ℝ) (g h : Gauge) :
    Real.exp (-2 * |t|) ≤
      Real.exp (t * inner ℝ (Phi g) (Phi h)) ∧
    Real.exp (t * inner ℝ (Phi g) (Phi h)) ≤
      Real.exp (2 * |t|) := by
  have h := p4Q2KQ_originalSU2RealFeatureExponent_abs_le t g h
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith [neg_abs_le (t * inner ℝ (Phi g) (Phi h))]
  · apply Real.exp_le_exp.mpr
    nlinarith [le_abs_self (t * inner ℝ (Phi g) (Phi h))]

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KQ_originalSU2RealFeatureInner_mem_Icc_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KQ_originalSU2RealFeatureInner_abs_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KQ_originalSU2RealFeatureExponent_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KQ_originalSU2RealFeatureExponential_twoSided

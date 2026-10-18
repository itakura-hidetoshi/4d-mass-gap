import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointDensityFourCornerV5_KG
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceKernelFeature
import Mathlib.Tactic

/-!
# P4-Q2-KH — genuine Wilson joint four-corner crossing is a real matrix inner exponential

KG proves the pointwise true original Perron/Wilson joint-density
four-corner multiplicative identity for arbitrary SU(2) left and right
link values. The already-proved matrix realification maps physical
SU(2) matrices into a concrete finite-dimensional real Euclidean space
and realizes real Wilson relative trace as an inner product.

We now convert the exact four-corner factor to
  exp ((b/2) * <Phi(L1_e)-Phi(L2_e), Phi(g)-Phi(h)>),
without choosing a surrogate posterior, differentiating the physical
vacuum, or assuming a source detector rank.

This supplies the mathematically exact feature-kernel interface for
the next (still open) universality/integral-transform injectivity proof.
It does NOT establish that injectivity, any spatial GI nonzero second
context, H1-C3, or continuum Yang-Mills mass gap. No sorry/new axiom.
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
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num)

/-- ORIGINAL SU(2) Wilson relative plaquette action as one minus the
concrete REAL Hilbert-Schmidt matrix feature pairing. No Peter–Weyl
or rank hypothesis is involved in this exact defining-representation identity. -/
theorem p4Q2KH_originalSU2WilsonEnergy_eq_realFeatureInner
    (u v : Gauge) :
    specialUnitaryWilsonPlaquetteEnergy 2 (u⁻¹ * v) =
      1 - (1 / 2 : ℝ) * inner ℝ (Phi u) (Phi v) := by
  rw [specialUnitaryWilsonPlaquetteEnergy_eq]
  change
    1 - specialUnitaryNormalizedTraceRelativeKernel 2 u v =
      1 - (1 / 2 : ℝ) * inner ℝ (Phi u) (Phi v)
  rw [specialUnitaryNormalizedTraceRelativeKernel_eq_scaled,
    specialUnitaryRealTraceRelativeKernel_eq_inner]
  norm_num

/-- The mixed original Wilson crossing energy for arbitrary actual
left-boundary SU(2) link values and right insertions is literally
a real Euclidean feature-difference inner product. -/
theorem p4Q2KH_originalTemporalCrossingFourCorner_eq_realFeatureInner
    (b : ℝ) (left₁ left₂ : Cfg) (e : Link)
    (g h : Gauge) :
    -b *
      ((specialUnitaryWilsonPlaquetteEnergy 2 ((left₁ e)⁻¹ * g) -
          specialUnitaryWilsonPlaquetteEnergy 2 ((left₁ e)⁻¹ * h)) -
        (specialUnitaryWilsonPlaquetteEnergy 2 ((left₂ e)⁻¹ * g) -
          specialUnitaryWilsonPlaquetteEnergy 2 ((left₂ e)⁻¹ * h))) =
      (b / 2) *
        inner ℝ (Phi (left₁ e) - Phi (left₂ e)) (Phi g - Phi h) := by
  rw [p4Q2KH_originalSU2WilsonEnergy_eq_realFeatureInner (left₁ e) g,
    p4Q2KH_originalSU2WilsonEnergy_eq_realFeatureInner (left₁ e) h,
    p4Q2KH_originalSU2WilsonEnergy_eq_realFeatureInner (left₂ e) g,
    p4Q2KH_originalSU2WilsonEnergy_eq_realFeatureInner (left₂ e) h]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  ring

/-- Exact TRUE physical joint-density four-corner identity with the
positive-coupling real matrix-feature exponential. The unknown vacuum
and genuine partition normalizers cancel by the proved KG/GQ/FR chain. -/
theorem p4Q2KH_originalJointFourCorner_eq_realFeatureExponential
    (b : ℝ) (hb : 0 ≤ b)
    (left₁ left₂ right : Cfg) (e : Link) (g h : Gauge) :
    rho b hb (left₁, Function.update right e g) *
      rho b hb (left₂, Function.update right e h) =
    Real.exp ((b / 2) *
      inner ℝ (Phi (left₁ e) - Phi (left₂ e)) (Phi g - Phi h)) *
      (rho b hb (left₁, Function.update right e h) *
        rho b hb (left₂, Function.update right e g)) := by
  rw [p4Q2KG_originalJointDensityFourCorner_eq_temporalExp H b hb
    left₁ left₂ right e g h]
  rw [p4Q2KH_originalTemporalCrossingFourCorner_eq_realFeatureInner
    H b left₁ left₂ e g h]

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KH_originalSU2WilsonEnergy_eq_realFeatureInner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KH_originalTemporalCrossingFourCorner_eq_realFeatureInner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KH_originalJointFourCorner_eq_realFeatureExponential

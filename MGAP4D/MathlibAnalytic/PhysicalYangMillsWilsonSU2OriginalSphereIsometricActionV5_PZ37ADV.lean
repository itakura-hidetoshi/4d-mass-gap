import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereHaarUniquenessV5_PZ37ADU
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADV — genuine SU(2) action on S³ is isometric and transitive

ADU constructed the ORIGINAL Haar-pushed measure on the genuine
Euclidean S³ and proved its invariance under the transported action.
Here the exact action is strengthened geometrically: it is an
isometric, transitive group action (all operations from the ORIGINAL
SU(2), no newly introduced group or measure). Its inverse is
literally the action of g⁻¹. All genuine sphere metric balls are
transported exactly, and the genuine original Haar-pushed measure
has the SAME radial ball mass at EVERY center, without a
sphere-surface measure substitution.

This is a prerequisite for the remaining measure-comparison
problem. It does NOT prove normalized Mathlib toSphere surface
measure invariant under these isometries. Consequently it does
NOT yet identify the two probability measures or claim an
unconditional ADQ radius-only lower bound, H-uniform coercivity
or a continuum four-dimensional Yang–Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "Φ" => p4Q2PZ37ADR_originalSU2ToSphere
local notation "Ψ" => p4Q2PZ37ADS_originalSphereToSU2
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "act" => p4Q2PZ37ADU_originalLeftActionOnSphere
local notation "ν" => p4Q2PZ37ADU_originalHaarOnSphere
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass

/-- The original ADK calibrated Wilson-feature chord is truly
left invariant in the ORIGINAL special-unitary group, as its squared
value is twice the original Wilson energy of g⁻¹h. -/
theorem p4Q2PZ37ADV_originalChordal_leftInvariant (g h k : G) :
    dJ (g * h) (g * k) = dJ h k := by
  have hGroup : (g * h)⁻¹ * (g * k) = h⁻¹ * k := by group
  have hSq : (dJ (g * h) (g * k)) ^ 2 = (dJ h k) ^ 2 := by
    calc
      (dJ (g * h) (g * k)) ^ 2 =
          2 * specialUnitaryWilsonPlaquetteEnergy 2 ((g * h)⁻¹ * (g * k)) :=
        p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy (g * h) (g * k)
      _ = 2 * specialUnitaryWilsonPlaquetteEnergy 2 (h⁻¹ * k) := by rw [hGroup]
      _ = (dJ h k) ^ 2 :=
        (p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy h k).symm
  have h₀ := p4Q2PZ37ADK_trueChordalDistance_nonneg (g * h) (g * k)
  have h₁ := p4Q2PZ37ADK_trueChordalDistance_nonneg h k
  nlinarith only [hSq, h₀, h₁]

/-- Actual transported SU(2) left action has literal identity. -/
theorem p4Q2PZ37ADV_originalLeftAction_one (x : S3) :
    act (1 : G) x = x := by
  change Φ ((1 : G) * Ψ x) = x
  rw [one_mul, p4Q2PZ37ADS_sphere_roundtrip]

/-- True group-action composition; nothing is abstractly assumed. -/
theorem p4Q2PZ37ADV_originalLeftAction_mul (g h : G) (x : S3) :
    act (g * h) x = act g (act h x) := by
  change Φ ((g * h) * Ψ x) = Φ (g * Ψ (Φ (h * Ψ x)))
  rw [p4Q2PZ37ADS_originalSU2_roundtrip, mul_assoc]

theorem p4Q2PZ37ADV_originalLeftAction_inv_left (g : G) (x : S3) :
    act g⁻¹ (act g x) = x := by
  calc
    act g⁻¹ (act g x) = act (g⁻¹ * g) x :=
      (p4Q2PZ37ADV_originalLeftAction_mul g⁻¹ g x).symm
    _ = act (1 : G) x := by rw [inv_mul_cancel]
    _ = x := p4Q2PZ37ADV_originalLeftAction_one x

theorem p4Q2PZ37ADV_originalLeftAction_inv_right (g : G) (x : S3) :
    act g (act g⁻¹ x) = x := by
  calc
    act g (act g⁻¹ x) = act (g * g⁻¹) x :=
      (p4Q2PZ37ADV_originalLeftAction_mul g g⁻¹ x).symm
    _ = act (1 : G) x := by rw [mul_inv_cancel]
    _ = x := p4Q2PZ37ADV_originalLeftAction_one x

/-- Each genuine original SU(2) action is an exact isometry of
the unit three-sphere, by ADT's physical chordal calibration. -/
theorem p4Q2PZ37ADV_originalLeftAction_dist (g : G) (x y : S3) :
    dist (act g x) (act g y) = dist x y := by
  calc
    dist (act g x) (act g y) =
        dJ (g * Ψ x) (g * Ψ y) :=
      (p4Q2PZ37ADT_originalChordal_eq_sphereDist (g * Ψ x) (g * Ψ y)).symm
    _ = dJ (Ψ x) (Ψ y) :=
      p4Q2PZ37ADV_originalChordal_leftInvariant g (Ψ x) (Ψ y)
    _ = dist (Φ (Ψ x)) (Φ (Ψ y)) :=
      p4Q2PZ37ADT_originalChordal_eq_sphereDist (Ψ x) (Ψ y)
    _ = dist x y := by
      rw [p4Q2PZ37ADS_sphere_roundtrip,
        p4Q2PZ37ADS_sphere_roundtrip]

theorem p4Q2PZ37ADV_originalLeftAction_isometry (g : G) :
    Isometry (act g) :=
  Isometry.of_dist_eq (p4Q2PZ37ADV_originalLeftAction_dist g)

/-- The action of each G-element is a fully bundled genuine S³
isometry equivalence, with the original inverse g⁻¹. -/
noncomputable def p4Q2PZ37ADV_originalLeftAction_isometryEquiv (g : G) :
    S3 ≃ᵢ S3 where
  toFun := act g
  invFun := act g⁻¹
  left_inv := p4Q2PZ37ADV_originalLeftAction_inv_left g
  right_inv := p4Q2PZ37ADV_originalLeftAction_inv_right g
  isometry_toFun := p4Q2PZ37ADV_originalLeftAction_isometry g

/-- The original SU(2) action reaches EVERY real unit-three-sphere
point from EVERY other point; transitivity is explicit. -/
theorem p4Q2PZ37ADV_originalLeftAction_transitive (x y : S3) :
    ∃ g : G, act g x = y := by
  refine ⟨Ψ y * (Ψ x)⁻¹, ?_⟩
  change Φ ((Ψ y * (Ψ x)⁻¹) * Ψ x) = y
  have hGroup : (Ψ y * (Ψ x)⁻¹) * Ψ x = Ψ y := by group
  rw [hGroup, p4Q2PZ37ADS_sphere_roundtrip]

/-- Ordinary sphere balls are exactly equivariant under the
ORIGINAL SU(2) action for ALL real radii. -/
theorem p4Q2PZ37ADV_sphereBall_preimage (g : G) (a : S3) (r : ℝ) :
    (act g) ⁻¹' Metric.ball (act g a) r = Metric.ball a r := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_ball]
  rw [p4Q2PZ37ADV_originalLeftAction_dist g x a]

/-- The TRUE normalized original Haar pushforward has the
exact same ball mass at every point of the actual sphere.
This follows from transitive isometric genuine SU(2) action and
ADU's proved measure invariance; no toSphere equality is assumed. -/
theorem p4Q2PZ37ADV_originalHaarSphereBall_mass_eq_radial (a : S3) (r : ℝ) :
    Measure.real ν (Metric.ball a r) = m r := by
  obtain ⟨g, hg⟩ :=
    p4Q2PZ37ADV_originalLeftAction_transitive (Φ (1 : G)) a
  rw [← hg]
  have hMP := p4Q2PZ37ADU_originalLeftAction_preservesHaar g
  have hMass : ν (Metric.ball (act g (Φ (1 : G))) r) =
      ν (Metric.ball (Φ (1 : G)) r) := by
    have hh := hMP.measure_preimage
      (show NullMeasurableSet
        (Metric.ball (act g (Φ (1 : G))) r) ν from
          measurableSet_ball.nullMeasurableSet)
    rw [p4Q2PZ37ADV_sphereBall_preimage] at hh
    exact hh.symm
  change (ν (Metric.ball (act g (Φ (1 : G))) r)).toReal = m r
  rw [hMass]
  exact (p4Q2PZ37ADU_originalRadialMass_eq_pushforwardSphereBall r).symm

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalChordal_leftInvariant
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalLeftAction_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalLeftAction_mul
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalLeftAction_inv_left
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalLeftAction_inv_right
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalLeftAction_dist
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalLeftAction_isometry
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalLeftAction_transitive
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_sphereBall_preimage
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADV_originalHaarSphereBall_mass_eq_radial

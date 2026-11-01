import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHaarFiniteNetCertificateV5_PZ37ADP
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADQ — normalized three-sphere Haar transfer interface

This is the next append-only step after ADP. The ORIGINAL compact
SU(2) Haar and the actual ADK/ADM chordal balls are not replaced.

Fixed mathlib's `Measure.toSphereBallBound` produces a radius-only,
strictly positive fraction of the TOTAL Euclidean three-sphere surface
measure. Its ambient real dimension is exactly four.

A second theorem states the exact, separately checkable two
requirements for transporting that bound to genuine SU(2):
(1) a sphere-coordinate map that identifies the ORIGINAL ADK chordal
ball with the preimage of the sphere chordal ball, and
(2) equality of the original normalized SU(2) Haar with the NORMALIZED
sphere measure, expressed without silently treating `toSphere` as a
probability (it is NOT automatically normalized).

The two bridge requirements are explicitly HYPOTHESES at this stage.
This file DOES NOT yet prove a measure-preserving SU(2) ↔ S³ map,
and therefore does NOT claim an unconditional radius-explicit
small-ball bound, H-uniform coercivity or a continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "haar" => normalizedCompactHaar G
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "surf" => ((volume : Measure E4).toSphere)
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass

local instance p4Q2PZ37ADQ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADQ_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The EXACT real ambient dimension of the unit three-sphere. -/
theorem p4Q2PZ37ADQ_realFourSphere_finrank :
    Module.finrank ℝ E4 = 4 := by
  exact finrank_euclideanSpace_fin

/-- The fixed mathlib `toSphere` measure is NOT normalized:
its total mass is four times the original Euclidean unit-ball volume.
This prevents replacing original Haar by an unverified sphere law. -/
theorem p4Q2PZ37ADQ_sphereSurface_totalMass :
    surf.real (Set.univ : Set S3) =
      4 * (volume : Measure E4).real (Metric.ball 0 1) := by
  simpa only [finrank_euclideanSpace_fin] using
    (Measure.toSphere_real_apply_univ (μ := (volume : Measure E4)))

/-- Radius-only, positive fraction of total authentic three-sphere
surface mass from the FIXED mathlib ball bound. -/
noncomputable def p4Q2PZ37ADQ_sphereRadiusFraction (r : ℝ) : ℝ :=
  ((Measure.toSphereBallBound 4 r : ℝ≥0) : ℝ) / 4

theorem p4Q2PZ37ADQ_sphereRadiusFraction_pos (r : ℝ) :
    0 < p4Q2PZ37ADQ_sphereRadiusFraction r := by
  unfold p4Q2PZ37ADQ_sphereRadiusFraction
  have h : 0 < Measure.toSphereBallBound 4 r :=
    Measure.toSphereBallBound_pos 4 r
  exact div_pos (by exact_mod_cast h) (by norm_num)

/-- NONCONDITIONAL fixed-mathlib quantitative sphere statement.
No substitute SU(2) measure is asserted: this is a theorem on S³. -/
theorem p4Q2PZ37ADQ_trueSphereBall_mass_ge_fraction
    (x : S3) (r : ℝ) (hr : 0 < r) :
    p4Q2PZ37ADQ_sphereRadiusFraction r *
        surf.real (Set.univ : Set S3) ≤
      surf.real (Metric.ball x r) := by
  have h := Measure.toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    (μ := (volume : Measure E4)) hr x
  simp only [finrank_euclideanSpace_fin] at h
  calc
    p4Q2PZ37ADQ_sphereRadiusFraction r *
        surf.real (Set.univ : Set S3) =
        (((Measure.toSphereBallBound 4 r : ℝ≥0) : ℝ)) *
          (volume : Measure E4).real (Metric.ball 0 1) := by
            rw [p4Q2PZ37ADQ_sphereSurface_totalMass]
            unfold p4Q2PZ37ADQ_sphereRadiusFraction
            ring
    _ ≤ surf.real (Metric.ball x r) := h

/-- EXACT conditional original-Haar bridge, with both obstructions visible:
distance/ball identification and NORMALIZED measure transport.
Only when those are independently proved does the S³ quantitative
bound apply to the same original SU(2) radial Haar mass `m`. -/
theorem p4Q2PZ37ADQ_originalRadialMass_ge_fraction_of_bridge
    (f : G → S3)
    (hBall : ∀ r : ℝ,
      BallJ (1 : G) r = f ⁻¹' Metric.ball (f (1 : G)) r)
    (hScale : ∀ s : Set S3,
      Measure.real haar (f ⁻¹' s) *
        surf.real (Set.univ : Set S3) = surf.real s)
    (hTotal : 0 < surf.real (Set.univ : Set S3))
    (r : ℝ) (hr : 0 < r) :
    p4Q2PZ37ADQ_sphereRadiusFraction r ≤ m r := by
  have hSphere :=
    p4Q2PZ37ADQ_trueSphereBall_mass_ge_fraction (f (1 : G)) r hr
  have hEq := hScale (Metric.ball (f (1 : G)) r)
  rw [← hBall r] at hEq
  change m r * surf.real (Set.univ : Set S3) =
    surf.real (Metric.ball (f (1 : G)) r) at hEq
  by_contra hn
  have hlt : m r < p4Q2PZ37ADQ_sphereRadiusFraction r :=
    lt_of_not_ge hn
  have hMul :=
    (mul_lt_mul_right hTotal).mpr hlt
  linarith

/-- A genuine SU(2) ball at ANY original center inherits the same
numeric radius-only floor, but only under the explicit sphere bridge. -/
theorem p4Q2PZ37ADQ_originalAllCenters_ge_fraction_of_bridge
    (f : G → S3)
    (hBall : ∀ r : ℝ,
      BallJ (1 : G) r = f ⁻¹' Metric.ball (f (1 : G)) r)
    (hScale : ∀ s : Set S3,
      Measure.real haar (f ⁻¹' s) *
        surf.real (Set.univ : Set S3) = surf.real s)
    (hTotal : 0 < surf.real (Set.univ : Set S3))
    (a : G) (r : ℝ) (hr : 0 < r) :
    p4Q2PZ37ADQ_sphereRadiusFraction r ≤ Measure.real haar (BallJ a r) := by
  rw [p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial]
  exact p4Q2PZ37ADQ_originalRadialMass_ge_fraction_of_bridge
    f hBall hScale hTotal r hr

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADQ_realFourSphere_finrank
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADQ_sphereSurface_totalMass
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADQ_sphereRadiusFraction_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADQ_trueSphereBall_mass_ge_fraction
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADQ_originalRadialMass_ge_fraction_of_bridge
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADQ_originalAllCenters_ge_fraction_of_bridge

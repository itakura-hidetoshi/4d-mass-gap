import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereOrthogonalSurfaceInvarianceV5_PZ37ADY
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADZ — unconditional ORIGINAL SU(2) Haar radius lower bound

ADY proved, without a measure-transport hypothesis, that the genuine
normalized compact Haar on the ORIGINAL interacting SU(2) pushes forward
to independently defined normalized Mathlib toSphere volume on the unit S³.
ADT already identified every original physical chordal ball with the
preimage of its corresponding literal Euclidean S³ ball. ADQ separately
proved an explicit lower bound using two openly stated bridge obligations.

This file discharges the remaining ADQ bridge obligations exactly:
* preimage evaluation of genuine Haar via the proven homeomorphism,
  for ALL sets (not merely Borel sets);
* the finite nonzero Mathlib surface mass normalization identity;
* strictly positive total surface mass in real dimension four;
* the unchanged original normalized Haar radial bound at the identity
  and at ALL original SU(2) centers, with strict positivity for r > 0.

No substitute gauge group, invented Haar distribution, changed source,
changed interacting posterior or Wilson FF receiver, new physical
assumption, uniform-in-H coercivity, or continuum mass-gap conclusion.
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
local notation "haar" => normalizedCompactHaar G
local notation "ν" => p4Q2PZ37ADU_originalHaarOnSphere
local notation "surf" => Measure.toSphere (volume : Measure E4)
local notation "σprob" => p4Q2PZ37ADU_normalizedMathlibSphereSurface
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass
local notation "κ" => p4Q2PZ37ADQ_sphereRadiusFraction

local instance p4Q2PZ37ADZ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADZ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADZ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADZ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADZ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADZ_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

local instance p4Q2PZ37ADZ_nonemptySphere : Nonempty S3 :=
  ⟨Φ (1 : G)⟩

/-- The genuine original SU(2) Haar preimage measure equals its
already-proved S³ pushforward on EVERY set. A homeomorphism gives a
measurable equivalence, so no hidden Borel-set premise is necessary. -/
theorem p4Q2PZ37ADZ_originalHaar_preimage (s : Set S3) :
    haar (Φ ⁻¹' s) = ν s := by
  have h :=
    p4Q2PZ37ADU_originalSU2HomeomorphSphere.toMeasurableEquiv.map_apply
      (μ := haar) s
  change ν s = haar (Φ ⁻¹' s) at h
  exact h.symm

/-- The ORIGINAL independent toSphere surface mass is exactly the
total surface mass times its PROBABILITY normalization for ALL sets.
In particular the raw toSphere measure is never mistaken for Haar. -/
theorem p4Q2PZ37ADZ_surface_normalization_scale (s : Set S3) :
    Measure.real (σprob : Measure S3) s *
        Measure.real surf (Set.univ : Set S3) =
      Measure.real surf s := by
  let μ : FiniteMeasure S3 := ⟨surf, inferInstance⟩
  have hNN : μ.normalize s * μ.mass = μ s := by
    rw [mul_comm (μ.normalize s) μ.mass]
    exact (μ.self_eq_mass_mul_normalize s).symm
  have hReal : (μ.normalize s : ℝ) * (μ.mass : ℝ) =
      (μ s : ℝ) := by
    exact_mod_cast hNN
  change (μ.normalize : Measure S3).real s *
      (μ : Measure S3).real Set.univ = (μ : Measure S3).real s
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,
    FiniteMeasure.measureReal_eq_coe_coeFn, FiniteMeasure.mass] using hReal

/-- The independent Mathlib S³ surface measure has strictly positive
total mass, so ADQ's normalization does not divide by zero. -/
theorem p4Q2PZ37ADZ_surface_totalMass_pos :
    0 < Measure.real surf (Set.univ : Set S3) := by
  letI : NeZero surf :=
    ⟨Measure.toSphere_ne_zero (volume : Measure E4)⟩
  exact measureReal_univ_pos

/-- The original SU(2) Haar and the INDEPENDENT Mathlib surface
measure satisfy ADQ's full scaling requirement on ALL sphere subsets.
The original sphere homeomorphism and ADY's unconditional Haar
identification completely discharge the prior transport obstruction. -/
theorem p4Q2PZ37ADZ_originalHaar_surface_scale (s : Set S3) :
    Measure.real haar (Φ ⁻¹' s) *
        Measure.real surf (Set.univ : Set S3) =
      Measure.real surf s := by
  have hIdentity : Measure.real haar (Φ ⁻¹' s) =
      Measure.real (σprob : Measure S3) s := by
    change (haar (Φ ⁻¹' s)).toReal =
      ((σprob : Measure S3) s).toReal
    rw [p4Q2PZ37ADZ_originalHaar_preimage s,
      p4Q2PZ37ADY_originalHaarSphere_eq_normalizedSurface]
  rw [hIdentity]
  exact p4Q2PZ37ADZ_surface_normalization_scale s

/-- For EVERY positive radius, the ORIGINAL normalized compact
SU(2) Haar radial mass has a genuine explicit, positive floor.
No conditional surface transport premise remains. -/
theorem p4Q2PZ37ADZ_originalRadialMass_ge_explicit
    (r : ℝ) (hr : 0 < r) : κ r ≤ m r := by
  exact p4Q2PZ37ADQ_originalRadialMass_ge_fraction_of_bridge
    Φ p4Q2PZ37ADT_ADQ_ballCondition
    p4Q2PZ37ADZ_originalHaar_surface_scale
    p4Q2PZ37ADZ_surface_totalMass_pos r hr

/-- The same unconditional radius-dependent quantitative floor holds
at EVERY center in the unchanged, original interacting SU(2). -/
theorem p4Q2PZ37ADZ_originalAllCenters_ge_explicit
    (a : G) (r : ℝ) (hr : 0 < r) :
    κ r ≤ Measure.real haar (BallJ a r) := by
  exact p4Q2PZ37ADQ_originalAllCenters_ge_fraction_of_bridge
    Φ p4Q2PZ37ADT_ADQ_ballCondition
    p4Q2PZ37ADZ_originalHaar_surface_scale
    p4Q2PZ37ADZ_surface_totalMass_pos a r hr

/-- The positive radius-only bound has genuine STRICT positivity,
not merely a nonnegative floor. -/
theorem p4Q2PZ37ADZ_originalRadialMass_pos
    (r : ℝ) (hr : 0 < r) : 0 < m r :=
  lt_of_lt_of_le (p4Q2PZ37ADQ_sphereRadiusFraction_pos r)
    (p4Q2PZ37ADZ_originalRadialMass_ge_explicit r hr)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADZ_originalHaar_preimage
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADZ_surface_normalization_scale
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADZ_surface_totalMass_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADZ_originalHaar_surface_scale
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADZ_originalRadialMass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADZ_originalAllCenters_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADZ_originalRadialMass_pos

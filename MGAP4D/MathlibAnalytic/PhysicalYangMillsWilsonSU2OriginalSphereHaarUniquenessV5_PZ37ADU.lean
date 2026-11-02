import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereChordalIsometryV5_PZ37ADT
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADU — actual SU(2) Haar pushforward, sphere action, uniqueness bridge

ADS proved a genuine original SU(2) ↔ Euclidean 3-sphere bijection.
ADT proved this precise equivalence identifies the ORIGINAL
eight-real Wilson feature chord with Euclidean sphere distance.
ADU:
* upgrades the actual equivalence to a HOMEOMORPHISM using the
  original ADK J-continuity and compactness of ORIGINAL SU(2);
* constructs the actual original normalized SU(2) Haar
  pushforward measure ON THE SAME Mathlib sphere;
* proves it is a genuine PROBABILITY and that its mass on every
  ordinary sphere ball is EXACTLY the original ADM radial mass;
* proves invariance under the full, genuine transported left SU(2)
  action, without any new group law replacing the original gauge;
* proves that ANY other probability sphere measure invariant under
  that very same action must equal the actual Haar pushforward.
  The proof uses the fixed mathlib uniqueness theorem for genuine
  compact group Haar probability.

We also name the probability-normalization of the FIXED mathlib
toSphere volume measure. Its invariance under the genuine SU(2)
transitive orthogonal action remains a distinct OPEN obligation.
The final identity with toSphere is therefore stated CONDITIONAL
on this explicit and nontrivial invariance property.

No substitute finite/discrete Haar, posteriors, source, FF receiver,
new physical hypothesis, theorem-root move or continuum mass-gap claim.
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
local notation "J" => specialUnitaryTwoNormalizedTraceFeatureVector
local notation "haar" => normalizedCompactHaar G
local notation "surf" => Measure.toSphere (volume : Measure E4)
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass

local instance p4Q2PZ37ADU_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADU_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADU_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADU_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADU_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADU_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Continuity is NOT an assumed new topology: ADT's exact metric
equality transports continuity of the ORIGINAL ADK feature J to
the genuine SU(2) → S³ mapping in the original topology. -/
theorem p4Q2PZ37ADU_originalSU2ToSphere_continuous :
    Continuous Φ := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hJ : ContinuousAt (fun b : G => J b) a :=
    p4Q2PZ37ADK_trueFeature_continuous.continuousAt
  have hT := tendsto_iff_dist_tendsto_zero.mp hJ
  have hFun :
      (fun b : G => dist (Φ b) (Φ a)) =
      (fun b : G => dist (J b) (J a)) := by
    funext b
    rw [← p4Q2PZ37ADT_originalChordal_eq_sphereDist b a]
    rfl
  rw [hFun]
  exact hT

/-- The REAL source group is compact, the target sphere is Hausdorff,
and ADR/ADS supply a bijection. Hence the proved continuous map is
an actual homeomorphism, without modifying either topology. -/
noncomputable def p4Q2PZ37ADU_originalSU2HomeomorphSphere : G ≃ₜ S3 := by
  let e := p4Q2PZ37ADS_originalSU2EquivSphere
  have hc : Continuous (e : G → S3) :=
    p4Q2PZ37ADU_originalSU2ToSphere_continuous
  have hClosed : IsClosedMap (e : G → S3) := by
    intro s hs
    exact (hs.isCompact.image hc).isClosed
  exact e.toHomeomorphOfContinuousClosed hc hClosed

/-- The original explicit inverse Ψ is continuous with respect
to the ORIGINAL topology on SU(2), not a replacement metric topology. -/
theorem p4Q2PZ37ADU_originalSphereToSU2_continuous :
    Continuous Ψ := by
  exact p4Q2PZ37ADU_originalSU2HomeomorphSphere.symm.continuous

theorem p4Q2PZ37ADU_originalSU2ToSphere_measurable :
    Measurable Φ :=
  p4Q2PZ37ADU_originalSU2ToSphere_continuous.measurable

theorem p4Q2PZ37ADU_originalSphereToSU2_measurable :
    Measurable Ψ :=
  p4Q2PZ37ADU_originalSphereToSU2_continuous.measurable

/-- The ACTUAL pushforward of the original normalized compact SU(2)
Haar measure, with no substituted probability distribution. -/
noncomputable def p4Q2PZ37ADU_originalHaarOnSphere : Measure S3 :=
  Measure.map Φ haar

/-- True original Haar pushed to S³ is itself a probability. -/
theorem p4Q2PZ37ADU_originalHaarOnSphere_probability :
    IsProbabilityMeasure p4Q2PZ37ADU_originalHaarOnSphere := by
  unfold p4Q2PZ37ADU_originalHaarOnSphere
  exact Measure.isProbabilityMeasure_map
    p4Q2PZ37ADU_originalSU2ToSphere_measurable.aemeasurable

/-- The forward mapping exactly preserves the measure
by DEFINITION of pushforward, with its measurability now proved. -/
theorem p4Q2PZ37ADU_originalHaarToSphere_measurePreserving :
    MeasurePreserving Φ haar p4Q2PZ37ADU_originalHaarOnSphere :=
  ⟨p4Q2PZ37ADU_originalSU2ToSphere_measurable, rfl⟩

/-- The inverse map transports the genuine pushforward BACK to
the exact original normalized SU(2) Haar probability. -/
theorem p4Q2PZ37ADU_originalSphereHaarToSU2_measurePreserving :
    MeasurePreserving Ψ p4Q2PZ37ADU_originalHaarOnSphere haar := by
  refine ⟨p4Q2PZ37ADU_originalSphereToSU2_measurable, ?_⟩
  change Measure.map Ψ (Measure.map Φ haar) = haar
  rw [Measure.map_map
    p4Q2PZ37ADU_originalSphereToSU2_measurable
    p4Q2PZ37ADU_originalSU2ToSphere_measurable]
  have hc : Ψ ∘ Φ = (id : G → G) := by
    funext g
    exact p4Q2PZ37ADS_originalSU2_roundtrip g
  rw [hc, Measure.map_id]

/-- On the actual Mathlib sphere, original SU(2) Haar radial ball
mass equals the mass of the SAME radius ordinary Euclidean sphere
ball under its GENUINE original Haar pushforward, with no assumptions. -/
theorem p4Q2PZ37ADU_originalRadialMass_eq_pushforwardSphereBall
    (r : ℝ) :
    m r =
      Measure.real p4Q2PZ37ADU_originalHaarOnSphere
        (Metric.ball (Φ (1 : G)) r) := by
  change (haar (BallJ (1 : G) r)).toReal =
    (Measure.map Φ haar (Metric.ball (Φ (1 : G)) r)).toReal
  rw [Measure.map_apply
    p4Q2PZ37ADU_originalSU2ToSphere_measurable
    measurableSet_ball]
  rw [← p4Q2PZ37ADT_ADQ_ballCondition]

/-- The EXACT SU(2) left-action transported to the actual sphere,
using both proven inverse maps. It is NOT a newly assumed
or separately chosen action/probability space. -/
def p4Q2PZ37ADU_originalLeftActionOnSphere (g : G) (x : S3) : S3 :=
  Φ (g * Ψ x)

/-- This original SU(2) action is continuous in the sphere coordinate. -/
theorem p4Q2PZ37ADU_originalLeftAction_continuous (g : G) :
    Continuous (p4Q2PZ37ADU_originalLeftActionOnSphere g) := by
  unfold p4Q2PZ37ADU_originalLeftActionOnSphere
  exact p4Q2PZ37ADU_originalSU2ToSphere_continuous.comp
    (continuous_const.mul p4Q2PZ37ADU_originalSphereToSU2_continuous)

/-- Every true original left SU(2) translation preserves
the genuinely transported normalized Haar probability on S³. -/
theorem p4Q2PZ37ADU_originalLeftAction_preservesHaar (g : G) :
    MeasurePreserving (p4Q2PZ37ADU_originalLeftActionOnSphere g)
      p4Q2PZ37ADU_originalHaarOnSphere
      p4Q2PZ37ADU_originalHaarOnSphere := by
  letI : Measure.IsHaarMeasure haar := by
    dsimp [normalizedCompactHaar]
    infer_instance
  have hLeft : MeasurePreserving (fun x : G => g * x) haar haar :=
    measurePreserving_mul_left haar g
  have h := p4Q2PZ37ADU_originalHaarToSphere_measurePreserving.comp
    (hLeft.comp p4Q2PZ37ADU_originalSphereHaarToSU2_measurePreserving)
  simpa only [p4Q2PZ37ADU_originalLeftActionOnSphere,
    Function.comp_def] using h

/-- Uniqueness bridge: ANY S³ probability invariant under the
ACTUAL original SU(2) transported left action has original Haar
as its inverse image. The remaining sphere-surface invariance
is an EXPLICIT hypothesis, not smuggled in as an axiom. -/
theorem p4Q2PZ37ADU_originalHaar_uniqueness_of_sphereInvariant
    (ν : Measure S3) [IsProbabilityMeasure ν]
    (hInvariant : ∀ g : G,
      Measure.map (p4Q2PZ37ADU_originalLeftActionOnSphere g) ν = ν) :
    Measure.map Ψ ν = haar := by
  let back : Measure G := Measure.map Ψ ν
  have hBackProb : IsProbabilityMeasure back := by
    dsimp [back]
    exact Measure.isProbabilityMeasure_map
      p4Q2PZ37ADU_originalSphereToSU2_measurable.aemeasurable
  letI : IsProbabilityMeasure back := hBackProb
  letI : Measure.IsMulLeftInvariant back := by
    constructor
    intro g
    show Measure.map (fun x : G => g * x) back = back
    change Measure.map (fun x : G => g * x) (Measure.map Ψ ν) =
      Measure.map Ψ ν
    rw [Measure.map_map (measurable_const_mul g)
      p4Q2PZ37ADU_originalSphereToSU2_measurable]
    have hFun :
        ((fun x : G => g * x) ∘ Ψ) =
          Ψ ∘ p4Q2PZ37ADU_originalLeftActionOnSphere g := by
      funext x
      exact (p4Q2PZ37ADS_originalSU2_roundtrip (g * Ψ x)).symm
    rw [hFun, ← Measure.map_map
      p4Q2PZ37ADU_originalSphereToSU2_measurable
      (p4Q2PZ37ADU_originalLeftAction_continuous g).measurable]
    rw [hInvariant g]
  have hBackHaar : Measure.IsHaarMeasure back :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior
      back Set.univ isCompact_univ (by simp) (by simp) (by simp)
  letI : Measure.IsHaarMeasure back := hBackHaar
  letI : Measure.IsHaarMeasure haar := by
    dsimp [normalizedCompactHaar]
    infer_instance
  change back = haar
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure back haar

/-- Equivalently, the true original Haar pushforward is the
UNIQUE probability measure on S³ invariant under the genuine
transitive transported SU(2) left action. -/
theorem p4Q2PZ37ADU_sphereProbability_eq_originalHaar_of_invariant
    (ν : Measure S3) [IsProbabilityMeasure ν]
    (hInvariant : ∀ g : G,
      Measure.map (p4Q2PZ37ADU_originalLeftActionOnSphere g) ν = ν) :
    ν = p4Q2PZ37ADU_originalHaarOnSphere := by
  have hBack :=
    p4Q2PZ37ADU_originalHaar_uniqueness_of_sphereInvariant ν hInvariant
  have hc : Φ ∘ Ψ = (id : S3 → S3) := by
    funext x
    exact p4Q2PZ37ADS_sphere_roundtrip x
  calc
    ν = Measure.map Φ (Measure.map Ψ ν) := by
      rw [Measure.map_map
        p4Q2PZ37ADU_originalSU2ToSphere_measurable
        p4Q2PZ37ADU_originalSphereToSU2_measurable,
        hc, Measure.map_id]
    _ = p4Q2PZ37ADU_originalHaarOnSphere := by
      rw [hBack]
      rfl

local instance p4Q2PZ37ADU_sphereNonempty : Nonempty S3 :=
  ⟨Φ (1 : G)⟩

/-- The fixed mathlib additive-Haar-derived sphere surface measure
normalized to a genuine probability. This is not DEFINED using
SU(2) Haar and thus retains the independent comparison challenge. -/
noncomputable def p4Q2PZ37ADU_normalizedMathlibSphereSurface : ProbabilityMeasure S3 :=
  FiniteMeasure.normalize (⟨surf, inferInstance⟩ : FiniteMeasure S3)

/-- An exact normalized surface sphere probability exists independently
of the original gauge-theoretic Haar law. -/
theorem p4Q2PZ37ADU_normalizedMathlibSphereSurface_probability :
    IsProbabilityMeasure
      (p4Q2PZ37ADU_normalizedMathlibSphereSurface : Measure S3) :=
  inferInstance

/-- Precise last descent obligation:
when normalized fixed-mathlib sphere surface measure is proven
invariant under the original SU(2) action, genuine Haar equality
follows from the already verified compact Haar UNIQUENESS theorem.
This does NOT assume the desired measure equality as a hypothesis. -/
theorem p4Q2PZ37ADU_originalHaar_eq_mathlibSphere_of_surfaceInvariant
    (hInvariant : ∀ g : G,
      Measure.map (p4Q2PZ37ADU_originalLeftActionOnSphere g)
        (p4Q2PZ37ADU_normalizedMathlibSphereSurface : Measure S3) =
          (p4Q2PZ37ADU_normalizedMathlibSphereSurface : Measure S3)) :
    p4Q2PZ37ADU_originalHaarOnSphere =
      (p4Q2PZ37ADU_normalizedMathlibSphereSurface : Measure S3) := by
  letI : IsProbabilityMeasure
      (p4Q2PZ37ADU_normalizedMathlibSphereSurface : Measure S3) :=
    p4Q2PZ37ADU_normalizedMathlibSphereSurface_probability
  exact (p4Q2PZ37ADU_sphereProbability_eq_originalHaar_of_invariant
    _ hInvariant).symm

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalSU2ToSphere_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalSphereToSU2_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalSU2ToSphere_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalSphereToSU2_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalHaarOnSphere_probability
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalHaarToSphere_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalSphereHaarToSU2_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalRadialMass_eq_pushforwardSphereBall
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalLeftAction_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalLeftAction_preservesHaar
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalHaar_uniqueness_of_sphereInvariant
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_sphereProbability_eq_originalHaar_of_invariant
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_normalizedMathlibSphereSurface_probability
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADU_originalHaar_eq_mathlibSphere_of_surfaceInvariant

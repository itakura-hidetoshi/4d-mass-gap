import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGIPlaquetteNoCancellationDetectionV5_PZ37ABC2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIJointBoundaryContinuityV5_HI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABD — original centered SINGLE-plaquette physical Hilbert
# source, authentic two-interacting-Wilson-posterior GI gap, open Haar event

ABC2 proved that at EVERY finite H,b>0 one genuine spatial
plaquette source contributes non-a.e.-zero to the ORIGINAL centered
Wilson total physical GI gap. Here we identify that individual
Haar-centered source with an ACTUAL Gauss-law physical Hilbert vector:
one half of the genuine LO physical local Wilson plaquette source
minus its own ORIGINAL Haar mean times the original physical unit.

LO's proved physical two-source response identity and AAI's original
centered Haar plaquette source give EXACT equality between this
physical Hilbert vector's genuine two-original-interacting-posterior
GI expectation gap and ABC's original local contribution.

Consequently the genuine centered local PHYSICAL source has a
non-a.e.-zero original GI gap, and HI's authentic pair-boundary
continuity gives a nonempty OPEN original pair-Haar event of positive
measure where its signed response has a positive absolute threshold.

All witnesses may depend on H,b. These are ORIGINAL Gauss-law Hilbert
sources with the exact original Wilson kernel, positive Perron vacuum,
two interacting conditional posterior laws and full pair-Haar.
The four-edge Wilson plaquette source is local, but its GI/Perron
response is NOT claimed to depend on only four boundary links.
No volume-uniform lower bound, finite-support common cylinder,
residual suppression, endpoint E/F, H1-H4, all-Hilbert coercivity,
new axioms/sorry/admit/native_decide or 4D continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABD_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABD_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABD_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABD_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABD_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ABD_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37ABD_haarOpenPos :
    (normalizedCompactHaar G).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance
local instance p4Q2PZ37ABD_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ABD_pairHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- EXACT original Haar-centered one-plaquette Gauss-law Hilbert
source, as an already constructed LO physical two-source combination.
Neither physical Hilbert carrier nor observable is replaced. -/
noncomputable def p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  p4Q2LO_originalPhysicalLocalTwoSource H p
    (-(1 / 2 : ℝ) *
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
    (1 / 2 : ℝ)

/-- The ABC exact centered Wilson plaquette contribution is LITERALLY
the unchanged two-interacting-posterior GI gap of an actual centered
plaquette vector in the original Gauss-law physical Hilbert space. -/
theorem p4Q2PZ37ABD_localContribution_eq_originalPhysicalGIGap
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z p =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z := by
  let Haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let J := p4Q2JH_originalGIResponseCLM H b hb.le e z
  let m : ℝ :=
    ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂Haar
  change (1 / 2 : ℝ) *
      J (p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p) =
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le
      (p4Q2LO_originalPhysicalLocalTwoSource H p (-(1 / 2 : ℝ) * m) (1 / 2)) e z
  rw [p4Q2LO_originalPhysicalLocalTwoSource_GI_eq
    H b hb.le e z p (-(1 / 2 : ℝ) * m) (1 / 2 : ℝ)]
  simp only [p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource,
    map_sub, map_smul, smul_eq_mul]
  ring

/-- Each finite genuine Wilson model possesses a TRUE local centered
Gauss-law physical Hilbert plaquette source whose two-original-posterior
GI expectation gap is non-a.e.-zero in ORIGINAL boundary pair-Haar. -/
theorem p4Q2PZ37ABD_exists_originalCenteredPhysicalPlaquetteGI_notAEZero
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      ¬ (∀ᵐ z
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le
          (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
          e z = 0) := by
  obtain ⟨e, p, hNotAE⟩ :=
    p4Q2PZ37ABC2_exists_actualLink_and_plaquette_GIContribution_notAEZero
      H b hb
  refine ⟨e, p, ?_⟩
  intro hZero
  apply hNotAE
  filter_upwards [hZero] with z hz
  rw [p4Q2PZ37ABD_localContribution_eq_originalPhysicalGIGap]
  exact hz

/-- A genuine original centered local plaquette PHYSICAL Hilbert
source detects the two distinct actual interacting Wilson posteriors
on an OPEN set of strictly POSITIVE original boundary pair-Haar mass,
with a strictly positive pointwise absolute GI-gap lower threshold.
Witnesses need not be uniform over H. -/
theorem p4Q2PZ37ABD_exists_originalLocalPhysical_openPairHaarGIEvent
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
      (E : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2))
      (delta : ℝ),
      0 < delta ∧ IsOpen E ∧
      0 < periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 E ∧
      ∀ z ∈ E,
        delta ≤ |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le
          (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
          e z| := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  obtain ⟨e, p, hNotAE⟩ :=
    p4Q2PZ37ABD_exists_originalCenteredPhysicalPlaquetteGI_notAEZero
      H b hb
  let D : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le
      (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
      e z
  have hDNotAE : ¬ (∀ᵐ z ∂μ, D z = 0) := hNotAE
  have hPoint : ∃ z0 : Pair, D z0 ≠ 0 := by
    by_contra hn
    apply hDNotAE
    have hz : ∀ z : Pair, D z = 0 := by
      intro z
      by_contra hne
      exact hn ⟨z, hne⟩
    filter_upwards with z
    exact hz z
  obtain ⟨z0, hz0⟩ := hPoint
  have hCont : Continuous D :=
    p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le
      (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
      e
  let delta : ℝ := |D z0| / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact half_pos (abs_pos.mpr hz0)
  let E : Set Pair := {z | delta < |D z|}
  have hOpen : IsOpen E := by
    change IsOpen ((fun z : Pair => |D z|) ⁻¹' Set.Ioi delta)
    exact isOpen_Ioi.preimage hCont.abs
  have hz0E : z0 ∈ E := by
    change delta < |D z0|
    dsimp [delta]
    have hPos : 0 < |D z0| := abs_pos.mpr hz0
    linarith
  have hMass : 0 < μ E := hOpen.measure_pos μ ⟨z0, hz0E⟩
  refine ⟨e, p, E, delta, hdelta, hOpen, hMass, ?_⟩
  intro z hz
  change delta < |D z| at hz
  exact hz.le

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABD_localContribution_eq_originalPhysicalGIGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABD_exists_originalCenteredPhysicalPlaquetteGI_notAEZero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABD_exists_originalLocalPhysical_openPairHaarGIEvent

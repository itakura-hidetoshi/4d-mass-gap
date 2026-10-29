import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredLocalPhysicalGIOpenEventV5_PZ37ABD
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABD2 — true Wilson full physical GI and centered
# local plaquette physical GI have SAME-SIGN positive Haar event

ABD constructs authentic centered single-plaquette sources in the
original Gauss-law Hilbert carrier. ABC proves that the ORIGINAL
centered full spatial Wilson GI two-interacting-posterior expectation
gap is EXACTLY the finite sum of their signed contributions.

At each H,b>0, AAZ gives a genuine link with non-a.e.-zero ORIGINAL
full centered Wilson GI gap, hence a real context z0 with gap != 0.
At that SAME original link and SAME original boundary-pair context,
the signed identity
    full(z0)^2 = sum_p full(z0) * physicalLocal(p,z0)
forces at least ONE *actual* centered physical Wilson plaquette p
to have full(z0)*physicalLocal(p,z0) > 0.

This is a strict SAME-SIGN (signed-cancellation-aware) certificate,
not merely two possibly disjoint positive contexts.
HI proves continuity of both original physical GI responses. Thus
their positive product persists above a strictly positive threshold
on a nonempty OPEN region of strictly positive original pair-Haar
measure. This is an actual positive-measure noncancelling aligned
physical source observation, with no point-mass Haar shortcut.

The chosen link, plaquette, pair-Haar event, and product threshold
depend on H,b; no uniform cylinder support/mass, no positive uniform
GI squared-moment lower bound, and no decay/control of the FULL
remaining signed Wilson plaquette response is inferred.
No changed original Gauss-law Hilbert source/receiver, Wilson kernel,
Perron vacuum, two interacting conditional posteriors, pair-Haar,
or five inherited JL native_decide axioms. No new axioms,
sorry/admit/native_decide, E/F, H1-H4 or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABD2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABD2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABD2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABD2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABD2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ABD2_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37ABD2_haarOpenPos :
    (normalizedCompactHaar G).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance
local instance p4Q2PZ37ABD2_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ABD2_pairHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- At some ACTUAL original spatial link, actual original pair-Haar
boundary context and genuine spatial plaquette, the signed original
FULL centered physical Wilson GI gap and an authentic SINGLE centered
plaquette Gauss-law physical GI gap have strictly POSITIVE product.
They are aligned at exactly the same physical original context. -/
theorem p4Q2PZ37ABD2_exists_originalFull_and_localPhysicalGI_sameSign
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
      (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2),
      0 <
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z *
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le
          (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
          e z := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let F (e : PeriodicHypercubicEvenSpatialSliceLink H) (z : Pair) : ℝ :=
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let L (e : PeriodicHypercubicEvenSpatialSliceLink H) (z : Pair)
      (p : Plaq) : ℝ :=
    p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z p
  obtain ⟨e, hNotAE⟩ :=
    p4Q2PZ37AAZ_exists_originalLink_centeredGIGap_notAEZero H b hb
  have hFNotAE : ¬ (∀ᵐ z ∂μ, F e z = 0) := hNotAE
  have hPoint : ∃ z0 : Pair, F e z0 ≠ 0 := by
    by_contra hn
    apply hFNotAE
    have hz : ∀ z : Pair, F e z = 0 := by
      intro z
      by_contra hne
      exact hn ⟨z, hne⟩
    filter_upwards with z
    exact hz z
  obtain ⟨z0, hFne⟩ := hPoint
  have hSumIdentity :
      (∑ p : Plaq, (F e z0) * L e z0 p) = (F e z0)^2 := by
    calc
      (∑ p : Plaq, (F e z0) * L e z0 p) =
          (F e z0) * (∑ p : Plaq, L e z0 p) := by
        simp only [Finset.mul_sum]
      _ = (F e z0)^2 := by
        rw [← p4Q2PZ37ABC_originalGIGap_eq_sum_truePlaquetteContributions
          H b hb e z0]
        ring
  have hPositiveLocal : ∃ p : Plaq, 0 < (F e z0) * L e z0 p := by
    by_contra hn
    have hBound (p : Plaq) : (F e z0) * L e z0 p ≤ 0 := by
      apply le_of_not_gt
      intro hp
      exact hn ⟨p, hp⟩
    have hSumNonpos :
        (∑ p : Plaq, (F e z0) * L e z0 p) ≤ 0 := by
      calc
        _ ≤ ∑ _p : Plaq, (0 : ℝ) := by
          apply Finset.sum_le_sum
          intro p _hp
          exact hBound p
        _ = 0 := by simp
    have hSqPos : 0 < (F e z0)^2 := sq_pos_of_ne_zero hFne
    have hSqNonpos : (F e z0)^2 ≤ 0 := by
      rw [← hSumIdentity]
      exact hSumNonpos
    exact (not_le_of_gt hSqPos) hSqNonpos
  obtain ⟨p, hp⟩ := hPositiveLocal
  refine ⟨e, p, z0, ?_⟩
  change 0 < (F e z0) *
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le
      (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
      e z0
  rw [← p4Q2PZ37ABD_localContribution_eq_originalPhysicalGIGap
    H b hb e z0 p]
  exact hp

/-- A strictly POSITIVE and same-sign full/local physical Wilson
two-interacting-posterior GI gap PRODUCT persists on an ORIGINAL
nonempty OPEN pair-Haar region of strictly positive Haar measure.
No H-uniform positive measure or signed nonlocal tail estimate. -/
theorem p4Q2PZ37ABD2_exists_originalPositiveMass_alignedLocalPhysicalGIEvent
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
      (E : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2))
      (kappa : ℝ),
      0 < kappa ∧ IsOpen E ∧
      0 < periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 E ∧
      ∀ z ∈ E,
        kappa ≤
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z *
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb.le
            (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
            e z := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  obtain ⟨e, p, z0, hPos⟩ :=
    p4Q2PZ37ABD2_exists_originalFull_and_localPhysicalGI_sameSign H b hb
  let F : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let L : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
      e z
  have hFCont : Continuous F :=
    p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e
  have hLCont : Continuous L :=
    p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e
  let kappa : ℝ := F z0 * L z0 / 2
  have hkappa : 0 < kappa := half_pos hPos
  let E : Set Pair := {z | kappa < F z * L z}
  have hOpen : IsOpen E := by
    change IsOpen ((fun z : Pair => F z * L z) ⁻¹' Set.Ioi kappa)
    exact isOpen_Ioi.preimage (hFCont.mul hLCont)
  have hz0 : z0 ∈ E := by
    change kappa < F z0 * L z0
    dsimp [kappa]
    linarith
  have hMass : 0 < μ E := hOpen.measure_pos μ ⟨z0, hz0⟩
  refine ⟨e, p, E, kappa, hkappa, hOpen, hMass, ?_⟩
  intro z hz
  exact le_of_lt hz

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABD2_exists_originalFull_and_localPhysicalGI_sameSign
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABD2_exists_originalPositiveMass_alignedLocalPhysicalGIEvent

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGIPlaquetteSourceSplittingV5_PZ37ABC
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABC2 — unconditional genuine single-plaquette source detection

ABC decomposes the UNCHANGED original centered Gauss-law physical
Wilson GI two-interacting-posterior expectation gap into the sum of
its actual, individually Haar-centered Wilson plaquette responses,
on the original complete outer pair-Haar boundary configuration.

AAZ establishes that in every finite H,b>0, the authentic whole-source
expectation gap is NOT almost everywhere zero on some genuine link.
A finite sum of functions that all vanish pair-Haar almost everywhere
would also vanish almost everywhere. Hence, at EVERY finite H,b>0,
there exist an ORIGINAL link e and an ORIGINAL plaquette p such that
the actual signed single-plaquette GI contribution does not vanish
pair-Haar almost everywhere. This is a source-level local witness,
not a pointwise artificial detector.

It does NOT imply that the source projector for a local plaquette has
finite-range dependence on the original Wilson/Perron boundary
variables, nor does it supply uniform amplitude, Haar mass, or an
H-independent noncancellation estimate for the full sum.
No new axioms/sorry/admit/native_decide, no conditional Haar
replacement, no changed physical source, two original interacting
posteriors, or continuum mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABC2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABC2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABC2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABC2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABC2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- UNCONDITIONALLY: the actual original centered physical Wilson
two-Wilson-posterior GI expectation gap contains at least ONE actual
single-plaquette Haar-centered physical source contribution whose
signed response is not almost everywhere zero, on the original full
outer pair-Haar measure and at some genuine spatial link. -/
theorem p4Q2PZ37ABC2_exists_actualLink_and_plaquette_GIContribution_notAEZero
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      ¬ (∀ᵐ z
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
        p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z p = 0) := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  obtain ⟨e, hNotAE⟩ :=
    p4Q2PZ37AAZ_exists_originalLink_centeredGIGap_notAEZero H b hb
  refine ⟨e, ?_⟩
  by_contra hNone
  push_neg at hNone
  have hAll : ∀ᵐ z ∂μ,
      ∀ p : Plaq,
        p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z p = 0 := by
    exact (Filter.eventually_all).mpr hNone
  apply hNotAE
  filter_upwards [hAll] with z hz
  rw [p4Q2PZ37ABC_originalGIGap_eq_sum_truePlaquetteContributions]
  apply Finset.sum_eq_zero
  intro p _hp
  exact hz p

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABC2_exists_actualLink_and_plaquette_GIContribution_notAEZero

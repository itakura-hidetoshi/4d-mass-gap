import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalLocalFullGIAlignedHaarEventV5_PZ37ABD2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABE — genuine full/LOCAL physical Wilson signed
# GI cross-response survives integration over the COMPLETE pair-Haar

ABC proved the exact finite sum of genuine centered Wilson plaquette
physical-source GI contributions, and ABD identified each component
with the TWO original interacting Wilson conditional expectations of
an authentic Gauss-law physical Hilbert source. ABA2 proved strict
positivity of the actual full centered Wilson unweighted GI gap-square
integral at SOME true spatial link in every finite H,b>0.

Here integrate the exact original physical finite-sum identity against
the unchanged FULL outer boundary pair-Haar, retaining the actual
signed full physical GI response:
  K_(H,b,e,p) :=
     integral_pairHaar Delta_full(H,b,e,z) *
                       Delta_physicalCenteredPlaquette(H,b,e,p,z).

HI proves continuity of both exact physical GI responses on the
compact real ORIGINAL pair-boundary carrier; the cross-products are
integrable. Thus, without dropping ANY original remote Haar
variables or substituting either interacting conditional posterior:
  SUM over ALL original spatial plaquettes p of K_(H,b,e,p)
      = integral_pairHaar Delta_full(H,b,e,z)^2
      = G_(H,b,e).

By ABA2, at EVERY finite H,b>0, some genuine link has G>0.
Consequently at that SAME true link, SOME actual centered plaquette
Gauss-law physical Hilbert source has K>0 after integration over
EVERY original pair-Haar boundary coordinate.

This is strictly stronger than pointwise / open-event same-sign
witnesses: global signed cross-response is NONCANCELLED AFTER
full original Haar integration for a selected real plaquette.
No uniform positive K floor, selected fixed local plaquette or
finite-support response, common m>0, all-Hilbert coercivity,
E/F, H1-H4, OS/Wightman or continuum Yang-Mills mass gap.
No new axioms, sorry/admit/native_decide, Dobrushin, JL's five
legacy geometry axioms, Wilson kernel/source/Perron/posterior changes.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABE_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABE_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABE_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABE_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABE_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The original FULL centered Gauss-law physical Wilson GI gap
cross-correlated against the true physically centered SINGLE
Wilson plaquette GI gap, integrated on the entire original
boundary pair-Haar measure. Both inner posterior laws remain
distinct and interacting. -/
noncomputable def p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ :=
  ∫ z,
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z *
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le
      (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
      e z
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- Genuine physical two-posterior full/local GI products are
integrable without altering Wilson/Perron normalization: HI gives
continuity and compactness gives integrability on pair-Haar. -/
theorem p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICross_integrable
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Integrable
      (fun z =>
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z *
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le
          (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
          e z)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  have hFull :=
    p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e
  have hLocal :=
    p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e
  exact (hFull.mul hLocal).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- UNCONDITIONALLY, the signed full/local centered physical
cross-moments SUM over every original spatial plaquette to exactly
the SAME full original unweighted genuine Wilson GI moment.
Original complete pair-Haar integration is performed BEFORE
selecting any one local plaquette. -/
theorem p4Q2PZ37ABE_originalSum_fullLocalCross_eq_originalFullGIMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p) =
    p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let F : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let L (p : Plaq) : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
      e z
  have hEach (p : Plaq) :
      Integrable (fun z : Pair => F z * L p z) μ :=
    p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICross_integrable
      H b hb e p
  have hSource (z : Pair) :
      (∑ p : Plaq, L p z) = F z := by
    calc
      (∑ p : Plaq, L p z) =
          ∑ p : Plaq,
            p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution
              H b hb e z p := by
        apply Finset.sum_congr (by ext p; simp)
        intro p _hp
        exact (p4Q2PZ37ABD_localContribution_eq_originalPhysicalGIGap
          H b hb e z p).symm
      _ = F z :=
        (p4Q2PZ37ABC_originalGIGap_eq_sum_truePlaquetteContributions
          H b hb e z).symm
  change (∑ p : Plaq, ∫ z, F z * L p z ∂μ) =
    ∫ z, (F z)^2 ∂μ
  calc
    (∑ p : Plaq, ∫ z, F z * L p z ∂μ) =
        ∫ z, ∑ p : Plaq, F z * L p z ∂μ := by
      rw [integral_finset_sum (Finset.univ : Finset Plaq)
        (fun p _hp => hEach p)]
    _ = ∫ z, F z * F z ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← Finset.mul_sum, hSource z]
    _ = ∫ z, (F z)^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      ring

/-- A TRUE centered one-plaquette Gauss-law PHYSICAL Hilbert source
has strictly POSITIVE global signed original pair-Haar cross-response
with the unchanged FULL centered Wilson source, on some actual link,
at EVERY finite H,b>0. No cancellations can annul ALL integrated
local correlations because their true finite sum is positive. -/
theorem p4Q2PZ37ABE_exists_originalLink_plaquette_positiveGlobalGICross
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      0 < p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
        H b hb e p := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  obtain ⟨e, hMomentPos⟩ :=
    p4Q2PZ37ABA2_exists_originalLink_positiveUnweightedGIMoment H b hb
  have hSumPos :
      0 < ∑ p : Plaq,
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p := by
    rw [p4Q2PZ37ABE_originalSum_fullLocalCross_eq_originalFullGIMoment]
    exact hMomentPos
  have hPos : ∃ p : Plaq,
      0 < p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
        H b hb e p := by
    by_contra hn
    have hBound (p : Plaq) :
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
          H b hb e p ≤ 0 := by
      apply le_of_not_gt
      intro hp
      exact hn ⟨p, hp⟩
    have hSumNonpos :
        (∑ p : Plaq,
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
            H b hb e p) ≤ 0 := by
      calc
        _ ≤ ∑ _p : Plaq, (0 : ℝ) := by
          apply Finset.sum_le_sum
          intro p _hp
          exact hBound p
        _ = 0 := by simp
    exact (not_le_of_gt hSumPos) hSumNonpos
  obtain ⟨p, hp⟩ := hPos
  exact ⟨e, p, hp⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICross_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABE_originalSum_fullLocalCross_eq_originalFullGIMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABE_exists_originalLink_plaquette_positiveGlobalGICross

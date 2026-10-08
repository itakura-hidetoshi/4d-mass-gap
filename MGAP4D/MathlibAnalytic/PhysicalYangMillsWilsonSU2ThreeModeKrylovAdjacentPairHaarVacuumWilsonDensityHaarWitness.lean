import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumRetainedWitnessPythagoras
import Mathlib.Tactic

/-!
# P4: actual Wilson-density formula and pair-Haar norm for posterior vacuum witnesses

The single genuine joint vacuum identified in #5282 and bounded by retained
conditional L2 candidates in #5284 is NOT an abstract replacement vacuum.
It is the original constant pair-Haar vector transported by the EXACT
physical half-density isometry U_beta. This file supplies its literal
joint-a.e. representative:

  U_beta(1)(A,B) = 1 / sqrt(w_beta(A,B))
  w_beta(A,B) = lambda_beta^(-1) Omega_beta(A) K_beta(A,B) Omega_beta(B).

The first identity is an equality a.e. for the ORIGINAL positive-beta
ground-state joint law; the second is already the established definition
of the actual normalized Wilson ground-state weight. No lower uniform
bound on the weight is introduced.

Every candidate error from #5284 also equals the corresponding
pair-Haar L2 error under U_beta.symm. Thus the direct sharp retained
candidate bound can be returned to the original pair-Haar carrier
without a spatial-link-cardinality factor.

These identities expose the real analytic obligations: oscillation of
the physical top eigenvector Omega and Wilson kernel at one right link,
plus the explicit lambda normalization. Their volume-uniform bounds
are not proved here. No Dobrushin, alternative law, or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4VacDensityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4VacDensityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4VacDensitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4VacDensityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4VacDensityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4VacDensitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The exact transported pair-Haar vacuum is the reciprocal of the
sqrt of the original positive-beta Wilson joint normalized density.
This uses the original half-density isometry and the known actual
joint/pair-Haar absolute continuity, not any pointwise equality
of arbitrary L2 representatives. -/
theorem originalGroundStateJointTransportedPairHaarOne_ae_eq_inv_sqrtDensity
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun z => originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta]
      (fun z =>
        (1 : ℝ) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  let one : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
    Lp.const 2 μ (1 : ℝ)
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  have hνμ : ν ≪ μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
      H N hN beta hbeta
  have honeμ : (fun z => one z) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    change (fun z => (Lp.const 2 μ (1 : ℝ)) z) =ᵐ[μ] (fun _ => (1 : ℝ))
    simp
  have honeν : (fun z => one z) =ᵐ[ν] (fun _ => (1 : ℝ)) :=
    hνμ.ae_eq honeμ
  have hU :
      (fun z => U one z) =ᵐ[ν]
        (fun z => one z /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z) := by
    simpa only [U,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv_apply,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
        H N hN beta hbeta one)
  change (fun z => U one z) =ᵐ[ν]
    (fun z => (1 : ℝ) /
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
        H N hN beta hbeta z)
  filter_upwards [hU, honeν] with z huz hone
  rw [huz, hone]

/-- Any original-joint candidate error is exactly the pair-Haar
difference from the actual transported-back candidate. This is
a genuine isometry, with NO two-sided density comparison constants. -/
theorem originalGroundStateJointTransportedPairHaarOne_candidateNorm_eq_pairHaar
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta - g‖ =
      ‖(Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
          (1 : ℝ)) -
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
          H N hN beta hbeta).symm g‖ := by
  let one : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
    Lp.const 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) (1 : ℝ)
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  change ‖U one - g‖ = ‖one - U.symm g‖
  calc
    ‖U one - g‖ = ‖U (one - U.symm g)‖ := by
      rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
    _ = ‖one - U.symm g‖ := U.norm_map _

/-- Full spatial-link witness error transported back exactly to Haar.
There is no sum-vs-sup substitution or link-count multiplier. -/
theorem originalGroundStateJointTransportedPairHaarOne_fullCandidateError_eq_pairHaar
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta - g e‖ ^ 2) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ)) -
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta).symm (g e)‖ ^ 2 := by
  classical
  apply Finset.sum_congr rfl
  intro e _he
  rw [originalGroundStateJointTransportedPairHaarOne_candidateNorm_eq_pairHaar
    H N hN beta hbeta (g e)]

/-- Bring the genuine positive-beta physical projection-drift witness
inequality back to the original pair-Haar norm, using the SAME
retained-context measurable joint witnesses as #5284. The witness
condition is not dropped or replaced by a product law. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_fullProjectionDrift_le_pairHaarCandidates
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (g : PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hg : ∀ e, AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => g e z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) ≤
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ)) -
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta).symm (g e)‖ ^ 2) := by
  have hbound :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_fullProjectionDrift_le_jointCandidates
      H N hN beta hbeta f g hg
  have herror :=
    originalGroundStateJointTransportedPairHaarOne_fullCandidateError_eq_pairHaar
      H N hN beta hbeta g
  rw [herror] at hbound
  exact hbound

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

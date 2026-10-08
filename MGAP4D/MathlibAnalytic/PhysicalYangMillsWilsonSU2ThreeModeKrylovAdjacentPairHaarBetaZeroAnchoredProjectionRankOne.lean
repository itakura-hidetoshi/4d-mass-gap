import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredDrift
import Mathlib.Tactic

/-!
# P4: the genuine beta-zero-anchored projection drift is rank one

The original physical receiver at frozen beta zero is rank one (#5274),
and the original frozen beta-zero transported link projections fix its
entire range (#5278--#5279). For arbitrary NONNEGATIVE frozen beta,
keep exactly the original posterior Q_beta,e = U_beta.symm P_beta,e U_beta
and the same literal beta-zero physical receiver V_0.

The *projection-drift* second term of the two-drift estimate (#5280)
then factors through a SINGLE canonical constant physical input:
  sum_e ||(Q_0,e - Q_beta,e) V_0 f||^2
    = inner(unit,f)^2 * sum_e ||1 - Q_beta,e 1||^2.

The one-link vector and squared identities are provided too.
Consequently the projection-drift term is exactly zero for any
constant-orthogonal physical input, regardless of positive beta.

This is exact at finite volume and has NO explicit link-count factor.
It does not bound the remaining constant-input full-link defect
uniformly in volume. The first receiver-drift term is also open.
No Dobrushin, replacement posterior law, or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4AnchoredRankOneTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AnchoredRankOneCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AnchoredRankOneSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AnchoredRankOneMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AnchoredRankOneBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AnchoredRankOneSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- EXACT rank-one identity for the difference of the two ORIGINAL
transported posterior projections acting on the beta-zero receiver.
The varying positive-beta projection is not replaced or linearized. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_projectionDrift_rankOne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) •
        (pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN 0 (by norm_num) e
              (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
                (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let V := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
  let Q₀ := pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
  let c : ℝ := inner ℝ u f
  have hv : V f = c • V u :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_rankOne H N hN f
  have hfixf : Q₀ (V f) = V f :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed H N hN f e
  have hfixu : Q₀ (V u) = V u :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed H N hN u e
  have hQ : Q (c • V u) = c • Q (V u) :=
    pairHaarTransportedGroundStateSpatialLinkProjection_smul
      H N hN beta hbeta e c (V u)
  change Q₀ (V f) - Q (V f) =
    c • (Q₀ (V u) - Q (V u))
  calc
    Q₀ (V f) - Q (V f) = V f - Q (V f) := by rw [hfixf]
    _ = c • V u - Q (c • V u) := by rw [hv]
    _ = c • V u - c • Q (V u) := by rw [hQ]
    _ = c • (Q₀ (V u) - Q (V u)) := by rw [hfixu, smul_sub]

/-- Linkwise SQUARED projection drift scales by the square of the
true physical constant Fourier coefficient. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_projectionDrift_sq_rankOne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2 =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))‖ ^ 2 := by
  rw [normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_projectionDrift_rankOne
    H N hN beta hbeta f e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- No link-count factor: the entire ACTUAL projection-drift sum is one
physical coefficient squared times the SAME original constant-receiver
posterior projection-drift sum. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_rankOne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))‖ ^ 2) := by
  classical
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
        ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro e _he
        exact normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_projectionDrift_sq_rankOne
          H N hN beta hbeta f e
    _ = _ := by rw [Finset.mul_sum]

/-- In fact V_0(unit) is the LITERAL pair-Haar constant 1 (#5278),
and Q_0 fixes it (#5279): all positive-beta projection drift is the
genuine Dirichlet loss of this single constant function under Q_beta.
No new conditional expectation is introduced. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_eq_constOne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (Lp.const 2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
              (1 : ℝ))‖ ^ 2) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let V₀ := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
  let Q₀ := pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num)
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta
  let w := Lp.const 2
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) (1 : ℝ)
  have hfix : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      Q₀ e (V₀ u) = V₀ u := by
    intro e
    exact normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed H N hN u e
  have hone : V₀ u = w :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_constantUnit_eq_one H N hN
  have hfull :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_rankOne
      H N hN beta hbeta f
  change (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖Q₀ e (V₀ f) - Q e (V₀ f)‖ ^ 2) =
    (inner ℝ u f) ^ 2 * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖w - Q e w‖ ^ 2)
  rw [hfull]
  congr 1
  apply Finset.sum_congr rfl
  intro e _he
  rw [hfix e, hone]

/-- Orthogonality to the physical constant mode kills the ENTIRE
positive-beta projection-drift term, for every finite volume and beta.
Only the separate receiver-drift term of #5280 then remains. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_eq_zero_of_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hOrth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      0 := by
  rw [normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_eq_constOne
    H N hN beta hbeta f, hOrth]
  simp

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

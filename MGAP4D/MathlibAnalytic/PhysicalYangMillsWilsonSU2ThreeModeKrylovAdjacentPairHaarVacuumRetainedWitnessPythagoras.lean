import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredVacuumJointVariance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

/-!
# P4: sharp posterior vacuum approximation by retained-context witnesses

PR #5282 identified the actual positive-beta anchored projection drift
with the conditional-expectation residual of U_beta(1), the *literal*
pair-Haar constant one transported to the original physical
ground-state joint L2 law. It is not enough merely to count links:
the true vacuum function is global, and summing a worst-case single
link estimate can create an unwanted volume factor.

The original conditional expectation is an orthogonal projection
onto the sigma-algebra retaining all information except a selected
right-boundary link. Its sharp Hilbert-space best-approximation
property gives, for EACH jointly L2 retained-measurable witness g_e,

  ||U_beta 1 - g_e||^2
    = ||U_beta 1 - P_beta,e(U_beta 1)||^2
        + ||P_beta,e(U_beta 1) - g_e||^2.

The exact sum and the resulting no-cardinality coefficient bound on
the true physical projection drift are formalized here. This creates
an explicit interface for locally measurable (distance-sensitive)
witness functions; NO such volume-uniform witness estimate is assumed
or claimed. No Dobrushin, alternative posterior, unproved locality
or continuum mass gap is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- The exact orthogonal Pythagorean identity for a genuine L2
conditional expectation and ANY retained-sigma-algebra L2 witness.
The existing mathlib inner_condExpL2_eq_inner_fun supplies orthogonality.
There is no probability, finite-measure, or positivity assumption. -/
theorem realL2_condExp_candidate_pythagoras
    {α : Type*} {m : MeasurableSpace α} [m0 : MeasurableSpace α]
    {μ : Measure α} (hm : m ≤ m0) (f g : Lp ℝ 2 μ)
    (hg : AEStronglyMeasurable[m] (fun a => g a) μ) :
    ‖f - g‖ ^ 2 =
      ‖f - (condExpL2 (μ := μ) ℝ ℝ hm f).1‖ ^ 2 +
      ‖(condExpL2 (μ := μ) ℝ ℝ hm f).1 - g‖ ^ 2 := by
  let p : Lp ℝ 2 μ := (condExpL2 (μ := μ) ℝ ℝ hm f).1
  have hp : AEStronglyMeasurable[m] (fun a => p a) μ :=
    aestronglyMeasurable_condExpL2 hm f
  have hpg : AEStronglyMeasurable[m] (fun a => (p - g) a) μ := by
    exact (hp.sub hg).congr (Lp.coeFn_sub p g).symm
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm f (p - g) hpg
  have horth : inner ℝ (f - p) (p - g) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hi.symm
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (f - p) (p - g) horth
  have hsum : (f - p) + (p - g) = f - g := by abel
  rw [hsum] at hpyth
  exact hpyth

/-- Sharp best-approximation inequality, not the weaker triangle
bound with an extra factor 2 or 4. -/
theorem realL2_condExp_residual_sq_le_candidate
    {α : Type*} {m : MeasurableSpace α} [m0 : MeasurableSpace α]
    {μ : Measure α} (hm : m ≤ m0) (f g : Lp ℝ 2 μ)
    (hg : AEStronglyMeasurable[m] (fun a => g a) μ) :
    ‖f - (condExpL2 (μ := μ) ℝ ℝ hm f).1‖ ^ 2 ≤ ‖f - g‖ ^ 2 := by
  have h := realL2_condExp_candidate_pythagoras hm f g hg
  nlinarith [sq_nonneg (‖(condExpL2 (μ := μ) ℝ ℝ hm f).1 - g‖)]

local instance p4WitnessTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4WitnessCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4WitnessSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4WitnessMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4WitnessBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4WitnessSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- This is a NAME for the existing U_beta(1), not a new physical
vacuum, new measure, or new half-density transform. -/
noncomputable def originalGroundStateJointTransportedPairHaarOne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    H N hN beta hbeta
    (Lp.const 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      (1 : ℝ))

/-- The original joint posterior projection has a sharp exact
Pythagorean decomposition relative to any valid retained-link L2
witness. The original joint law and its retained sigma-algebra are
unchanged. -/
theorem originalGroundStateJointTransportedPairHaarOne_candidate_pythagoras
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hg : AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
      (fun z => g z)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) :
    ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta - g‖ ^ 2 =
      ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e
          (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2 +
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e
          (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta) - g‖ ^ 2 := by
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N e
  let v := originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN beta hbeta e
  change ‖v - g‖ ^ 2 = ‖v - P v‖ ^ 2 + ‖P v - g‖ ^ 2
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply]
  exact realL2_condExp_candidate_pythagoras hm v g hg

/-- The exact all-link candidate decomposition, preserving every true
joint posterior and allowing an independent measurable local witness
for each link. No link-cardinality factor is introduced. -/
theorem originalGroundStateJointTransportedPairHaarOne_fullCandidate_pythagoras
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hg : ∀ e, AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => g e z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta - g e‖ ^ 2) =
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e
            (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2) +
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e
            (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta) -
          g e‖ ^ 2) := by
  classical
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta - g e‖ ^ 2) =
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta e
                (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2 +
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta e
                (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta) -
              g e‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro e _he
        exact originalGroundStateJointTransportedPairHaarOne_candidate_pythagoras
          H N hN beta hbeta e (g e) (hg e)
    _ = _ := by rw [Finset.sum_add_distrib]

/-- The genuine original-joint full-link vacuum variance is bounded
SHARPLY (constant 1) by the sum of L2 errors of arbitrary
retained-measurable witnesses. This is an explicit future locality
interface, NOT a completed volume-uniform estimate. -/
theorem originalGroundStateJointTransportedPairHaarOne_fullResidual_le_candidates
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hg : ∀ e, AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => g e z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e
          (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta - g e‖ ^ 2 := by
  classical
  have hpyth :=
    originalGroundStateJointTransportedPairHaarOne_fullCandidate_pythagoras
      H N hN beta hbeta g hg
  have hnonneg :
      0 ≤ (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e
            (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta) -
          g e‖ ^ 2) := by
    apply Finset.sum_nonneg
    intro e _he
    exact sq_nonneg _
  linarith

/-- Physical consequence: PR #5282's original positive-beta
projection drift is bounded by one physical constant Fourier
coefficient squared times the SUM of retained-context witness
approximation errors. The expression does not multiply by the
number of spatial links. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_fullProjectionDrift_le_jointCandidates
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
        ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta - g e‖ ^ 2) := by
  rw [normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_eq_jointVacuum
    H N hN beta hbeta f]
  have hle :=
    originalGroundStateJointTransportedPairHaarOne_fullResidual_le_candidates
      H N hN beta hbeta g hg
  exact mul_le_mul_of_nonneg_left hle
    (sq_nonneg (inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f))

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

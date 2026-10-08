import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumWilsonDensityHaarWitness
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

/-!
# P4: exact nonvanishing criterion for the physical Wilson posterior vacuum

The latest P4 result (#5285) identifies the ACTUAL joint-L2 vacuum
  U_beta(1) = 1 / sqrt(W_beta)  (joint-a.e.)
for the original normalized Wilson ground-state joint density W_beta.
The genuine one-link posterior P_beta,e is the existing CondExpL2
orthogonal projection onto all left-boundary and all right-boundary
coordinates except the selected link e.

This file proves that the original one-link vacuum posterior energy
vanishes exactly when the transported vacuum has an L2 representative
measurable with respect to this RETAINED sigma-algebra. The full spatial
sum vanishes if and only if this is true for every link, and the same
criterion is stated directly for the original reciprocal square-root
Wilson joint density.

Consequently, non-measurability at any one link is a rigorous
obstruction to exact vanishing at positive beta. We do NOT assert that
non-measurability has already been established at every positive beta
or that any volume-uniform bound has been proved.

No replacement law, fictitious independence assumption, Dobrushin
coefficient, or continuum Yang--Mills mass-gap claim is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- An L2 vector is fixed by its genuine conditional-expectation
orthogonal projection precisely when its original L2 class has a
representative measurable under the retained sigma algebra.
This is a pure mathlib statement; neither finiteness nor positivity
of the measure is needed. -/
theorem realL2_condExp_fixed_iff_retained_aestronglyMeasurable
    {α : Type*} {m : MeasurableSpace α} [m0 : MeasurableSpace α]
    {μ : Measure α} (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    (condExpL2 (μ := μ) ℝ ℝ hm f).1 = f ↔
      AEStronglyMeasurable[m] (fun a => f a) μ := by
  letI : Fact (m ≤ m0) := ⟨hm⟩
  constructor
  · intro hfix
    have hmem : f ∈ lpMeas ℝ ℝ m 2 μ := by
      have hmem0 : (condExpL2 (μ := μ) ℝ ℝ hm f).1 ∈
          lpMeas ℝ ℝ m 2 μ :=
        (condExpL2 (μ := μ) ℝ ℝ hm f).property
      rw [hfix] at hmem0
      exact hmem0
    exact mem_lpMeas_iff_aestronglyMeasurable.mp hmem
  · intro hmeas
    let q : lpMeas ℝ ℝ m 2 μ :=
      ⟨f, mem_lpMeas_iff_aestronglyMeasurable.mpr hmeas⟩
    have hq : (condExpL2 (μ := μ) ℝ ℝ hm
        (q : Lp ℝ 2 μ) : lpMeas ℝ ℝ m 2 μ) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    exact congrArg Subtype.val hq

local instance p4VacRetainedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4VacRetainedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4VacRetainedSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4VacRetainedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4VacRetainedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4VacRetainedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The ACTUAL positive-beta posterior projection fixes the
transported pair-Haar constant vacuum if and only if its L2 class
is measurable under the original full off-target joint context. -/
theorem originalGroundStateJointTransportedPairHaarOne_link_fixed_iff_retained
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta e
        (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta) =
      originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta ↔
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
      (fun z => originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta z)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  let hm := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
    H N e
  let v := originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta
  change
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e v = v) ↔
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
      (fun z => v z)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply]
  exact realL2_condExp_fixed_iff_retained_aestronglyMeasurable hm v

/-- One original posterior-fiber vacuum energy is zero iff the exact
transported physical vacuum is retained-link measurable. -/
theorem originalGroundStateJointTransportedPairHaarOne_linkResidual_sq_zero_iff_retained
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta e
        (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2 = 0 ↔
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
      (fun z => originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta z)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  let v := originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN beta hbeta e
  have hnorm :
      (‖v - P v‖ ^ 2 = 0) ↔ (P v = v) := by
    constructor
    · intro hsq
      have hn : ‖v - P v‖ = 0 := by
        nlinarith [norm_nonneg (v - P v)]
      have hz : v - P v = 0 := norm_eq_zero.mp hn
      exact (sub_eq_zero.mp hz).symm
    · intro hf
      rw [hf]
      simp
  exact hnorm.trans
    (originalGroundStateJointTransportedPairHaarOne_link_fixed_iff_retained
      H N hN beta hbeta e)

/-- The full TRUE positive-beta vacuum joint posterior sum vanishes
iff the vacuum is measurable with respect to every off-target
information sigma algebra. No links are omitted or replaced. -/
theorem originalGroundStateJointTransportedPairHaarOne_fullResidual_zero_iff_allRetained
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e
          (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2) = 0 ↔
    (∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) := by
  classical
  let v := originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN beta hbeta
  have hsum :
      ((∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖v - P e v‖ ^ 2) = 0) ↔
      (∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖v - P e v‖ ^ 2 = 0) := by
    constructor
    · intro hz e
      have h :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ)
          (f := fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
            ‖v - P e v‖ ^ 2)
          (by intro j _hj; exact sq_nonneg _)).mp hz e (Finset.mem_univ e)
      exact h
    · intro hz
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ)
        (f := fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
          ‖v - P e v‖ ^ 2)
        (by intro j _hj; exact sq_nonneg _)).mpr
      intro e _he
      exact hz e
  change ((∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖v - P e v‖ ^ 2) = 0) ↔
    (∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => v z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta))
  constructor
  · intro hz e
    exact (originalGroundStateJointTransportedPairHaarOne_linkResidual_sq_zero_iff_retained
      H N hN beta hbeta e).mp ((hsum.mp hz) e)
  · intro hz
    apply hsum.mpr
    intro e
    exact (originalGroundStateJointTransportedPairHaarOne_linkResidual_sq_zero_iff_retained
      H N hN beta hbeta e).mpr (hz e)

/-- Exact Wilson-density obstruction: vanishing of the original
full positive-beta vacuum posterior energy is equivalent to
retained-link measurability of the ORIGINAL reciprocal square-root
normalized Wilson density (joint-a.e.), for EVERY right link.
No volume-independent density comparison is presupposed. -/
theorem originalGroundStateJointTransportedPairHaarOne_fullResidual_zero_iff_WilsonInverseSqrt_retained
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e
          (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2) = 0 ↔
    (∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => (1 : ℝ) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) := by
  have hae :=
    originalGroundStateJointTransportedPairHaarOne_ae_eq_inv_sqrtDensity
      H N hN beta hbeta
  constructor
  · intro hz e
    have hm :=
      (originalGroundStateJointTransportedPairHaarOne_fullResidual_zero_iff_allRetained
        H N hN beta hbeta).mp hz e
    exact hm.congr hae
  · intro hm
    apply (originalGroundStateJointTransportedPairHaarOne_fullResidual_zero_iff_allRetained
      H N hN beta hbeta).mpr
    intro e
    exact (hm e).congr hae.symm

/-- One witness of non-measurability of the literal reciprocal Wilson
sqrt density at a genuine right link forces strictly positive
full-link posterior vacuum energy. This is a CONDITIONED obstruction,
not an assertion of such a witness for all positive couplings. -/
theorem originalGroundStateJointTransportedPairHaarOne_fullResidual_pos_of_WilsonNotRetained
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (he : ¬ AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => (1 : ℝ) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    0 < (∑ j : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta j
          (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2) := by
  classical
  let v := originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN beta hbeta
  let E : ℝ := ∑ j : PeriodicHypercubicEvenSpatialSliceLink H, ‖v - P j v‖ ^ 2
  have hnonneg : 0 ≤ E := by
    dsimp [E]
    apply Finset.sum_nonneg
    intro j _hj
    exact sq_nonneg _
  have hne : E ≠ 0 := by
    intro hz
    have hmeas :=
      (originalGroundStateJointTransportedPairHaarOne_fullResidual_zero_iff_WilsonInverseSqrt_retained
        H N hN beta hbeta).mp (by simpa only [E, v, P] using hz)
    exact he (hmeas e)
  change 0 < E
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepStageProfile
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

/-!
# Bounded-concrete core invariance under ground-state one-link sweeps

The sharp one-link Haar-variance theorem is currently formulated on the
bounded strongly measurable concrete core of the genuine ground-state joint
law.  The six-spatial sweep-stage profile, however, evaluates successive
one-link residuals at intermediate Hilbert vectors.

This file closes that compatibility point.

A bounded concrete representative `F` remains in the bounded-concrete core
after one genuine one-link `condExpL2` projection.  The proof uses the
ordinary conditional expectation as a measurable representative, its order
preservation and constant-function identity to obtain the essential bound, and
then replaces it by an everywhere bounded indicator representative without
changing its L2 class.  Mathlib's `MemLp.condExpL2_ae_eq_condExp` identifies
that representative with the actual L2 orthogonal projection.

Consequently every finite same-color one-link sweep, and every prefix of the
canonical sweep, stays inside the bounded-concrete core.  This is the exact
input needed to apply the existing sharp one-link theorem stage by stage.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter Set
open scoped BigOperators

noncomputable section

local instance boundedConcreteOneLinkSweepSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundedConcreteOneLinkSweepSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One genuine one-link conditional expectation preserves the bounded
strongly measurable concrete core of the ground-state joint L2 space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  rcases hf with ⟨F, hF, bound, hbound, rfl⟩
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let m :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
      H N target
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N target
  let hF2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_memLp_two
      H N hN beta hbeta F hF bound hbound
  let fL2 :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound
  let B : ℝ := max bound 0
  let G :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ :=
    μJ[F | m]
  let S : Set
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    {z | ‖G z‖ ≤ B}
  let G' :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ :=
    S.indicator G
  letI : IsProbabilityMeasure μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  have hB0 : 0 ≤ B := by
    exact le_max_right _ _
  have hboundB : bound ≤ B := by
    exact le_max_left _ _
  have hFint : Integrable F μJ := by
    exact hF2.integrable (by norm_num)
  have hConstB : Integrable (fun _ :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) => B) μJ :=
    integrable_const B
  have hConstNegB : Integrable (fun _ :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) => -B) μJ :=
    integrable_const (-B)
  have hFle :
      F ≤ᵐ[μJ] fun _ => B := by
    filter_upwards with z
    have habs : |F z| ≤ bound := by
      simpa [Real.norm_eq_abs] using hbound z
    exact (le_abs_self (F z)).trans (habs.trans hboundB)
  have hleF :
      (fun _ :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) => -B) ≤ᵐ[μJ]
        F := by
    filter_upwards with z
    have habs : |F z| ≤ bound := by
      simpa [Real.norm_eq_abs] using hbound z
    have habsB : |F z| ≤ B := habs.trans hboundB
    exact (neg_le_neg habsB).trans (neg_abs_le (F z))
  have hGle :
      G ≤ᵐ[μJ] fun _ => B := by
    have h :=
      MeasureTheory.condExp_mono
        (m := m) hFint hConstB hFle
    simpa [G, MeasureTheory.condExp_const hm] using h
  have hleG :
      (fun _ :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) => -B) ≤ᵐ[μJ]
        G := by
    have h :=
      MeasureTheory.condExp_mono
        (m := m) hConstNegB hFint hleF
    simpa [G, MeasureTheory.condExp_const hm] using h
  have hGabs : ∀ᵐ z ∂μJ, ‖G z‖ ≤ B := by
    filter_upwards [hGle, hleG] with z hzUpper hzLower
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hzLower, hzUpper⟩
  have hGsm : StronglyMeasurable G := by
    simpa [G] using
      (MeasureTheory.stronglyMeasurable_condExp
        (μ := μJ) (m := m) (f := F))
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le hGsm.norm.measurable measurable_const
  have hG'sm : StronglyMeasurable G' := by
    simpa [G'] using hGsm.indicator hS
  have hG'bound : ∀ z, ‖G' z‖ ≤ B := by
    intro z
    by_cases hz : z ∈ S
    · simpa [G', Set.indicator_of_mem hz] using hz
    · simp [G', Set.indicator_of_not_mem hz, hB0]
  have hG'eqG : G' =ᵐ[μJ] G := by
    filter_upwards [hGabs] with z hz
    have hzS : z ∈ S := by
      simpa [S] using hz
    simp [G', Set.indicator_of_mem hzS]
  have hCond :
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target fL2 z) =ᵐ[μJ] G := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply]
    simpa [fL2, G, μJ, m, hm] using
      (hF2.condExpL2_ae_eq_condExp (𝕜 := ℝ) hm)
  refine ⟨G', hG'sm, B, hG'bound, ?_⟩
  apply Lp.ext
  have hConcrete :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta G' hG'sm B hG'bound
  exact hConcrete.trans (hG'eqG.trans hCond.symm)

/-- The fixed-color one-link projection used in the canonical sweep preserves
the bounded-concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color e f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_mem_boundedConcreteCore
      H N hN beta hbeta e.1 f hf

/-- Every finite ordered same-color one-link sweep preserves the bounded
concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (cs : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        cs f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  induction cs generalizing f with
  | nil =>
      simpa [realHilbertProjectionSweep] using hf
  | cons e es ih =>
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      apply ih
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2_mem_boundedConcreteCore
          H N hN beta hbeta color e f hf

/-- In particular every prefix of the canonical fixed-color one-link sweep
lies in the bounded-concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPrefix_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (k : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        (((Finset.univ :
          Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take k)
        f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
      H N hN beta hbeta color
      (((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take k)
      f hf

end

end MGAP4D.MathlibAnalytic

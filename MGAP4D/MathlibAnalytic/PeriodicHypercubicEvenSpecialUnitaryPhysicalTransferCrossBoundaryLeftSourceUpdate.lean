import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryGenuineOneStepL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkSourceFixedBoundedRepresentative
import Mathlib.Tactic

/-!
# Apply the genuine cross-boundary estimate to actual left one-link updates

PR #4963 proves the cross-boundary one-step estimate for a bounded concrete
representative that is pointwise invariant in one left source coordinate.

To use that theorem inside the actual two-sided sweep recurrence we need such a
representative for the genuine left one-link update itself.

Endpoint swap gives this without duplicating the right-side representative
construction:

* endpoint swap preserves the bounded-concrete core;
* the genuine left one-link projection is swap-conjugate to the right one-link
  projection;
* the already-established right source-invariant representative, swapped back,
  is pointwise invariant in the corresponding left source coordinate.

This yields the actual-update estimate

  || P_R,target (P_L,source f)
       - P_L,source(P_R,target(P_L,source f)) ||
    <= c_cross(beta)
       || P_L,source f - P_R,target(P_L,source f) ||.

No new coefficient, cutoff, factor two, link-count factor, or volume factor is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

local instance crossBoundaryLeftSourceUpdateSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryLeftSourceUpdateSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryLeftSourceUpdateSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryLeftSourceUpdateSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryLeftSourceUpdateSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryLeftSourceUpdateSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Swap a concrete joint observable pointwise. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable
    {H N : ℕ}
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  F z.swap

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_stronglyMeasurable
    (H N : ℕ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable
        F) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable]
    using hF.comp_measurable measurable_swap

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_norm_le
    (H N : ℕ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ∀ z,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable
          F z‖ ≤ bound := by
  intro z
  exact hbound z.swap

/-- The bounded concrete L2 class of the pointwise-swapped observable is exactly
endpoint swap applied to the original bounded concrete L2 class. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_swap_eq_swapL2Equiv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable
          F)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_stronglyMeasurable
          H N F hF)
        bound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_norm_le
          H N F bound hbound) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound) := by
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  let f :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound
  let G :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable
      F
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_stronglyMeasurable
      H N F hF
  let hGb :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_norm_le
      H N F bound hbound
  let g :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta G hG bound hGb
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  have hf :
      (fun z => f z) =ᵐ[μJ] F := by
    simpa [f, μJ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
        H N hN beta hbeta F hF bound hbound
  have hg :
      (fun z => g z) =ᵐ[μJ] G := by
    simpa [g, G, hG, hGb, μJ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
        H N hN beta hbeta G hG bound hGb
  have hfSwap :
      (fun z => f z.swap) =ᵐ[μJ] G := by
    have h :=
      hs.quasiMeasurePreserving.ae_eq_comp hf
    simpa [
      Function.comp_def, G,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable]
      using h
  have hEcoe :
      (fun z => E f z) =ᵐ[μJ] (fun z => f z.swap) := by
    change
      (MeasureTheory.Lp.compMeasurePreserving Prod.swap hs f) =ᵐ[μJ]
        (fun z => f z.swap)
    simpa [Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving f hs)
  apply Lp.ext
  filter_upwards [hg, hEcoe, hfSwap] with z hgz hEz hFz
  change g z = E f z
  rw [hgz, hEz, hFz]

/-- Endpoint swap preserves the bounded-concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  rcases hf with ⟨F, hF, bound, hbound, hRep⟩
  let G :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable
      F
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_stronglyMeasurable
      H N F hF
  let hGb :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_norm_le
      H N F bound hbound
  refine ⟨G, hG, bound, hGb, ?_⟩
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta G hG bound hGb =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound) := by
            simpa [G, hG, hGb] using
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_swap_eq_swapL2Equiv
                H N hN beta hbeta F hF bound hbound
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f :=
      congrArg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta)
        hRep

/-- The genuine left one-link conditional expectation preserves the bounded
concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
        H N hN beta hbeta source f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  have hE :
      E f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_boundedConcreteCore
      H N hN beta hbeta f hf
  have hRight :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta source (E f) ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_mem_boundedConcreteCore
      H N hN beta hbeta source (E f) hE
  have hBack :
      E
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta source (E f)) ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_boundedConcreteCore
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta source (E f))
      hRight
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_eq_swap_right_swap
      H N hN beta hbeta source f]
  exact hBack

/-- Every actual left one-link update of a bounded-core vector admits a single
bounded strongly measurable representative that is pointwise invariant in the
same left source coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_exists_bounded_leftSourceInvariant_representative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃ (G :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hG : StronglyMeasurable G)
      (bound : ℝ)
      (hbound : ∀ z, ‖G z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta G hG bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source f ∧
      ∀ (left right :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        G (Function.update left source value, right) = G (left, right) := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  have hE :
      E f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_boundedConcreteCore
      H N hN beta hbeta f hf
  obtain ⟨F, hF, bound, hbound, hRep, hInvariant⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_sourceInvariant_representative
      H N hN beta hbeta source (E f) hE
  let G :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable
      F
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_stronglyMeasurable
      H N F hF
  let hGb :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable_norm_le
      H N F bound hbound
  refine ⟨G, hG, bound, hGb, ?_, ?_⟩
  · calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta G hG bound hGb =
        E
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound) := by
              simpa [G, hG, hGb, E] using
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_swap_eq_swapL2Equiv
                  H N hN beta hbeta F hF bound hbound
      _ =
        E
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta source (E f)) :=
        congrArg E hRep
      _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source f := by
            symm
            exact
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_eq_swap_right_swap
                H N hN beta hbeta source f
  · intro left right value
    unfold G
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapConcreteObservable
    exact hInvariant right left value

/-- The actual left-source update satisfies the genuine cross-boundary norm
leakage estimate with the unchanged cross coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftSourceUpdate_leakage_norm_le_crossCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta source f) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source f))‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
                H N hN beta hbeta source f)‖ := by
  obtain ⟨G, hG, bound, hbound, hRep, hInvariant⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_exists_bounded_leftSourceInvariant_representative
      H N hN beta hbeta source f hf
  have hSq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftLeakage_norm_sq_le_crossCoefficient_sq_mul_targetResidual
      H N hN beta hbeta hBetaLt source target G hG bound hbound hInvariant
  rw [hRep] at hSq
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
      beta
  let a :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta source f) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source f))‖
  let b :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta source f)‖
  have hc : 0 ≤ c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_nonneg
      beta hbeta
  have hab : 0 ≤ c * b := mul_nonneg hc (norm_nonneg _)
  have hSq' : a ^ 2 ≤ (c * b) ^ 2 := by
    simpa [a, b, c, pow_two] using hSq
  have hNorm : a ≤ c * b :=
    (sq_le_sq₀ (norm_nonneg _) hab).mp hSq'
  simpa [a, b, c] using hNorm

end

end MathlibAnalytic
end MGAP4D

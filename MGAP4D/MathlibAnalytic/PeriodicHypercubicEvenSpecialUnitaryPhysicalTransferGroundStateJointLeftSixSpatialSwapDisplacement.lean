import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSwapOneLinkConjugacy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOrderedRelativeFrame
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialConditionalExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialGroupedLinkSweep
import Mathlib.Tactic

/-!
# Endpoint-swap transport of whole spatial-color sweeps

The genuine ground-state joint law is exactly invariant under exchanging the
two boundary configurations, and #4951 already proves one-link conjugacy.
G1 also needs the same symmetry at the six spatial-color block level.

This file proves:

* swap exchanges the right- and left-color retained sigma-algebras;
* swap conjugates the corresponding color conditional expectations;
* swap conjugates any finite right one-link sweep to the matching left sweep;
* whole left-color sweep displacement is therefore controlled by the existing
  #4943 right-color displacement estimate with exactly the same coefficient.

No link-count, lattice-volume, rank, or commutativity coefficient is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance groundStateJointSwapColorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointSwapColorSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointSwapColorSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointSwapColorSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointSwapColorSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointSwapColorSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pulling the right-color retained sigma-algebra back by endpoint swap gives
exactly the corresponding left-color retained sigma-algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_comap_swap_eq_left
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    MeasurableSpace.comap Prod.swap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color) =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N color := by
  unfold
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
  simp_rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
  rfl

/-- Conversely, pulling the left-color retained sigma-algebra back by endpoint
swap recovers the corresponding right-color retained sigma-algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_comap_swap_eq_right
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    MeasurableSpace.comap Prod.swap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N color := by
  unfold
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
  simp_rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
  rfl

/-- Swap sends right-color measurable L2 vectors to the matching left-color
measurable subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_leftSpatialColor_lpMeas_of_mem_right
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf : f ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  let π :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  rcases hf with ⟨g, hg, hfg⟩
  have hswap :
      @Measurable
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color)
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color)
        Prod.swap := by
    rw [measurable_iff_comap_le]
    exact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_comap_swap_eq_left
        H N color).le
  refine ⟨g ∘ Prod.swap, hg.comp_measurable hswap, ?_⟩
  have hfgSwap :
      ((fun z => f z) ∘ Prod.swap) =ᵐ[π] (g ∘ Prod.swap) :=
    hs.quasiMeasurePreserving.ae_eq_comp hfg
  have hcoe :
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f z) =ᵐ[π]
        ((fun z => f z) ∘ Prod.swap) := by
    change
      (MeasureTheory.Lp.compMeasurePreserving Prod.swap hs f) =ᵐ[π]
        ((fun z => f z) ∘ Prod.swap)
    simpa [Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving f hs)
  exact hcoe.trans hfgSwap

/-- Swap sends left-color measurable L2 vectors back to the matching right-color
measurable subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_rightSpatialColor_lpMeas_of_mem_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf : f ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  let π :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  rcases hf with ⟨g, hg, hfg⟩
  have hswap :
      @Measurable
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color)
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color)
        Prod.swap := by
    rw [measurable_iff_comap_le]
    exact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_comap_swap_eq_right
        H N color).le
  refine ⟨g ∘ Prod.swap, hg.comp_measurable hswap, ?_⟩
  have hfgSwap :
      ((fun z => f z) ∘ Prod.swap) =ᵐ[π] (g ∘ Prod.swap) :=
    hs.quasiMeasurePreserving.ae_eq_comp hfg
  have hcoe :
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f z) =ᵐ[π]
        ((fun z => f z) ∘ Prod.swap) := by
    change
      (MeasureTheory.Lp.compMeasurePreserving Prod.swap hs f) =ᵐ[π]
        ((fun z => f z) ∘ Prod.swap)
    simpa [Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving f hs)
  exact hcoe.trans hfgSwap

/-- Endpoint swap conjugates the genuine right-color conditional expectation
to the corresponding genuine left-color conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialColorCondExpL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
        H N hN beta hbeta color
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f) := by
  let hR :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
      H N color
  let hL :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
      H N color
  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color ≤
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
    ⟨hR⟩
  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color ≤
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
    ⟨hL⟩
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  let R :=
    lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
  let L :=
    lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_apply]
  change E (R.starProjection f) = L.starProjection (E f)
  symm
  refine L.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_leftSpatialColor_lpMeas_of_mem_right
        H N hN beta hbeta color (R.starProjection f)
        (R.starProjection_apply_mem f)
  · intro w hw
    have hEw : E w ∈ R :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_rightSpatialColor_lpMeas_of_mem_left
        H N hN beta hbeta color w hw
    have horth := R.starProjection_inner_eq_zero f (E w) hEw
    calc
      inner ℝ (E f - E (R.starProjection f)) w =
          inner ℝ (E (f - R.starProjection f)) (E (E w)) := by
            rw [E.map_sub,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_apply_apply
                H N hN beta hbeta w]
      _ = inner ℝ (f - R.starProjection f) (E w) := by
            rw [E.inner_map_map]
      _ = 0 := horth

/-- Equivalent isolated formula for the genuine left-color projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_eq_swap_right_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
        H N hN beta hbeta color f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
            H N hN beta hbeta f)) := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialColorCondExpL2
      H N hN beta hbeta color
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f)
  simpa using h.symm

/-- Endpoint swap preserves color residual norms while exchanging the right and
left color projections. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialColorResidual_norm_eq_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
            H N hN beta hbeta f)‖ =
      ‖f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color f‖ := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
      H N hN beta hbeta color
  calc
    ‖E f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
          H N hN beta hbeta color (E f)‖ =
        ‖E (f - P f)‖ := by
          rw [E.map_sub]
          rw [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialColorCondExpL2
              H N hN beta hbeta color f]
    _ = ‖f - P f‖ := E.norm_map (f - P f)
    _ = _ := rfl

/-- Endpoint swap conjugates any finite right one-link sweep to the matching
left one-link sweep, in the supplied order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLinkSweep
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (links : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta)
          links f) =
      realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta)
        links
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f) := by
  induction links generalizing f with
  | nil =>
      simp [realHilbertProjectionSweep]
  | cons e links ih =>
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      rw [ih]
      congr 1
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLinkCondExpL2
          H N hN beta hbeta e f

/-- Equivalent isolated formula for an arbitrary left one-link sweep. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkSweep_eq_swap_right_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (links : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta)
        links f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta)
          links
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
            H N hN beta hbeta f)) := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLinkSweep
      H N hN beta hbeta links
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f)
  simpa using h.symm

/-- Swap preserves the displacement norm of a finite sweep while exchanging
right and left one-link families. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkSweep_displacement_norm_eq_right_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (links : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    ‖f -
        realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta)
          links f‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f -
        realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta)
          links
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
            H N hN beta hbeta f)‖ := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
      H N hN beta hbeta
  have hLeft :
      realHilbertProjectionSweep L links f =
        E (realHilbertProjectionSweep R links (E f)) := by
    simpa [E, R, L] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkSweep_eq_swap_right_swap
        H N hN beta hbeta links f
  have hSwapLeft :
      E (realHilbertProjectionSweep L links f) =
        realHilbertProjectionSweep R links (E f) := by
    have h := congrArg E hLeft
    simpa [E,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_apply_apply] using h
  calc
    ‖f - realHilbertProjectionSweep L links f‖ =
        ‖E (f - realHilbertProjectionSweep L links f)‖ := by
          symm
          exact E.norm_map (f - realHilbertProjectionSweep L links f)
    _ = ‖E f - E (realHilbertProjectionSweep L links f)‖ := by
          rw [E.map_sub]
    _ = ‖E f - realHilbertProjectionSweep R links (E f)‖ := by
          rw [hSwapLeft]
    _ = _ := rfl

/-- Whole left-color sweep displacement has exactly the same volume-free bound
as the existing right-color theorem, transported by endpoint swap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftFixedColor_sweep_displacement_le_one_add_sqrt_lossRatio_mul_colorResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 8 < s)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.jointLeakageLossContractionCutoff s hs)
    (c : Fin 6)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    ‖f -
        realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta)
          (GroundStateSourceFixedPairEnergy.sixSpatialColorLinkList H c) f‖ ≤
      (1 + Real.sqrt (GroundStateSourceFixedPairEnergy.jointLeakageLossRatio s beta)) *
        ‖f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  have hRight :=
    GroundStateSourceFixedPairEnergy.fixedColor_sweep_displacement_le_one_add_sqrt_lossRatio_mul_colorResidual
      H N hN beta hbeta s hs hcut
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
      (E f)
  have hRightSweep :
      ‖E f -
          realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta)
            (GroundStateSourceFixedPairEnergy.sixSpatialColorLinkList H c)
            (E f)‖ ≤
        (1 + Real.sqrt (GroundStateSourceFixedPairEnergy.jointLeakageLossRatio s beta)) *
          ‖E f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
              (E f)‖ := by
    rw [
      GroundStateSourceFixedPairEnergy.sixSpatialColorLinkList_sweep_eq
        H N hN beta hbeta c (E f)]
    exact hRight
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkSweep_displacement_norm_eq_right_swap
      H N hN beta hbeta
      (GroundStateSourceFixedPairEnergy.sixSpatialColorLinkList H c) f]
  have hColor :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialColorResidual_norm_eq_left
      H N hN beta hbeta
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
      (E f)
  have hColor' :
      ‖E f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
          (E f)‖ =
        ‖f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ := by
    simpa [E,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_apply_apply] using
      hColor.symm
  rw [← hColor']
  exact hRightSweep

end

end MathlibAnalytic
end MGAP4D

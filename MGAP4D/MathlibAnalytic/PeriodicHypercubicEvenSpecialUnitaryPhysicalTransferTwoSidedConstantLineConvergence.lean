import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedLossContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointAllRightRetainedGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialResidualKernel
import MGAP4D.MathlibAnalytic.RealHilbertNestedBlockProjectionSweepPathLoss
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# Constant-line fixed geometry and convergence of the full two-sided one-link sweep

PR #4969 gives strict geometric path-loss decay for the complete tagged
right/left one-link sweep on every genuine joint L2 vector.

This file identifies the actual fixed space of that sweep.

* all right one-link fixedness is the already-proved complete left-boundary
  retained subspace;
* all left one-link fixedness is transported by the endpoint-swap L2 isometry;
* under pair Haar, fst-measurability of the swapped representative is exactly
  snd-measurability of the original representative;
* simultaneous fst/snd measurability collapses qualitatively to a constant;
* hence the common fixed space of every tagged one-link projection is exactly
  the intrinsic joint constant line.

The orthogonal projection onto that line absorbs every one-link update.  The
generic geometric-loss convergence theorem therefore identifies the actual
iterated full sweep with the constant-line projection.

No new coefficient or finite-cardinality factor is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace InnerProduct

noncomputable section

local instance twoSidedConstantLineConvergenceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoSidedConstantLineConvergenceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance twoSidedConstantLineConvergenceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoSidedConstantLineConvergenceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoSidedConstantLineConvergenceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance twoSidedConstantLineConvergenceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Left one-link analogue of the existing right one-link fixed-space theorem:
the genuine left conditional expectation fixes exactly its literal retained
L2 subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_fixed_iff_mem_lpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
        H N hN beta hbeta target x = x ↔
      x ∈ lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
          H N target)
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace_le
      H N target
  constructor
  · intro hfixed
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
          H N target)
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
      condExpL2 ℝ ℝ hm x
    have hq :
        (q :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta) = x := by
      simpa [q, hm] using hfixed
    rw [← hq]
    exact q.property
  · intro hx
    letI : Fact
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
            H N target ≤
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
      ⟨hm⟩
    let q : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
          H N target)
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
      ⟨x, hx⟩
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_apply]
    have hq :
        (condExpL2 ℝ ℝ hm
          (q :
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta) :
          lpMeas ℝ ℝ
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
              H N target)
            2
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
              H N hN beta hbeta)) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    exact congrArg
      (fun z : lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
            H N target)
          2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) =>
        (z :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta))
      hq

/-- Pair-Haar measurable transport through endpoint swap at the boundary sigma
level: fst-measurability of f after swapping is snd-measurability of f. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_aestronglyMeasurable_snd_of_swap_fst
    (H N : ℕ)
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (h :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
        (fun z => f z.swap)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.snd
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
      f
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μPair := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let LeftSigma : MeasurableSpace (X × X) :=
    MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace X)
  let RightSigma : MeasurableSpace (X × X) :=
    MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace X)
  have hSwap :
      @Measurable (X × X) (X × X) RightSigma LeftSigma Prod.swap := by
    apply Measurable.of_comap_le
    simp [LeftSigma, RightSigma, MeasurableSpace.comap_comp, Function.comp_def]
  have hPairSwap :
      MeasurePreserving Prod.swap μPair μPair := by
    simpa [μPair, μ,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  let g := h.mk (fun z => f z.swap)
  have hg :
      StronglyMeasurable[RightSigma] (fun z => g z.swap) := by
    exact h.stronglyMeasurable_mk.comp_measurable hSwap
  have hAe :
      (fun z => g z.swap) =ᵐ[μPair] f := by
    have hcomp :=
      hPairSwap.quasiMeasurePreserving.ae_eq_comp h.ae_eq_mk
    simpa [g, Function.comp_def] using hcomp.symm
  exact ⟨fun z => g z.swap, hg, hAe⟩

/-- Simultaneous fixedness under every genuine right and left one-link
conditional expectation forces an actual constant vector in the genuine joint
L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_all_fixed_mem_constantLine
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hfixed :
      ∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta e z = z) :
    z ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
        H N hN beta hbeta := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let μPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let LeftSigma : MeasurableSpace (X × X) :=
    MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace X)
  let RightSigma : MeasurableSpace (X × X) :=
    MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace X)
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  have hRight :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e z = z := by
    intro e
    exact hfixed (Sum.inl e)
  have hzLeftFixed :
      GroundStateSourceFixedPairEnergy.allRightLeftRetainedCondExpL2
          H N hN beta hbeta z = z :=
    (GroundStateSourceFixedPairEnergy.allRightLink_fixed_iff_leftRetained
      H N hN beta hbeta z).1 hRight
  have hzLeft :
      z ∈ lpMeas ℝ ℝ LeftSigma 2 μJ := by
    exact
      (GroundStateSourceFixedPairEnergy.allRightLeftRetained_fixed_iff_mem
        H N hN beta hbeta z).1 hzLeftFixed
  have hLeft :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta e z = z := by
    intro e
    exact hfixed (Sum.inr e)
  have hERight :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e (E z) = E z := by
    intro e
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e (E z) =
        E
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta e z) := by
              symm
              exact
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_leftSpatialLinkCondExpL2
                  H N hN beta hbeta e z
      _ = E z := congrArg E (hLeft e)
  have hELeftFixed :
      GroundStateSourceFixedPairEnergy.allRightLeftRetainedCondExpL2
          H N hN beta hbeta (E z) = E z :=
    (GroundStateSourceFixedPairEnergy.allRightLink_fixed_iff_leftRetained
      H N hN beta hbeta (E z)).1 hERight
  have hELeft :
      E z ∈ lpMeas ℝ ℝ LeftSigma 2 μJ := by
    exact
      (GroundStateSourceFixedPairEnergy.allRightLeftRetained_fixed_iff_mem
        H N hN beta hbeta (E z)).1 hELeftFixed
  have hfstJoint :
      AEStronglyMeasurable[LeftSigma]
        (z : X × X → ℝ) μJ :=
    mem_lpMeas_iff_aestronglyMeasurable.mp hzLeft
  have hEfstJoint :
      AEStronglyMeasurable[LeftSigma]
        (E z : X × X → ℝ) μJ :=
    mem_lpMeas_iff_aestronglyMeasurable.mp hELeft
  have hfstPair :
      AEStronglyMeasurable[LeftSigma]
        (z : X × X → ℝ) μPair :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
      H N hN beta hbeta LeftSigma (z : X × X → ℝ)).1 hfstJoint
  have hEfstPair :
      AEStronglyMeasurable[LeftSigma]
        (E z : X × X → ℝ) μPair :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
      H N hN beta hbeta LeftSigma (E z : X × X → ℝ)).1 hEfstJoint
  let hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  have hEcoeJoint :
      (fun p : X × X => E z p) =ᵐ[μJ]
        (fun p => z p.swap) := by
    change
      (MeasureTheory.Lp.compMeasurePreserving Prod.swap hs z) =ᵐ[μJ]
        (fun p => z p.swap)
    simpa [Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving z hs)
  have hEcoePair :
      (fun p : X × X => E z p) =ᵐ[μPair]
        (fun p => z p.swap) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_ae_eq_iff_pairHaar
      H N hN beta hbeta
      (fun p : X × X => E z p)
      (fun p => z p.swap)).1 hEcoeJoint
  have hSwapFstPair :
      AEStronglyMeasurable[LeftSigma]
        (fun p : X × X => z p.swap) μPair :=
    hEfstPair.congr hEcoePair
  have hsndPair :
      AEStronglyMeasurable[RightSigma]
        (z : X × X → ℝ) μPair := by
    simpa [LeftSigma, RightSigma, μPair] using
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_aestronglyMeasurable_snd_of_swap_fst
        H N (z : X × X → ℝ) hSwapFstPair
  obtain ⟨c, hcPair⟩ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_ae_eq_const_of_fst_snd_aestronglyMeasurable
      H N
      (z : X × X → ℝ)
      hfstPair hsndPair
  have hcJoint :
      (z : X × X → ℝ) =ᵐ[μJ] fun _ => c :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_ae_eq_iff_pairHaar
      H N hN beta hbeta
      (z : X × X → ℝ) (fun _ => c)).2 hcPair
  have hZero :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          H N hN beta hbeta z = 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_ae_const
      H N hN beta hbeta z).2 ⟨c, hcJoint⟩
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
      H N hN beta hbeta z).1 hZero

/-- Every vector in the intrinsic joint constant line is fixed by each genuine
right or left one-link conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_fixed_of_mem_constantLine
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hz :
      z ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta e z = z := by
  change z ∈
    (ℝ ∙
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
        H N hN beta hbeta 1) at hz
  rcases Submodule.mem_span_singleton.mp hz with ⟨c, hc⟩
  have hzConst :
      z =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
          H N hN beta hbeta c := by
    calc
      z = c •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
            H N hN beta hbeta 1 := hc.symm
      _ =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
            H N hN beta hbeta c := by
        symm
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2_eq_smul_one
            H N hN beta hbeta c
  subst z
  cases e with
  | inl e =>
      apply
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_fixed_iff_mem_lpMeas
          H N hN beta hbeta e _).2
      apply mem_lpMeas_iff_aestronglyMeasurable.mpr
      exact
        aestronglyMeasurable_const.congr
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2_coeFn
            H N hN beta hbeta c).symm
  | inr e =>
      apply
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_fixed_iff_mem_lpMeas
          H N hN beta hbeta e _).2
      apply mem_lpMeas_iff_aestronglyMeasurable.mpr
      exact
        aestronglyMeasurable_const.congr
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2_coeFn
            H N hN beta hbeta c).symm

/-- Exact common-fixed geometry of all tagged one-link projections. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_all_fixed_iff_mem_constantLine
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta e z = z) ↔
      z ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
          H N hN beta hbeta := by
  constructor
  · intro h
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_all_fixed_mem_constantLine
        H N hN beta hbeta z h
  · intro hz e
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_fixed_of_mem_constantLine
        H N hN beta hbeta e z hz

/-- The complete canonical tagged one-link sweep has exactly the intrinsic
constant line as fixed space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweep_fixed_iff_mem_constantLine
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
        H N hN beta hbeta z = z ↔
      z ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
          H N hN beta hbeta := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let sources :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
  change realHilbertProjectionSweep P sources z = z ↔ _
  rw [
    realHilbertProjectionSweep_apply_eq_self_iff_forall_mem_fixed
      P
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta)
      sources z]
  have hAll :
      (∀ e ∈ sources, P e z = z) ↔
        ∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          P e z = z := by
    simp [sources]
  rw [hAll]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_all_fixed_iff_mem_constantLine
      H N hN beta hbeta z

/-- Orthogonal projection onto the intrinsic joint constant line. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta).starProjection

/-- The constant-line projection absorbs each genuine tagged one-link update. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedSpatialLink
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta e z) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta z := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  let B : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
    C.starProjection
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta e
  change B (P z) = B z
  apply ext_inner_right ℝ
  intro g
  have hFixed :
      P (B g) = B g := by
    apply
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_fixed_of_mem_constantLine
        H N hN beta hbeta e (B g)
    exact C.starProjection_apply_mem g
  calc
    inner ℝ (B (P z)) g =
        inner ℝ (P z) (B g) :=
      Submodule.inner_starProjection_left_eq_right C (P z) g
    _ = inner ℝ z (P (B g)) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e z (B g)
    _ = inner ℝ z (B g) := by rw [hFixed]
    _ = inner ℝ (B z) g :=
      (Submodule.inner_starProjection_left_eq_right C z g).symm

/-- The constant-line projection absorbs the complete canonical tagged one-link
sweep. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedFullSweep
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
          H N hN beta hbeta z) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta z := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let sources :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  change B (realHilbertProjectionSweep P sources z) = B z
  exact
    realHilbertNestedBlock_projectionSweep_absorb
      B P sources
      (fun e _ y =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedSpatialLink
          H N hN beta hbeta e y)
      z

/-- Under the strict #4969 small-coupling regime, the actual complete
two-sided one-link sweep converges on every joint L2 vector to the orthogonal
projection onto the intrinsic constant line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_iterates_tendsto_constantProjection
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let sources :=
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
    let S := realHilbertProjectionSweep P sources
    let B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
    Tendsto (fun n : ℕ => S^[n] z) atTop (𝓝 (B z)) := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let sources :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
  let S := realHilbertProjectionSweep P sources
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  have hEta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio_nonneg_lt_one
      s hs beta hbeta hcut
  have hAbsorb : ∀ y, B (S y) = B y := by
    intro y
    simpa [P, sources, S, B,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedFullSweep
        H N hN beta hbeta y
  have hFixed : ∀ y, S y = y → B y = y := by
    intro y hy
    apply
      (Submodule.starProjection_eq_self_iff).2
    apply
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweep_fixed_iff_mem_constantLine
        H N hN beta hbeta y).1
    simpa [P, sources, S,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector] using hy
  have hDecay : ∀ n : ℕ,
      realHilbertProjectionSweepPathLoss P sources (S^[n] z) ≤
        eta ^ n * realHilbertProjectionSweepPathLoss P sources z := by
    intro n
    simpa [P, sources, S, eta] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_iteratedPathLoss_le_geometric
        H N hN s hs beta hbeta hcut z n
  exact
    realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
      P sources B eta hEta.1 hEta.2
      hAbsorb hFixed z hDecay

end

end MathlibAnalytic
end MGAP4D

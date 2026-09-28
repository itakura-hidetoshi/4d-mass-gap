import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateOneLinkPairHaarCommutation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarPiAEFiniteIntersectionTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarCommonFixedBoundary
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarRayleighConstant
import Mathlib.Tactic

/-!
# Beta-zero same-color one-link sweep equals the color block

For one fixed six-spatial color at beta zero, every one-link conditional
expectation is a literal product-Haar coordinate projection.  PR #4887 proves
that these projections commute pairwise.  PRs #4885 and #4886 identify the
intersection of their retained coordinate supports with the retained support of
the corresponding spatial-color block.

Hence the complete ordered same-color one-link sweep and the pair-Haar
spatial-color conditional expectation are the same orthogonal projection.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 2000000

local instance betaZeroSameColorSweepEqBlockTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroSameColorSweepEqBlockCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroSameColorSweepEqBlockSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroSameColorSweepEqBlockMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroSameColorSweepEqBlockBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroSameColorSweepEqBlockSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every one of the six spatial color classes contains at least one
spatial-slice link. -/
theorem periodicHypercubicEvenFixedSpatialColorLink_nonempty
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    Nonempty (PeriodicHypercubicEvenFixedSpatialColorLink H color) := by
  let v0 : PeriodicHypercubicEvenSpatialSliceVertex H :=
    ⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩
  have hv0 :
      periodicHypercubicEvenCheckerboardParity H v0.1 = 0 := by
    simp [v0, periodicHypercubicEvenCheckerboardParity,
      periodicHypercubicEvenCoordinateParity, periodicHypercubicEvenParityHom]
  by_cases hp : color.2 = 0
  · refine ⟨⟨(v0, color.1), ?_⟩⟩
    apply Prod.ext
    · rfl
    · exact hv0.trans hp.symm
  · let v1 :=
      periodicHypercubicEvenSpatialSliceShift H v0 color.1
    have hv1 :
        periodicHypercubicEvenCheckerboardParity H v1.1 = 1 := by
      change
        periodicHypercubicEvenCheckerboardParity H
            (periodicHypercubicShift
              (PeriodicHypercubicEvenSideLength H) v0.1 color.1.1) = 1
      rw [periodicHypercubicEvenCheckerboardParity_shift, hv0]
      norm_num
    have hpval : color.2.val = 1 := by
      have hlt : color.2.val < 2 := ZMod.val_lt color.2
      have hne : color.2.val ≠ 0 := by
        intro hzero
        apply hp
        exact (ZMod.val_eq_zero color.2).mp hzero
      omega
    have hp1 : color.2 = 1 := by
      calc
        color.2 = (color.2.val : ZMod 2) :=
          (ZMod.natCast_zmod_val color.2).symm
        _ = 1 := by
          simp [hpval]
    refine ⟨⟨(v1, color.1), ?_⟩⟩
    apply Prod.ext
    · rfl
    · exact hv1.trans hp1.symm

/-- The complete canonical list of links in one fixed spatial color is
nonempty. -/
theorem periodicHypercubicEvenFixedSpatialColorLink_univ_toList_ne_nil
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList) ≠ [] := by
  rcases periodicHypercubicEvenFixedSpatialColorLink_nonempty H color with ⟨e⟩
  intro hnil
  have he :
      e ∈ ((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList) := by
    simp
  rw [hnil] at he
  simpa using he

/-- On literal pair Haar, simultaneous fixedness under all one-link
projections in one spatial color is exactly membership in the corresponding
color-retained L2 subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaar_commonFixed_iff_mem_colorLpMeas
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    (∀ e : PeriodicHypercubicEvenFixedSpatialColorLink H color,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
        H N color e x = x) ↔
      x ∈ lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color)
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  classical
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let I := PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let η : Measure G := normalizedCompactHaar G
  let ω := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N
  let cs :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
  let p :
      PeriodicHypercubicEvenFixedSpatialColorLink H color → I → Prop :=
    fun e i =>
      i ∈ periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet
        H e.1
  constructor
  · intro hfixed
    have he :
        MeasurePreserving E ω (Measure.pi (fun _ : I => η)) := by
      simpa [E, I, G, η, ω] using
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
          H N
    have hcs : cs ≠ [] := by
      simpa [cs] using
        periodicHypercubicEvenFixedSpatialColorLink_univ_toList_ne_nil H color
    have hEach :
        ∀ e ∈ cs,
          PairHaarSupportAEStronglyMeasurable
            ω E (p e) (x : X × X → ℝ) := by
      intro e _he
      have hfix :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
              H N e.1 x = x := by
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection] using
          hfixed e
      have hmem :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_fixed_iff_mem_lpMeas
          H N e.1 x).1 hfix
      have hmeas :=
        mem_lpMeas_iff_aestronglyMeasurable.mp hmem
      rw [
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_retainedCoordinateRestriction,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction_eq_piRestriction_comp]
        at hmeas
      simpa [PairHaarSupportAEStronglyMeasurable, X, I, G, ω, E, p] using
        hmeas
    have hall :=
      aestronglyMeasurable_piRestriction_iInter_list_of_measurePreserving_equiv
        ω η E he p cs hcs (x : X × X → ℝ) hEach
    have hpred :
        (fun i : I => ∀ e ∈ cs, p e i) =
          (fun i : I =>
            i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
              H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color)) := by
      simpa [I, p, cs] using
        periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet_fixedColor_univList
          H color
    have hall' :
        PairHaarSupportAEStronglyMeasurable
          ω E
          (fun i : I =>
            i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
              H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color))
          (x : X × X → ℝ) := by
      rw [← hpred]
      exact hall
    have hcolorSpace :
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N color =
          MeasurableSpace.comap
            ((pairHaarPiRestriction (K := G)
              (fun i : I =>
                i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
                  H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color))) ∘ E)
            (inferInstance : MeasurableSpace
              ({i : I //
                i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
                  H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color)} → G)) := by
      have h :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedCoordinateRestriction
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin color)
      rw [
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_piRestriction_comp]
        at h
      simpa [E, I, G] using h
    rw [mem_lpMeas_iff_aestronglyMeasurable, hcolorSpace]
    simpa [PairHaarSupportAEStronglyMeasurable, X, I, G, ω, E] using hall'
  · intro hcolor
    intro e
    apply
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_fixed_iff_mem_lpMeas
        H N e.1 x).2
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hcolor ⊢
    exact hcolor.mono <| by
      simpa [e.2] using
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le_spatialLink
          H N e.1

/-- The complete literal pair-Haar same-color one-link sweep fixes exactly the
vectors fixed by the corresponding pair-Haar spatial-color block. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarFullSweep_fixed_iff_color_fixed
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
          H N color)
        ((Finset.univ :
          Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
        x = x ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
        H N color x = x := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
      H N color
  let cs :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
  rw [
    realHilbertProjectionSweep_apply_eq_self_iff_forall_mem_fixed
      P
      (fun e => by
        simpa [P,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_idempotent
            H N e.1)
      (fun e a b =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_symmetric
          H N e.1 a b)
      cs x]
  have hcommon :
      (∀ e ∈ cs, P e x = x) ↔
        ∀ e : PeriodicHypercubicEvenFixedSpatialColorLink H color, P e x = x := by
    simp [cs]
  rw [hcommon]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaar_commonFixed_iff_mem_colorLpMeas]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_fixed_iff_mem_lpMeas
      H N color x).symm

/-- The complete literal pair-Haar same-color one-link sweep is exactly the
pair-Haar spatial-color block projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarFullSweep_eq_colorProjection
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
          H N color)
        ((Finset.univ :
          Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
        H N color := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
      H N color
  let cs :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
  let S := realHilbertProjectionSweep P cs
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
      H N color
  have hPid : ∀ e, (P e).comp (P e) = P e := by
    intro e
    simpa [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_idempotent
        H N e.1
  have hPsymm : ∀ e a b, inner ℝ (P e a) b = inner ℝ a (P e b) := by
    intro e a b
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_symmetric
        H N e.1 a b
  have hComm : ∀ e d a, P e (P d a) = P d (P e a) := by
    intro e d a
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection_commute
        H N color e d a
  have hSid :
      S.comp S = S := by
    simpa [S] using
      realHilbertProjectionSweep_idempotent_of_pairwise_commute
        P hPid hComm cs
  have hSsymm :
      ∀ a b, inner ℝ (S a) b = inner ℝ a (S b) := by
    intro a b
    simpa [S] using
      realHilbertProjectionSweep_symmetric_of_pairwise_commute
        P hPsymm hComm cs a b
  have hBid : B.comp B = B := by
    simpa [B] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_idempotent
        H N color
  have hBsymm :
      ∀ a b, inner ℝ (B a) b = inner ℝ a (B b) := by
    intro a b
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_symmetric
        H N color a b
  have hFixed : ∀ a, S a = a ↔ B a = a := by
    intro a
    simpa [S, P, cs, B] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarFullSweep_fixed_iff_color_fixed
        H N color a
  have hRange : S.range = B.range := by
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨a, rfl⟩
      have hSfix : S (S a) = S a := by
        have h := congrArg
          (fun T :
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N =>
            T a) hSid
        simpa only [ContinuousLinearMap.comp_apply] using h
      have hBfix := (hFixed (S a)).1 hSfix
      exact ⟨S a, hBfix⟩
    · intro y hy
      rcases hy with ⟨a, rfl⟩
      have hBfix : B (B a) = B a := by
        have h := congrArg
          (fun T :
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N =>
            T a) hBid
        simpa only [ContinuousLinearMap.comp_apply] using h
      have hSfix := (hFixed (B a)).2 hBfix
      exact ⟨B a, hSfix⟩
  have hSSelf : IsSelfAdjoint S := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact hSsymm
  have hBSelf : IsSelfAdjoint B := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact hBsymm
  have hSIdemElem : IsIdempotentElem S := by
    change S * S = S
    apply ContinuousLinearMap.ext
    intro a
    have h := congrArg
      (fun T :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N =>
        T a) hSid
    simpa using h
  have hBIdemElem : IsIdempotentElem B := by
    change B * B = B
    apply ContinuousLinearMap.ext
    intro a
    have h := congrArg
      (fun T :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N =>
        T a) hBid
    simpa using h
  have hSStar : IsStarProjection S := ⟨hSIdemElem, hSSelf⟩
  have hBStar : IsStarProjection B := ⟨hBIdemElem, hBSelf⟩
  have hSB : S = B :=
    (ContinuousLinearMap.IsStarProjection.ext_iff hSStar hBStar).2 hRange
  simpa [S, P, cs, B] using hSB

end

end MGAP4D.MathlibAnalytic

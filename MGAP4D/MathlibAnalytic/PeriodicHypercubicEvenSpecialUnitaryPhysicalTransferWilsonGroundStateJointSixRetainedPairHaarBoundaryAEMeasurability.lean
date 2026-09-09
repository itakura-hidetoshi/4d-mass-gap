import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarPiAEIntersectionTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarAEMeasurability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointLeftRetainedSigmaCoordinateBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointRightRetainedSigmaCoordinateBridge
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance groundStateSixRetainedBoundaryAETopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateSixRetainedBoundaryAECompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateSixRetainedBoundaryAESecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateSixRetainedBoundaryAEMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateSixRetainedBoundaryAEBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateSixRetainedBoundaryAESpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal joint spatial-coordinate equivalence sends the actual product
Haar law exactly to the finite product Haar law on the disjoint-union carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) := by
  change MeasurePreserving
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H =>
        Matrix.specialUnitaryGroup (Fin N) ℂ)).symm
    ((Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))).prod
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))))
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
  exact
    MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
      (fun _ : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- The actual right-retained coordinate map is literally restriction of the
unified coordinate presentation to the right-retained support. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_piRestriction_comp
    (H N : ℕ)
    (c : Fin 6) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
        H N c =
      (pairHaarPiRestriction (K := Matrix.specialUnitaryGroup (Fin N) ℂ)
        (fun i => i ∈
          periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c)) ∘
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N := by
  rfl

/-- Left-retained counterpart of the literal restriction identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction_eq_piRestriction_comp
    (H N : ℕ)
    (c : Fin 6) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
        H N c =
      (pairHaarPiRestriction (K := Matrix.specialUnitaryGroup (Fin N) ℂ)
        (fun i => i ∈
          periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)) ∘
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N := by
  rfl

/-- Membership in the actual right-six retained `L²` intersection forces the
same represented function to be pair-Haar a.e. strongly measurable with
respect to the complete left-boundary sigma-algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetained_pairHaar_aestronglyMeasurable_fst
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hz : z ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
        H N hN beta hbeta) :
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
      (z :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  classical
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let I := PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let η : Measure G := normalizedCompactHaar G
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N
  have he :
      MeasurePreserving E
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (Measure.pi (fun _ : I => η)) := by
    simpa [E, I, G, η] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
        H N
  have hcolors : ∀ c : Fin 6,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G)
            (fun i : I => i ∈
              periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c)) ∘ E)
          (inferInstance : MeasurableSpace
            ({i : I // i ∈
              periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c} → G))]
        (z : X × X → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    intro c
    have hc :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetained_pairHaar_aestronglyMeasurable
        H N hN beta hbeta z hz c
    rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedCoordinateRestriction]
      at hc
    rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_piRestriction_comp]
      at hc
    simpa [X, I, G, E] using hc
  have hall :=
    aestronglyMeasurable_piRestriction_iInter_finSix_of_measurePreserving_equiv
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      η E he
      (fun c i => i ∈
        periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c)
      (z : X × X → ℝ) hcolors
  have hpred :
      (fun i : I => ∀ c : Fin 6,
        i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c) =
      (fun i : I => i ∈
        periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H) := by
    funext i
    apply propext
    constructor
    · intro hi
      have hi' :
          i ∈ ⋂ c : Fin 6,
            periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c := by
        simpa only [Set.mem_iInter] using hi
      rw [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet_iInter_eq_leftBoundary H]
        at hi'
      exact hi'
    · intro hi
      have hi' :
          i ∈ ⋂ c : Fin 6,
            periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c := by
        rw [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet_iInter_eq_leftBoundary H]
        exact hi
      simpa only [Set.mem_iInter] using hi'
  rw [hpred] at hall
  have hboundaryMeasurable :
      Measurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace X)]
        ((pairHaarPiRestriction (K := G)
          (fun i : I => i ∈
            periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H)) ∘ E) := by
    letI : MeasurableSpace (X × X) :=
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace X)
    change Measurable
      ((pairHaarPiRestriction (K := G)
        (fun i : I => i ∈
          periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H)) ∘ E)
    rw [measurable_pi_iff]
    intro i
    rcases i with ⟨i, hi⟩
    cases i with
    | inl e =>
        have heq :
            (fun x : X × X =>
              ((pairHaarPiRestriction (K := G)
                (fun i : I => i ∈
                  periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H)) ∘ E)
                x ⟨Sum.inl e, hi⟩) =
              (fun x : X × X => x.1 e) := by
          funext x
          rfl
        rw [heq]
        exact
          (measurable_pi_apply e).comp
            (measurable_iff_comap_le.mpr le_rfl)
    | inr e =>
        change False at hi
        contradiction
  exact hall.mono (measurable_iff_comap_le.mp hboundaryMeasurable)

/-- Left/right symmetric result: actual left-six retained membership forces
pair-Haar a.e. strong measurability with respect to the complete right boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetained_pairHaar_aestronglyMeasurable_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hz : z ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
        H N hN beta hbeta) :
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.snd
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
      (z :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  classical
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let I := PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let η : Measure G := normalizedCompactHaar G
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N
  have he :
      MeasurePreserving E
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (Measure.pi (fun _ : I => η)) := by
    simpa [E, I, G, η] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
        H N
  have hcolors : ∀ c : Fin 6,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G)
            (fun i : I => i ∈
              periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)) ∘ E)
          (inferInstance : MeasurableSpace
            ({i : I // i ∈
              periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c} → G))]
        (z : X × X → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    intro c
    have hc :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetained_pairHaar_aestronglyMeasurable
        H N hN beta hbeta z hz c
    rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_eq_comap_leftRetainedCoordinateRestriction]
      at hc
    rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction_eq_piRestriction_comp]
      at hc
    simpa [X, I, G, E] using hc
  have hall :=
    aestronglyMeasurable_piRestriction_iInter_finSix_of_measurePreserving_equiv
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      η E he
      (fun c i => i ∈
        periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)
      (z : X × X → ℝ) hcolors
  have hpred :
      (fun i : I => ∀ c : Fin 6,
        i ∈ periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c) =
      (fun i : I => i ∈
        periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet H) := by
    funext i
    apply propext
    constructor
    · intro hi
      have hi' :
          i ∈ ⋂ c : Fin 6,
            periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c := by
        simpa only [Set.mem_iInter] using hi
      rw [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet_iInter_eq_rightBoundary H]
        at hi'
      exact hi'
    · intro hi
      have hi' :
          i ∈ ⋂ c : Fin 6,
            periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c := by
        rw [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet_iInter_eq_rightBoundary H]
        exact hi
      simpa only [Set.mem_iInter] using hi'
  rw [hpred] at hall
  have hboundaryMeasurable :
      Measurable[
        MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace X)]
        ((pairHaarPiRestriction (K := G)
          (fun i : I => i ∈
            periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet H)) ∘ E) := by
    letI : MeasurableSpace (X × X) :=
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace X)
    change Measurable
      ((pairHaarPiRestriction (K := G)
        (fun i : I => i ∈
          periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet H)) ∘ E)
    rw [measurable_pi_iff]
    intro i
    rcases i with ⟨i, hi⟩
    cases i with
    | inl e =>
        change False at hi
        contradiction
    | inr e =>
        have heq :
            (fun x : X × X =>
              ((pairHaarPiRestriction (K := G)
                (fun i : I => i ∈
                  periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet H)) ∘ E)
                x ⟨Sum.inr e, hi⟩) =
              (fun x : X × X => x.2 e) := by
          funext x
          rfl
        rw [heq]
        exact
          (measurable_pi_apply e).comp
            (measurable_iff_comap_le.mpr le_rfl)
  exact hall.mono (measurable_iff_comap_le.mp hboundaryMeasurable)

end

end MathlibAnalytic
end MGAP4D
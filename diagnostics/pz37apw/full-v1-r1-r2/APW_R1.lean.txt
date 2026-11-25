import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicOriginalOSCanonicalVacuumCenteredRealizationV5_PZ37APV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APW — literal time-one open-half factorization
At positive extent the time-one spatial slice belongs to the strict
open half. At zero extent it belongs to the antipodal fixed boundary.
Use the actual unchanged interior coordinate map to construct a bounded
continuous original insertion. Its actual Wilson synthesis is precisely
APP's boundary moment. Open-half L2 approximation by actual canonical
observables suffices for APV's unique nonzero centered realization.
No assertion that the required approximation or time evolution holds.
-/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "B" => PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
local notation "O" => PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "E" => periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
local notation "j1" => p4Q2PZ37AMX_positiveTimeOne
local notation "Fcl" => p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
local notation "M" => p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
local notation "X" => p4Q2PZ37APP_originalTimeOneBoundaryMomentL2
local notation "U" => p4Q2PZ37APP_originalTimeOneOSCenteredBoundaryL2
local notation "Mode" => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy

local instance p4Q2PZ37APW_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APW_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APW_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APW_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APW_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APW_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APW_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APW_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37APW_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance


def p4Q2PZ37APW_openTimeOneSlice
    (H : ℕ) (hH : 0 < H) (x : O H 2) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  fun e => x (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
    (Sum.inl (⟨0, hH⟩, e)))

local notation "Slice" => p4Q2PZ37APW_openTimeOneSlice

theorem p4Q2PZ37APW_closureTimeOneSlice_eq_open
    (H : ℕ) (hH : 0 < H) (b : B H 2) (x : O H 2) :
    (E H 2 (b, x)).1 (j1 H) = Slice H hH x := by
  let k : Fin H := ⟨0, hH⟩
  have hj : j1 H = k.succ.castSucc := by
    apply Fin.ext
    rfl
  funext e
  rw [hj, periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_interior_apply]
  rfl

theorem p4Q2PZ37APW_zeroExtentTimeOneSlice_eq_antipodal
    (H : ℕ) (hH : H = 0) (b : B H 2) (x : O H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (E H 2 (b, x)).1 (j1 H) e =
      b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
        (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)) := by
  have hj : j1 H = (Fin.last H).succ := by
    apply Fin.ext
    simp [p4Q2PZ37AMX_positiveTimeOne, hH]
  rw [hj, periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_apply]

/-- Actual bounded continuous two-mode observable on the strict open half. -/
noncomputable def p4Q2PZ37APW_openTimeOneObservable
    (H : ℕ) (hH : 0 < H) (c0 c1 : ℝ) :
    BoundedContinuousFunction (O H 2) ℝ := by
  let a : O H 2 → G := fun x => Hol H 2 (Slice H hH x)
  have ha : Continuous a := by
    dsimp only [a, p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy,
      haarFinFourCyclicPlaquetteWord]
    simp only [haarFinFourCyclicNestedCoordinates_apply, haarCyclicPlaquetteWord,
      p4Q2PZ37APW_openTimeOneSlice]
    fun_prop
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => c0 * Mode 0 (a x) + c1 * Mode 1 (a x),
      (continuous_const.mul ((Mode 0).continuous.comp ha)).add
        (continuous_const.mul ((Mode 1).continuous.comp ha))⟩

local notation "W" => p4Q2PZ37APW_openTimeOneObservable

theorem p4Q2PZ37APW_closureTimeOneObservable_eq_open
    (H : ℕ) (hH : 0 < H) (c0 c1 : ℝ) (b : B H 2) (x : O H 2) :
    Fcl H c0 c1 (b, x) = W H hH c0 c1 x := by
  unfold p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
    p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable
    p4Q2PZ37ANA_timeOneTwoModeWilsonObservable
  rw [p4Q2PZ37APW_closureTimeOneSlice_eq_open H hH b x]
  rfl

theorem p4Q2PZ37APW_originalTimeOneBoundaryGramMoment_eq_openMoment
    (H : ℕ) (hH : 0 < H) [Nontrivial G] (beta : ℝ)
    (hb : 0 ≤ beta) (c0 c1 : ℝ) (b : B H 2) :
    M H beta hb c0 c1 b =
      periodicHypercubicEvenBoundaryObservableMoment
        H 2 (by norm_num) beta hb (W H hH c0 c1) b := by
  have hf : (fun x : O H 2 => Fcl H c0 c1 (b, x)) =
      (fun x : O H 2 => W H hH c0 c1 x) :=
    funext (p4Q2PZ37APW_closureTimeOneObservable_eq_open H hH c0 c1 b)
  unfold p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
    periodicHypercubicEvenBoundaryObservableMoment
  rw [hf]

theorem p4Q2PZ37APW_originalTimeOneBoundaryMomentL2_eq_openSynthesis
    (H : ℕ) (hH : 0 < H) [Nontrivial G] (beta : ℝ)
    (hb : 0 ≤ beta) (c0 c1 : ℝ) :
    X H beta hb c0 c1 =
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H 2 (by norm_num) beta hb
        (periodicHypercubicEvenWilsonOpenHalfObservableL2 H 2 (W H hH c0 c1)) := by
  let u := W H hH c0 c1
  calc
    X H beta hb c0 c1 =
        periodicHypercubicEvenBoundaryObservableMomentL2
          H 2 (by norm_num) beta hb u := by
      apply Lp.ext
      filter_upwards [p4Q2PZ37APP_originalTimeOneBoundaryMomentL2_coeFn
        H beta hb c0 c1,
        periodicHypercubicEvenBoundaryObservableMomentL2_coeFn
          H 2 (by norm_num) beta hb u] with b hx hy
      exact hx.trans ((p4Q2PZ37APW_originalTimeOneBoundaryGramMoment_eq_openMoment H hH beta hb c0 c1 b).trans hy.symm)
    _ = _ := periodicHypercubicEvenBoundaryObservableMomentL2_eq_synthesisOperator
      H 2 (by norm_num) beta hb u

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ} {hN : 0 < (2 : ℕ)}
    [Nontrivial G] {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent 2 hN beta hbeta)

theorem p4Q2PZ37APW_modeOneRealization_of_openHalfL2Closure
    (n : ℕ) (hH : 0 < halfExtent n)
    (hx : periodicHypercubicEvenWilsonOpenHalfObservableL2 (halfExtent n) 2
      (W (halfExtent n) hH 0 1) ∈
      closure (Set.range (fun F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).Carrier =>
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n F))) :
    ∃ x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert, R.toCompletedBoundaryMomentLinearIsometryAutomatic n x = X (halfExtent n) (beta n) (hbeta n) 0 1 := by
  let Pn := (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n)
  let J := R.toCompletedBoundaryMomentLinearIsometryAutomatic n
  let D := physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
    halfExtent 2 hN beta hbeta n
  let A := fun F : Pn.Carrier =>
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n F
  have hsub : Set.range A ⊆ D ⁻¹' Set.range J := by
    rintro y ⟨F, rfl⟩
    refine ⟨Pn.physicalState F, ?_⟩
    calc
      J (Pn.physicalState F) = physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n F :=
        R.toCompletedBoundaryMomentLinearIsometryAutomatic_physicalState n F
      _ = D (A F) :=
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
          S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n F
  have hclosed : IsClosed (D ⁻¹' Set.range J) :=
    (R.isClosed_range_toCompletedBoundaryMomentLinearIsometryAutomatic n).preimage D.continuous
  have hmem : periodicHypercubicEvenWilsonOpenHalfObservableL2 (halfExtent n) 2
      (W (halfExtent n) hH 0 1) ∈ D ⁻¹' Set.range J :=
    (closure_minimal hsub hclosed) hx
  obtain ⟨x, hix⟩ := hmem
  exact ⟨x, hix.trans ((p4Q2PZ37APW_originalTimeOneBoundaryMomentL2_eq_openSynthesis (halfExtent n) hH
    (beta n) (hbeta n) 0 1).symm)⟩

theorem p4Q2PZ37APW_centeredRealization_unique_of_openHalfL2Closure
    (n : ℕ) (hH : 0 < halfExtent n) (hb : 0 < beta n)
    (hx : periodicHypercubicEvenWilsonOpenHalfObservableL2 (halfExtent n) 2
      (W (halfExtent n) hH 0 1) ∈
      closure (Set.range (fun F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).Carrier =>
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n F))) :
    ∃! x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert,
      R.toCompletedBoundaryMomentLinearIsometryAutomatic n x = U (halfExtent n) (beta n) (hbeta n) ∧ inner ℝ (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).vacuum x = 0 ∧ x ≠ 0 := by
  obtain ⟨x, hix⟩ := (p4Q2PZ37APV_centeredRealization_iff_modeOneRealization R n).2
    (p4Q2PZ37APW_modeOneRealization_of_openHalfL2Closure R n hH hx)
  refine ⟨x, ⟨hix, p4Q2PZ37APV_centeredRealization_orthogonal_nonzero R n hb x hix⟩, ?_⟩
  intro y hy
  exact (R.toCompletedBoundaryMomentLinearIsometryAutomatic n).injective (hy.1.trans hix.symm)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_openTimeOneSlice
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_closureTimeOneSlice_eq_open
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_zeroExtentTimeOneSlice_eq_antipodal
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_openTimeOneObservable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_closureTimeOneObservable_eq_open
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_originalTimeOneBoundaryGramMoment_eq_openMoment
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_originalTimeOneBoundaryMomentL2_eq_openSynthesis
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_modeOneRealization_of_openHalfL2Closure
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APW_centeredRealization_unique_of_openHalfL2Closure

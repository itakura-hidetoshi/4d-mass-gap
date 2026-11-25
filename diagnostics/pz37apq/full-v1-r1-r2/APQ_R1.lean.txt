import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicOriginalTimeOneOSCenteredBoundaryL2V5_PZ37APP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APQ — original centered boundary Gram vector, native transfer readout

Candidate: combine APP's exact L² representative with APN's boundary-only
Fubini theorem and APM's true gauge-reduced closure insertion. Read out the
same centered vector against arbitrary physical Gauss-law endpoint states.
The resulting pairing is precisely the physical one-slab insertion
T^H M_a T, times the original partition square-root normalization.
No new semigroup assumption, carrier equality, top alignment or gap claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Slab" => periodicHypercubicEvenPositiveHalfCylinderSlabCount
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "P" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "B" => PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
local notation "BM" => periodicHypercubicEvenBoundaryHaarMeasure
local notation "L" => PeriodicHypercubicEvenBoundaryHaarL2
local notation "Closure" => PeriodicHypercubicEvenPositiveHalfClosureConfiguration
local notation "CM" => periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure
local notation "E" => periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
local notation "Gram" => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
local notation "M" => p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
local notation "Obs" => p4Q2PZ37APL_originalTwoModeObservable
local notation "X" => p4Q2PZ37APP_originalTimeOneBoundaryMomentL2
local notation "U" => p4Q2PZ37APP_originalTimeOneOSCenteredBoundaryL2
local notation "Vac" => periodicHypercubicEvenBoundaryVacuumL2
local notation "TopVac" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
local notation "NormZ" => periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
local notation "NativeAmp" => periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
local notation "Amp" => periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
local notation "Ins" => periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator

local instance p4Q2PZ37APQ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APQ_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APQ_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APQ_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩

/-- Endpoint projections retain both reflection-fixed spatial slices.
These are definitionally the private endpoint maps used in APN. -/
private def p4Q2PZ37APQ_left (H : ℕ) (b : B H 2) : Cfg H 2 :=
  fun e => b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e)

private def p4Q2PZ37APQ_right (H : ℕ) (b : B H 2) : Cfg H 2 :=
  fun e => b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
    (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e))

/-- Literal endpoint test of a boundary Haar L² vector, using the original
Gauss-law slice L² representatives. -/
noncomputable def p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing
    (H : ℕ) (v : L H 2) (f g : P H 2) : ℝ :=
  ∫ b : B H 2,
    ((f : Lp ℝ 2 (Mu H 2)) (p4Q2PZ37APQ_left H b) *
      (g : Lp ℝ 2 (Mu H 2)) (p4Q2PZ37APQ_right H b)) * v b ∂(BM H 2)

local notation "Pair" => p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing

/-- The exact APP L² class has APM's native time-one amplitude as its
endpoint test. This is not merely the older pointwise Gram formula. -/
theorem p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing_eq_nativeAmplitude
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 ≤ beta) (q : ℝ)
    (f g : P H 2) :
    Pair H (X H beta hb q 1) f g =
      NormZ H 2 (by norm_num) beta hb *
        NativeAmp H 2 beta (Slab H) (p4Q2PZ37AMX_positiveTimeOne H)
          (Obs H q) (f : Lp ℝ 2 (Mu H 2)) (g : Lp ℝ 2 (Mu H 2)) := by
  calc
    _ = ∫ b : B H 2,
        ((f : Lp ℝ 2 (Mu H 2)) (p4Q2PZ37APQ_left H b) *
          (g : Lp ℝ 2 (Mu H 2)) (p4Q2PZ37APQ_right H b)) *
          M H beta hb q 1 b ∂(BM H 2) := by
      unfold p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing
      apply integral_congr_ae
      filter_upwards
        [p4Q2PZ37APP_originalTimeOneBoundaryMomentL2_coeFn H beta hb q 1]
        with b h
      rw [h]
    _ = ∫ z : Closure H G,
        Gram H 2 (by norm_num) beta hb z.1 z.2 *
          (f : Lp ℝ 2 (Mu H 2)) ((E H 2 z).1 0) *
          (g : Lp ℝ 2 (Mu H 2)) ((E H 2 z).1 (Fin.last (Slab H))) *
          Obs H q ((E H 2 z).1 (p4Q2PZ37AMX_positiveTimeOne H))
          ∂(CM H 2) := by
      exact (p4Q2PZ37APN_originalTimeOneClosure_eq_testedBoundaryMoment
        H beta hb q f g).symm
    _ = _ :=
      p4Q2PZ37APM_originalClosureInsertedIntegral_eq_nativeAmplitude
        H beta hb (p4Q2PZ37AMX_positiveTimeOne H) (Obs H q)
        (p4Q2PZ37APL_originalTwoModeObservable_gaugeInvariant H q) f g

/-- Transport only the finite index, not the underlying physical kernel. -/
private theorem p4Q2PZ37APQ_nativeAmplitude_cast
    (H : ℕ) (beta : ℝ) {n m : ℕ} (h : n = m)
    (j : Fin (n + 1))
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H 2)
    (f g : Lp ℝ 2 (Mu H 2)) :
    NativeAmp H 2 beta n j a f g =
      NativeAmp H 2 beta m (Fin.cast (congrArg (fun k : ℕ => k + 1) h) j) a f g := by
  subst m
  rfl

/-- Matrix coefficient of the existing native physical insertion operator:
its definition is T^H M_a T. The equality is for arbitrary physical f,g. -/
theorem p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing_eq_physicalInsertion
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 ≤ beta) (q : ℝ)
    (f g : P H 2) :
    Pair H (X H beta hb q 1) f g =
      NormZ H 2 (by norm_num) beta hb *
        inner ℝ
          (Ins H 2 (by norm_num) beta hb 1 H (Obs H q)
            (p4Q2PZ37APL_originalTwoModeObservable_gaugeInvariant H q) f) g := by
  let a := Obs H q
  let j := p4Q2PZ37AMX_positiveTimeOne H
  let ha := p4Q2PZ37APL_originalTwoModeObservable_gaugeInvariant H q
  have hTotal : Slab H = 1 + H := by
    simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount, Nat.add_comm]
  have hIndex : Fin.cast (congrArg (fun k : ℕ => k + 1) hTotal) j =
      periodicHypercubicEvenSpecialUnitaryTransferSliceIndex 1 H := by
    apply Fin.ext
    rfl
  have hEq : NativeAmp H 2 beta (Slab H) j a
      (f : Lp ℝ 2 (Mu H 2)) (g : Lp ℝ 2 (Mu H 2)) =
      Amp H 2 beta 1 H a (f : Lp ℝ 2 (Mu H 2)) (g : Lp ℝ 2 (Mu H 2)) := by
    calc
      _ = NativeAmp H 2 beta (1 + H)
          (Fin.cast (congrArg (fun k : ℕ => k + 1) hTotal) j) a
          (f : Lp ℝ 2 (Mu H 2)) (g : Lp ℝ 2 (Mu H 2)) :=
        p4Q2PZ37APQ_nativeAmplitude_cast H beta hTotal j a _ _
      _ = _ := congrArg (fun k => NativeAmp H 2 beta (1 + H) k a
          (f : Lp ℝ 2 (Mu H 2)) (g : Lp ℝ 2 (Mu H 2))) hIndex
  calc
    _ = NormZ H 2 (by norm_num) beta hb *
        NativeAmp H 2 beta (Slab H) j a
          (f : Lp ℝ 2 (Mu H 2)) (g : Lp ℝ 2 (Mu H 2)) :=
      p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing_eq_nativeAmplitude
        H beta hb q f g
    _ = NormZ H 2 (by norm_num) beta hb *
        Amp H 2 beta 1 H a
          (f : Lp ℝ 2 (Mu H 2)) (g : Lp ℝ 2 (Mu H 2)) :=
      congrArg (fun s : ℝ => NormZ H 2 (by norm_num) beta hb * s) hEq
    _ = _ := congrArg (fun s : ℝ => NormZ H 2 (by norm_num) beta hb * s)
      (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator_inner_eq_amplitude
        H 2 (by norm_num) beta hb 1 H a ha f g).symm

/-- Apply the exact native readout to the actual APP vacuum-orthogonal
excitation, with its original centering coefficient. -/
theorem p4Q2PZ37APQ_originalTimeOneOSCenteredBoundaryEndpointPairing_eq_physicalInsertion
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 ≤ beta) (f g : P H 2) :
    let q := -inner ℝ (Vac H 2 (by norm_num) beta hb) (X H beta hb 0 1)
    Pair H (U H beta hb) f g =
      NormZ H 2 (by norm_num) beta hb *
        inner ℝ
          (Ins H 2 (by norm_num) beta hb 1 H (Obs H q)
            (p4Q2PZ37APL_originalTwoModeObservable_gaugeInvariant H q) f) g := by
  exact p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing_eq_physicalInsertion
    H beta hb _ f g

/-- The actual centered boundary vector has a strictly positive native
endpoint readout at every finite H and positive beta. -/
theorem p4Q2PZ37APQ_originalTimeOneOSCenteredBoundaryEndpointPairing_pos
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 < beta) :
    let q := -inner ℝ (Vac H 2 (by norm_num) beta hb.le) (X H beta hb.le 0 1)
    0 < Pair H (U H beta hb.le)
      (p4Q2PZ37APL_originalVacuumWeightedTwoMode H beta hb.le q)
      (TopVac H 2 (by norm_num) beta hb.le) := by
  let q := -inner ℝ (Vac H 2 (by norm_num) beta hb.le) (X H beta hb.le 0 1)
  let f := p4Q2PZ37APL_originalVacuumWeightedTwoMode H beta hb.le q
  let g := TopVac H 2 (by norm_num) beta hb.le
  change 0 < Pair H (X H beta hb.le q 1) f g
  rw [p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing_eq_nativeAmplitude]
  rw [← p4Q2PZ37APM_originalClosureInsertedIntegral_eq_nativeAmplitude
    H beta hb.le (p4Q2PZ37AMX_positiveTimeOne H) (Obs H q)
    (p4Q2PZ37APL_originalTwoModeObservable_gaugeInvariant H q) f g]
  exact p4Q2PZ37APM_originalTimeOneClosurePairing_pos H beta hb q

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing_eq_nativeAmplitude
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APQ_originalTimeOneBoundaryEndpointPairing_eq_physicalInsertion
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APQ_originalTimeOneOSCenteredBoundaryEndpointPairing_eq_physicalInsertion
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APQ_originalTimeOneOSCenteredBoundaryEndpointPairing_pos

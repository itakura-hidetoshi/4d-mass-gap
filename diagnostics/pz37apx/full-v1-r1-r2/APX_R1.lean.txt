import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicOriginalTimeOneOpenHalfRealizationV5_PZ37APW
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfTemporalStep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryTemporalHalfSectorGeometry
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APX — finite periodic half-turn support obstruction
A half-period temporal translation moves every strictly positive spatial edge
and every positive temporal edge into the negative edge sector. Hence canonical
positive-half sections, translated back by a half-period, have identical
positive restrictions. If the existing all-nonnegative-integer temporal
covariance package preserves the same positive-time algebra, every canonical
finite positive-half pullback is pointwise constant.
This is an obstruction within that package, not an assertion that its hypotheses
hold for the physical continuum model, nor a no-go theorem for Yang–Mills.
-/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "O" => PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "P" => periodicHypercubicEvenEdgeOrbitPartition
local notation "Section" => periodicHypercubicEvenSpecialUnitaryPositiveHalfSection
local notation "Tau" => periodicHypercubicIntegerTemporalConfigurationTranslation
local notation "L" => PeriodicHypercubicEvenSideLength

local instance p4Q2PZ37APX_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APX_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APX_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APX_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APX_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APX_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APX_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APX_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37APX_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A positive edge and its half-period translate belong to opposite sectors. -/
theorem p4Q2PZ37APX_halfTurn_positiveEdge_negative
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H)
    (hp : periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive) :
    periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEdgeTranslationEquiv (L H)
        (periodicHypercubicIntegerTemporalDisplacement (L H) ((H + 1 : ℕ) : ℤ)) e) =
      ReflectionEdgeSide.negative := by
  have hv : (e.1 0).val ≤ H := by
    by_contra! h
    by_cases hd : e.2 = 0
    · have he : e = (e.1, 0) := Prod.ext rfl hd
      have hn : periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.negative := by
        rw [he]
        exact periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val H e.1 (by omega)
      simp [hn] at hp
    · exact (periodicHypercubicEvenEdgeSide_spatial_ne_positive_of_zero_or_half_le_val
        H e hd (Or.inr (by omega))) hp
  let e' : PeriodicHypercubicEvenEdge H :=
    periodicHypercubicEdgeTranslationEquiv (L H)
      (periodicHypercubicIntegerTemporalDisplacement (L H) ((H + 1 : ℕ) : ℤ)) e
  have hadd : (e.1 0).val + (H + 1) < L H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hval : (e'.1 0).val = (e.1 0).val + (H + 1) := by
    exact periodicHypercubicEvenIntegerTemporalEdgeTranslation_sourceTime_val_of_add_lt H (H + 1) e hadd
  change periodicHypercubicEvenEdgeSide H e' = _
  by_cases hd : e.2 = 0
  · have hd' : e'.2 = 0 := by
      simpa [e', periodicHypercubicEdgeTranslationEquiv] using hd
    have he' : e' = (e'.1, 0) := Prod.ext rfl hd'
    have hh : H + 1 ≤ (e'.1 0).val := by omega
    rw [he']
    exact periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val H e'.1 hh
  · have hp0 : 0 < (e.1 0).val := by
      by_contra! h
      exact (periodicHypercubicEvenEdgeSide_spatial_ne_positive_of_zero_or_half_le_val
        H e hd (Or.inl (by omega))) hp
    have hd' : e'.2 ≠ 0 := by
      simpa [e', periodicHypercubicEdgeTranslationEquiv] using hd
    exact periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val H e' hd' (by omega)

/-- Undoing a half turn on any canonical section erases its positive-half
information from the positive restriction. -/
theorem p4Q2PZ37APX_inverseHalfTurn_section_positiveRestriction_eq
    (H : ℕ) (x y : O H 2) :
    (P H).positiveRestriction (Tau (L H) (-((H + 1 : ℕ) : ℤ)) (Section H 2 x)) =
    (P H).positiveRestriction (Tau (L H) (-((H + 1 : ℕ) : ℤ)) (Section H 2 y)) := by
  let k : ℤ := ((H + 1 : ℕ) : ℤ)
  funext e
  change Tau (L H) (-k) (Section H 2 x) e.1 =
    Tau (L H) (-k) (Section H 2 y) e.1
  let t := periodicHypercubicEdgeTranslationEquiv (L H)
    (periodicHypercubicIntegerTemporalDisplacement (L H) k) e.1
  have hx : Section H 2 x t = Tau (L H) (-k) (Section H 2 x) e.1 := by
    have h := periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
      (L H) k (Tau (L H) (-k) (Section H 2 x)) e.1
    rw [periodicHypercubicIntegerTemporalConfigurationTranslation_apply_neg] at h
    exact h
  have hy : Section H 2 y t = Tau (L H) (-k) (Section H 2 y) e.1 := by
    have h := periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
      (L H) k (Tau (L H) (-k) (Section H 2 y)) e.1
    rw [periodicHypercubicIntegerTemporalConfigurationTranslation_apply_neg] at h
    exact h
  have hn : (P H).side t = ReflectionEdgeSide.negative :=
    p4Q2PZ37APX_halfTurn_positiveEdge_negative H e.1 e.2
  have hxy : Section H 2 x t = Section H 2 y t := by
    exact FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_eq_of_side_ne_positive
      (P H) (fun _ => 1) x y (fun _ => 1) t (by rw [hn]; decide)
  exact hx.symm.trans (hxy.trans hy)

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ} {hN : 0 < (2 : ℕ)}
    [Nontrivial G] {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent 2 hN beta hbeta)
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- All nonnegative finite periodic time translations preserving the same
strict positive-time algebra force its finite pullbacks to be constant. -/
theorem p4Q2PZ37APX_canonicalPullback_constant_of_allPositiveTranslations
    (T : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toCanonicalCoherentPositiveTimePullback E)
    (n : ℕ) (F : R.reflectionData.positiveTimeSubalgebra)
    (x y : O (halfExtent n) 2) :
    R.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
      (⟨F.1, F.2⟩ : R.reflectionData.positiveTimeSubalgebra.toSubmodule) x =
    R.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
      (⟨F.1, F.2⟩ : R.reflectionData.positiveTimeSubalgebra.toSubmodule) y := by
  let Q := R.toLinearHalfSupportReflection
  let k : ℕ := halfExtent n + 1
  let A := Section (halfExtent n) 2 x
  let B := Section (halfExtent n) 2 y
  let A' := Tau (L (halfExtent n)) (-(Int.ofNat k)) A
  let B' := Tau (L (halfExtent n)) (-(Int.ofNat k)) B
  let f : BoundedContinuousFunction S.Configuration ℝ :=
    ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ)
  let g : BoundedContinuousFunction S.Configuration ℝ :=
    (((T.positiveTranslation n k F : R.reflectionData.positiveTimeSubalgebra) :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ)
  have hT (Z : PeriodicHypercubicEvenEdge (halfExtent n) → G) :
      g (R.interpolate n Z) =
        f (R.interpolate n (Tau (L (halfExtent n)) (Int.ofNat k) Z)) := by
    calc
      _ = f (E.translate (T.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat k))
          (R.interpolate n Z)) := by
        simp only [g, f, T.positiveTranslation_coe,
          PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance.fullTranslation,
          PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance.realizedGaugeInvariantObservableTranslation,
          physicalGaugeInvariantObservablePrecompAlgEquiv_apply]
      _ = _ := by
        have h := T.toDiscreteTemporalCovariance.interpolate_integerTemporal_equivariant n (Int.ofNat k) Z
        change R.interpolate n (Tau (L (halfExtent n)) (Int.ofNat k) Z) =
          E.translate ((Int.ofNat k : ℝ) * S.latticeSpacing n) (R.interpolate n Z) at h
        exact congrArg f h.symm
  have hA : Tau (L (halfExtent n)) (Int.ofNat k) A' = A :=
    periodicHypercubicIntegerTemporalConfigurationTranslation_apply_neg _ _ _
  have hB : Tau (L (halfExtent n)) (Int.ofNat k) B' = B :=
    periodicHypercubicIntegerTemporalConfigurationTranslation_apply_neg _ _ _
  have hres : (P (halfExtent n)).positiveRestriction A' =
      (P (halfExtent n)).positiveRestriction B' :=
    p4Q2PZ37APX_inverseHalfTurn_section_positiveRestriction_eq (halfExtent n) x y
  change Q.positiveHalfPullback n ⟨F.1, F.2⟩ x =
    Q.positiveHalfPullback n ⟨F.1, F.2⟩ y
  calc
    _ = f (R.interpolate n A) := by
      symm
      simpa only [A, f, periodicHypercubicEvenSpecialUnitaryPositiveRestriction_positiveHalfSection]
        using Q.observable_pullback n F A
    _ = g (R.interpolate n A') := by rw [hT A', hA]
    _ = g (R.interpolate n B') := by
      change (((T.positiveTranslation n k F : R.reflectionData.positiveTimeSubalgebra) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A') =
        (((T.positiveTranslation n k F : R.reflectionData.positiveTimeSubalgebra) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n B')
      rw [Q.observable_pullback n (T.positiveTranslation n k F) A',
        Q.observable_pullback n (T.positiveTranslation n k F) B', hres]
    _ = f (R.interpolate n B) := by rw [hT B', hB]
    _ = _ := by
      simpa only [B, f, periodicHypercubicEvenSpecialUnitaryPositiveRestriction_positiveHalfSection]
        using Q.observable_pullback n F B

/-- A nonconstant genuine time-one observable cannot be an exact pullback
under the all-step positive-time covariance assumptions. -/
theorem p4Q2PZ37APX_no_exact_modeOnePullback_of_distinct_values
    (T : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toCanonicalCoherentPositiveTimePullback E)
    (n : ℕ) (hH : 0 < halfExtent n)
    (x y : O (halfExtent n) 2)
    (hxy : p4Q2PZ37APW_openTimeOneObservable (halfExtent n) hH 0 1 x ≠
      p4Q2PZ37APW_openTimeOneObservable (halfExtent n) hH 0 1 y) :
    ¬ ∃ F : R.reflectionData.positiveTimeSubalgebra,
      R.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
        (⟨F.1, F.2⟩ : R.reflectionData.positiveTimeSubalgebra.toSubmodule) =
        p4Q2PZ37APW_openTimeOneObservable (halfExtent n) hH 0 1 := by
  rintro ⟨F, hF⟩
  have h := p4Q2PZ37APX_canonicalPullback_constant_of_allPositiveTranslations R T n F x y
  rw [hF] at h
  exact hxy h

end
end MGAP4D.MathlibAnalytic
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APX_halfTurn_positiveEdge_negative
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APX_inverseHalfTurn_section_positiveRestriction_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APX_canonicalPullback_constant_of_allPositiveTranslations
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APX_no_exact_modeOnePullback_of_distinct_values

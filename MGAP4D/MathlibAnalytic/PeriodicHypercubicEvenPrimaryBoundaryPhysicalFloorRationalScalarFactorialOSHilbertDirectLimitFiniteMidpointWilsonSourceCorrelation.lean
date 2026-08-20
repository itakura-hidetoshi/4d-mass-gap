import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteCenteredMidpointCorrelationReduction
import Mathlib.Tactic

/-!
# Actual Wilson-source realization of finite midpoint correlations

The preceding same-root reduction identifies the remaining quantitative decay input with the
finite midpoint-resolved scalar-path quantity

`M_n(F;r) = E_n[F(x_-q) F(x_(q+2r))] - E_n[tau_r F]^2`.

This file pulls that midpoint quantity one level further back, through the already-canonical direct
source identity for the primary scalar path law, to the actual compact `SU(N)` Wilson Gibbs
measure at each selected factorial scale.

The two midpoint factors are evaluated on the literal reflection-completed primary scalar path
read out from one finite Wilson configuration.  Thus the remaining common-decay statement is
proved exactly equivalent to a static centered two-time correlation estimate under the actual
finite Wilson Gibbs measure itself.  No heat-bath update time, random-scan chain, old physical
Hilbert carrier, transfer-operator premise, positive rate, or numerical mass value is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance finiteMidpointWilsonSourceSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance finiteMidpointWilsonSourceSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteMidpointWilsonSourceSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteMidpointWilsonSourceSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteMidpointWilsonSourceSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteMidpointWilsonSourceSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Restrict a scalar rational path to the reflected fixed-slot coordinates `-q`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftRestrictionContinuousMap
    (J : Finset ℚ) : C(ℚ → ℝ, ∀ q : J, ℝ) :=
  ⟨fun x q => x (-q.1), continuous_pi (fun q => continuous_apply (-q.1))⟩

/-- Restrict a scalar rational path to the midpoint-resolved right coordinates `q+2r`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightRestrictionContinuousMap
    (J : Finset ℚ) (r : ℚ) : C(ℚ → ℝ, ∀ q : J, ℝ) :=
  ⟨fun x q => x ((q.1 + r) + r),
    continuous_pi (fun q => continuous_apply ((q.1 + r) + r))⟩

/-- Product test on the scalar path for the midpoint-resolved pair. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable
    (J : Finset ℚ) (r : ℚ)
    (F G : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  (F.compContinuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftRestrictionContinuousMap
        J)) *
    (G.compContinuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightRestrictionContinuousMap
        J r))

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable_apply
    (J : Finset ℚ) (r : ℚ)
    (F G : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable
        J r F G x =
      F (fun q : J => x (-q.1)) *
        G (fun q : J => x ((q.1 + r) + r)) :=
  rfl

/-- Exact direct-source pullback of a midpoint product expectation.  This is termwise at every
finite scale: no eventual stationarity or continuum limit is used. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductExpectation_eq_wilsonSource
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ) (r : ℚ)
    (F G : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    (∫ x,
        F (fun q : J => x (-q.1)) *
          G (fun q : J => x ((q.1 + r) + r))
      ∂(periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n : Measure (ℚ → ℝ))) =
      ∫ A,
        F (fun q : J =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n A) (-q.1)) *
          G (fun q : J =>
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
                H latticeSpacing n A) ((q.1 + r) + r))
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  let X :=
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N) ∘
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n)
  let Phi :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable
      J r F G
  let mu :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  have hX : Measurable X := by
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable
        H N).comp
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
          H (Matrix.specialUnitaryGroup (Fin N) ℂ) latticeSpacing n)
  have hdirect :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_eq_map_wilsonSource
      H N hN beta hbeta latticeSpacing n
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_toMeasure,
    hdirect]
  change (∫ y, Phi y ∂Measure.map X mu) = ∫ A, Phi (X A) ∂mu
  exact MeasureTheory.integral_map
    hX.aemeasurable Phi.continuous.aestronglyMeasurable

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Literal midpoint product expectation written directly on the actual compact Wilson Gibbs
source at selected factorial scale `n`. -/
noncomputable def fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceProductExpectation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  let X :=
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
      (H (L.subsequence n)) N) ∘
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
        (H (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n)
  ∫ A,
    F.observable (fun q : (P.fixedSlotDataOfIndex J).slots => X A (-q.1)) *
      F.observable
        (fun q : (P.fixedSlotDataOfIndex J).slots => X A ((q.1 + r) + r))
    ∂(periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (H (L.subsequence n))) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))).gibbsMeasure

/-- Actual Wilson-source midpoint product with the square of the same translated finite mean
subtracted.  The centering scalar is exactly the one in the #1917 midpoint quantity. -/
noncomputable def fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCenteredCorrelation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ) (hr : 0 ≤ r)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate r hr J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate r hr F
  let m := (P.fixedSlotDataOfIndex K).fixedSlotCarrierFiniteMean G n
  P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceProductExpectation J r F n - m ^ 2

/-- The #1917 finite midpoint quantity is termwise exactly its actual compact Wilson-source
centered correlation. -/
theorem fixedSlotCarrierFiniteTranslatedMidpointMeanSubtractedCorrelation_eq_wilsonSource
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ) (hr : 0 ≤ r)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) :
    P.fixedSlotCarrierFiniteTranslatedMidpointMeanSubtractedCorrelation J r hr F n =
      P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCenteredCorrelation J r hr F n := by
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate r hr J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate r hr F
  let m := (P.fixedSlotDataOfIndex K).fixedSlotCarrierFiniteMean G n
  let mu :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n
  have hpull :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductExpectation_eq_wilsonSource
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n (P.fixedSlotDataOfIndex J).slots r F.observable F.observable
  change
    ((∫ x,
        F.observable
            (fun q : (P.fixedSlotDataOfIndex J).slots => x (-q.1)) *
          F.observable
            (fun q : (P.fixedSlotDataOfIndex J).slots => x ((q.1 + r) + r))
        ∂(mu : Measure (ℚ → ℝ))) - m ^ 2) =
      P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceProductExpectation J r F n - m ^ 2
  rw [hpull]
  rfl

/-- Actual Wilson-source midpoint correlation aligned with positive smoothing time `s` and
subsequent half-separation `h`. -/
noncomputable def fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCenteredCorrelation
    J ((s : ℚ) + h) (add_nonneg s.2 hh) F n

/-- Smoothed scalar midpoint correlation and actual Wilson-source midpoint correlation agree
termwise on every selected factorial scale. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation_eq_wilsonSource
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) :
    P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation J s h hh F n =
      P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation J s h hh F n := by
  exact
    P.fixedSlotCarrierFiniteTranslatedMidpointMeanSubtractedCorrelation_eq_wilsonSource
      J ((s : ℚ) + h) (add_nonneg s.2 hh) F n

/-- Common physical Euclidean-time decay stated entirely as a static centered correlation
inequality on the actual finite compact Wilson Gibbs source. -/
def FixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceUniformDecayAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) : Prop :=
  ∀ (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (_hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (t : NNRat),
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation
          J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F n ≤
        Real.exp (-m * (t : ℝ)) *
          P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation
            J s 0 le_rfl F n

/-- The common midpoint-decay input is exactly equivalent to its formulation on the actual compact
Wilson Gibbs source.  This equivalence is termwise and therefore needs no additional scaling or
continuum hypothesis. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredMidpointUniformDecayAt_iff_wilsonSource
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) :
    P.FixedSlotCarrierFiniteSmoothedCenteredMidpointUniformDecayAt m ↔
      P.FixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceUniformDecayAt m := by
  constructor
  · intro hdec J s hs F t
    filter_upwards [hdec J s hs F t] with n hn
    rw [← P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation_eq_wilsonSource
      J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F n]
    rw [← P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation_eq_wilsonSource
      J s 0 le_rfl F n]
    exact hn
  · intro hdec J s hs F t
    filter_upwards [hdec J s hs F t] with n hn
    rw [P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation_eq_wilsonSource
      J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F n]
    rw [P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation_eq_wilsonSource
      J s 0 le_rfl F n]
    exact hn

/-- Direct same-root endpoint from an actual compact Wilson-source midpoint correlation decay
rate.  Nontriviality of the exact excitation sector remains an explicit independent input. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_wilsonSourceMidpointDecay_of_nontrivial
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    {m : ℝ}
    (hm : 0 < m)
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceUniformDecayAt m)
    (hne : ∃ x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert, x ≠ 0) :
    ∃ mu : ℝ, 0 < mu ∧
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt mu := by
  have hmid : P.FixedSlotCarrierFiniteSmoothedCenteredMidpointUniformDecayAt m :=
    (P.fixedSlotCarrierFiniteSmoothedCenteredMidpointUniformDecayAt_iff_wilsonSource m).2 hdec
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_midpointDecay_of_nontrivial
      hreach hm hmid hne

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteMidpointWilsonSourceCorrelation
import Mathlib.Tactic

/-!
# Actual Wilson-source midpoint correlations as static Gibbs covariances

The preceding same-root layer identifies the remaining finite decay input with the centered
midpoint product on the actual compact periodic `SU(N)` Wilson Gibbs source.  The centering scalar
there is the finite mean of the midpoint-translated literal cylinder.

For static Gibbs correlation technology, the canonical object is instead the ordinary covariance

`E_W[O_- O_+] - E_W[O_-] E_W[O_+]`.

This file proves that these are eventually exactly the same quantity on the selected factorial
tail.  The left midpoint marginal has the original finite mean by exact reflection invariance.  The
right midpoint marginal has that same mean eventually by the already-canonical factorial temporal
stationarity at the doubled midpoint shift.  The midpoint centering scalar itself has the original
finite mean eventually by stationarity at the single shift.

Consequently the #1918 Wilson-source midpoint decay predicate is exactly equivalent to exponential
decay of an ordinary static covariance of two literal observables under the actual compact Wilson
Gibbs measure.  This is the form to which a future support-distance Dobrushin or other static
clustering estimate may be applied.

No heat-bath time, random-scan time, boundary Gram operator, transfer-operator hypothesis, spectral
gap, positive rate, or numerical mass value is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance finiteMidpointWilsonCovarianceSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance finiteMidpointWilsonCovarianceSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteMidpointWilsonCovarianceSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteMidpointWilsonCovarianceSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteMidpointWilsonCovarianceSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteMidpointWilsonCovarianceSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact pullback of the left midpoint marginal from the scalar path law to the actual compact
Wilson Gibbs source. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftExpectation_eq_wilsonSource
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    (∫ x, F (fun q : J => x (-q.1))
      ∂(periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n : Measure (ℚ → ℝ))) =
      ∫ A,
        F (fun q : J =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n A) (-q.1))
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  have h :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductExpectation_eq_wilsonSource
      H N hN beta hbeta latticeSpacing n J 0 F
      (1 : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
  simpa using h

/-- Exact pullback of the right midpoint marginal from the scalar path law to the actual compact
Wilson Gibbs source. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightExpectation_eq_wilsonSource
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ) (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    (∫ x, F (fun q : J => x ((q.1 + r) + r))
      ∂(periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n : Measure (ℚ → ℝ))) =
      ∫ A,
        F (fun q : J =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n A) ((q.1 + r) + r))
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  have h :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductExpectation_eq_wilsonSource
      H N hN beta hbeta latticeSpacing n J r
      (1 : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) F
  simpa using h

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Left literal midpoint marginal expectation on the actual selected compact Wilson Gibbs source. -/
noncomputable def fixedSlotCarrierFiniteMidpointWilsonSourceLeftExpectation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
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
    F.observable (fun q : (P.fixedSlotDataOfIndex J).slots => X A (-q.1))
    ∂(periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (H (L.subsequence n))) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))).gibbsMeasure

/-- Right literal midpoint marginal expectation on the actual selected compact Wilson Gibbs source. -/
noncomputable def fixedSlotCarrierFiniteMidpointWilsonSourceRightExpectation
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
    F.observable
      (fun q : (P.fixedSlotDataOfIndex J).slots => X A ((q.1 + r) + r))
    ∂(periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (H (L.subsequence n))) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))).gibbsMeasure

/-- The left midpoint source marginal has exactly the original finite cylinder mean.  This is
finite reflection invariance, not an asymptotic statement. -/
theorem fixedSlotCarrierFiniteMidpointWilsonSourceLeftExpectation_eq_finiteMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) :
    P.fixedSlotCarrierFiniteMidpointWilsonSourceLeftExpectation J F n =
      (P.fixedSlotDataOfIndex J).fixedSlotCarrierFiniteMean F n := by
  let mu :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n
  let Cyl := (P.fixedSlotDataOfIndex J).fixedSlotCarrierPositiveCylinder F
  let Left : BoundedContinuousFunction (ℚ → ℝ) ℝ :=
    F.observable.compContinuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftRestrictionContinuousMap
        (P.fixedSlotDataOfIndex J).slots)
  have href :
      Measure.map
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
          (mu : Measure (ℚ → ℝ)) =
        (mu : Measure (ℚ → ℝ)) := by
    simpa [mu] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_reflection_map_eq_self
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n
  have hobs :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
          Cyl.pathObservable = Left := by
    ext x
    rw [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_apply]
    change
      F.observable
          (fun q : (P.fixedSlotDataOfIndex J).slots =>
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x q.1) =
        F.observable (fun q : (P.fixedSlotDataOfIndex J).slots => x (-q.1))
    rfl
  have hrefExp :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_reflectionPullback_eq_of_map_eq_self
      mu href Cyl.pathObservable
  have hpull :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftExpectation_eq_wilsonSource
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n (P.fixedSlotDataOfIndex J).slots F.observable
  change
    P.fixedSlotCarrierFiniteMidpointWilsonSourceLeftExpectation J F n =
      (P.fixedSlotDataOfIndex J).fixedSlotCarrierFiniteMean F n
  unfold fixedSlotCarrierFiniteMidpointWilsonSourceLeftExpectation
  simp only [Function.comp_apply]
  rw [← hpull]
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu Left =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu Cyl.pathObservable
  rw [← hobs]
  exact hrefExp

/-- The right midpoint source marginal is exactly the finite mean of the same literal cylinder
translated by the doubled midpoint shift. -/
theorem fixedSlotCarrierFiniteMidpointWilsonSourceRightExpectation_eq_doubleTranslateFiniteMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ) (hr : 0 ≤ r)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) :
    P.fixedSlotCarrierFiniteMidpointWilsonSourceRightExpectation J r F n =
      (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate (r + r) (add_nonneg hr hr) J)).fixedSlotCarrierFiniteMean
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate
          (r + r) (add_nonneg hr hr) F) n := by
  let mu :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n
  let Right : BoundedContinuousFunction (ℚ → ℝ) ℝ :=
    F.observable.compContinuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightRestrictionContinuousMap
        (P.fixedSlotDataOfIndex J).slots r)
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate (r + r) (add_nonneg hr hr) J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate
    (r + r) (add_nonneg hr hr) F
  let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
  have hobs : Cyl.pathObservable = Right := by
    ext x
    change
      F.observable
          (fun q : (P.fixedSlotDataOfIndex J).slots => x (q.1 + (r + r))) =
        F.observable
          (fun q : (P.fixedSlotDataOfIndex J).slots => x ((q.1 + r) + r))
    congr 1
    funext q
    ring
  have hpull :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightExpectation_eq_wilsonSource
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n (P.fixedSlotDataOfIndex J).slots r F.observable
  change
    P.fixedSlotCarrierFiniteMidpointWilsonSourceRightExpectation J r F n =
      (P.fixedSlotDataOfIndex K).fixedSlotCarrierFiniteMean G n
  unfold fixedSlotCarrierFiniteMidpointWilsonSourceRightExpectation
  simp only [Function.comp_apply]
  rw [← hpull]
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu Right =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu Cyl.pathObservable
  rw [hobs]

/-- On the selected factorial tail, both actual Wilson midpoint marginals equal the single-shift
finite mean used to center the #1918 midpoint product. -/
theorem fixedSlotCarrierFiniteMidpointWilsonSourceMarginalMeans_eventually_eq_translatedMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ) (hr : 0 ≤ r)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteMidpointWilsonSourceLeftExpectation J F n =
          (P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate r hr J)).fixedSlotCarrierFiniteMean
            ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate r hr F) n ∧
        P.fixedSlotCarrierFiniteMidpointWilsonSourceRightExpectation J r F n =
          (P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate r hr J)).fixedSlotCarrierFiniteMean
            ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate r hr F) n := by
  have hsingle :=
    (P.fixedSlotDataOfIndex J).fixedSlotCarrierFiniteMean_timeTranslate_eventually_eq
      r hr F
  have hdouble :=
    (P.fixedSlotDataOfIndex J).fixedSlotCarrierFiniteMean_timeTranslate_eventually_eq
      (r + r) (add_nonneg hr hr) F
  filter_upwards [hsingle, hdouble] with n hsingle_n hdouble_n
  constructor
  · rw [P.fixedSlotCarrierFiniteMidpointWilsonSourceLeftExpectation_eq_finiteMean J F n]
    exact hsingle_n.symm
  · rw [P.fixedSlotCarrierFiniteMidpointWilsonSourceRightExpectation_eq_doubleTranslateFiniteMean
      J r hr F n]
    rw [hdouble_n]
    exact hsingle_n.symm

/-- Ordinary static covariance of the two literal midpoint observables under the actual compact
Wilson Gibbs source. -/
noncomputable def fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCovariance
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceProductExpectation J r F n -
    P.fixedSlotCarrierFiniteMidpointWilsonSourceLeftExpectation J F n *
      P.fixedSlotCarrierFiniteMidpointWilsonSourceRightExpectation J r F n

/-- The #1918 centered source midpoint quantity is eventually exactly the ordinary static Gibbs
covariance. -/
theorem fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCenteredCorrelation_eventually_eq_covariance
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ) (hr : 0 ≤ r)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCenteredCorrelation J r hr F n =
        P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCovariance J r F n := by
  filter_upwards [
    P.fixedSlotCarrierFiniteMidpointWilsonSourceMarginalMeans_eventually_eq_translatedMean
      J r hr F] with n hn
  rcases hn with ⟨hleft, hright⟩
  unfold fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCenteredCorrelation
  unfold fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCovariance
  rw [hleft, hright]
  ring

/-- Smoothed ordinary Wilson-source covariance aligned with the current positive smoothing time
`s` and subsequent half-separation `h`. -/
noncomputable def fixedSlotCarrierFiniteSmoothedMidpointWilsonSourceCovariance
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCovariance
    J ((s : ℚ) + h) F n

/-- The smoothed #1918 source midpoint correlation is eventually exactly the ordinary static
Wilson Gibbs covariance. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation_eventually_eq_covariance
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation J s h hh F n =
        P.fixedSlotCarrierFiniteSmoothedMidpointWilsonSourceCovariance J s h hh F n := by
  exact
    P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCenteredCorrelation_eventually_eq_covariance
      J ((s : ℚ) + h) (add_nonneg s.2 hh) F

/-- Common Euclidean-time decay stated as decay of ordinary static covariances of literal
observables under the actual compact finite Wilson Gibbs source. -/
def FixedSlotCarrierFiniteSmoothedMidpointWilsonSourceCovarianceUniformDecayAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) : Prop :=
  ∀ (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (_hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (t : NNRat),
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedMidpointWilsonSourceCovariance
          J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F n ≤
        Real.exp (-m * (t : ℝ)) *
          P.fixedSlotCarrierFiniteSmoothedMidpointWilsonSourceCovariance
            J s 0 le_rfl F n

/-- The actual Wilson-source midpoint-decay input is exactly equivalent to ordinary static Gibbs
covariance decay on the selected factorial tail. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceUniformDecayAt_iff_covariance
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) :
    P.FixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceUniformDecayAt m ↔
      P.FixedSlotCarrierFiniteSmoothedMidpointWilsonSourceCovarianceUniformDecayAt m := by
  constructor
  · intro hdec J s hs F t
    have hnum :=
      P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation_eventually_eq_covariance
        J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F
    have hzero :=
      P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation_eventually_eq_covariance
        J s 0 le_rfl F
    filter_upwards [hdec J s hs F t, hnum, hzero] with n hn hnum_n hzero_n
    rw [← hnum_n, ← hzero_n]
    exact hn
  · intro hdec J s hs F t
    have hnum :=
      P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation_eventually_eq_covariance
        J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F
    have hzero :=
      P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceCorrelation_eventually_eq_covariance
        J s 0 le_rfl F
    filter_upwards [hdec J s hs F t, hnum, hzero] with n hn hnum_n hzero_n
    rw [hnum_n, hzero_n]
    exact hn

/-- Direct same-root coercivity endpoint from a positive common decay rate for the actual compact
Wilson Gibbs static midpoint covariances. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_wilsonSourceCovarianceDecay_of_nontrivial
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
    (hdec : P.FixedSlotCarrierFiniteSmoothedMidpointWilsonSourceCovarianceUniformDecayAt m)
    (hne : ∃ x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert, x ≠ 0) :
    ∃ mu : ℝ, 0 < mu ∧
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt mu := by
  have hsource : P.FixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceUniformDecayAt m :=
    (P.fixedSlotCarrierFiniteSmoothedCenteredMidpointWilsonSourceUniformDecayAt_iff_covariance m).2 hdec
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_wilsonSourceMidpointDecay_of_nontrivial
      hreach hm hsource hne

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteMidpointWilsonSourceCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointPlaquetteLocalDistanceLowerBound
import Mathlib.Tactic

/-!
# Actual midpoint Wilson covariance on separated physical-link supports

The current same-root route has now reached two exact finite statements about
the same literal midpoint pair:

* the remaining finite two-time quantity is an ordinary static covariance under
  the actual compact periodic `SU(N)` Wilson Gibbs measure;
* the reflected-left and translated-right midpoint observables depend on
  explicit finite sets of physical links, and those support sets have an actual
  Wilson-plaquette-local path-separation lower bound whenever the corresponding
  cyclic physical-floor bound holds.

This file identifies those layers without adding a clustering hypothesis.  It
names the two actual source observables, writes their ordinary static covariance,
proves their exact support dependence, identifies the selected-factorial
covariance from the existing same-root route with this support-localized
covariance, and packages support dependence together with the plaquette-local
separation receipt.

No covariance decay rate is proved here.  In particular, no assumption that
`18 * q(beta) < 1` holds along the factorial continuum sequence is introduced.
No heat-bath or random-scan time is identified with Euclidean time, and no
positive mass or Hamiltonian gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance midpointSeparatedCovarianceSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance midpointSeparatedCovarianceSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance midpointSeparatedCovarianceSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance midpointSeparatedCovarianceSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance midpointSeparatedCovarianceSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance midpointSeparatedCovarianceSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The literal reflected-left fixed-slot observable on the actual finite Wilson
configuration space. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  let X :=
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N) ∘
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n)
  F (fun q : J => X A (-q.1))

/-- The literal translated-right fixed-slot observable on the actual finite
Wilson configuration space. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  let X :=
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N) ∘
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n)
  F (fun q : J => X A ((q.1 + r) + r))

/-- Ordinary static covariance of the two literal midpoint observables under
the actual compact periodic `SU(N)` Wilson Gibbs measure. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) : ℝ :=
  let μ :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  let OLeft :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
      H N latticeSpacing n J F
  let ORight :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
      H N latticeSpacing n J r F
  (∫ A, OLeft A * ORight A ∂μ) -
    (∫ A, OLeft A ∂μ) * (∫ A, ORight A ∂μ)

/-- The actual reflected-left source observable depends only on the finite
reflected-left midpoint support from the canonical support layer. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J →
      A e = B e) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
        H N latticeSpacing n J F A =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
        H N latticeSpacing n J F B := by
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftObservable_eq_of_eqOn_support
      H N latticeSpacing n J hJ F A B hAB

/-- The actual translated-right source observable depends only on the finite
translated-right midpoint support from the canonical support layer. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r →
      A e = B e) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
        H N latticeSpacing n J r F A =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
        H N latticeSpacing n J r F B := by
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightObservable_eq_of_eqOn_support
      H N latticeSpacing n J hJ r hr F A B hAB

/-- The selected-factorial ordinary static covariance from the existing
same-root route is definitionally the support-localized covariance above. -/
theorem
    PrimaryScalarFixedSlotOSPreHilbertData.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCovariance_eq_supportLocalized
    {H : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) :
    P.fixedSlotCarrierFiniteTranslatedMidpointWilsonSourceCovariance J r F n =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n (P.fixedSlotDataOfIndex J).slots r F.observable := by
  rfl

/-- Exact support receipt for the ordinary static midpoint covariance: the left
and right factors depend only on their respective physical-link supports, and
those supports are separated by at least `D` actual Wilson-plaquette-local
steps whenever the explicit cyclic physical-floor lower bound is at least
`D`. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_support_receipt_of_floor_min_ge
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (D : ℕ)
    (hleftWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (hrightWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) ≤ H)
    (hfloor : ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
      D ≤
        min
          (Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
            Int.toNat
              (physicalTemporalFloorStep latticeSpacing
                ((((qRight + r) + r : ℚ) : ℝ)) n))
          (PeriodicHypercubicEvenSideLength H -
            (Int.toNat
                (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
              Int.toNat
                (physicalTemporalFloorStep latticeSpacing
                  ((((qRight + r) + r : ℚ) : ℝ)) n))))
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    (∀ A B : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ,
      (∀ e,
        e ∈
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
            H latticeSpacing n J →
        A e = B e) →
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
          H N latticeSpacing n J F A =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
          H N latticeSpacing n J F B) ∧
    (∀ A B : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ,
      (∀ e,
        e ∈
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
            H latticeSpacing n J r →
        A e = B e) →
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
          H N latticeSpacing n J r F A =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
          H N latticeSpacing n J r F B) ∧
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r) := by
  constructor
  · intro A B hAB
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable_eq_of_eqOn_support
        H N latticeSpacing n J hJ F A B hAB
  constructor
  · intro A B hAB
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable_eq_of_eqOn_support
        H N latticeSpacing n J hJ r hr F A B hAB
  · exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_plaquetteLocalSeparatedBy_of_floor_min_ge
        H latticeSpacing n J r D hleftWithin hrightWithin hfloor

end

end MathlibAnalytic
end MGAP4D

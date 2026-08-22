import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceBoundedContinuous
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteSupportGibbsCovarianceSpatialGeometric
import Mathlib.Tactic

/-!
# Geometric decay of the actual finite midpoint Wilson-source covariance

The canonical route now has all ingredients on the same finite compact Wilson
source:

* the literal midpoint covariance and its exact reflected-left / translated-right
  physical-link supports;
* a bounded-continuous realization of both literal source observables;
* the direct finite-support spatial Gibbs covariance theorem under the concrete
  periodic `SU(N)` Dobrushin threshold.

This file composes those layers.  The two source BCF norms are also bounded by
the norm of the original fixed-slot observable, because each source is only a
composition of that observable with a finite coordinate map.

The result is a genuine finite-volume geometric spatial-clustering estimate for
the actual midpoint Wilson-source covariance used by the same-root OS route.
It still assumes the finite-scale threshold explicitly.  No assertion is made
that this threshold holds uniformly on the factorial continuum sequence, and no
continuum clustering or physical mass-gap conclusion is drawn here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

private instance midpointWilsonSourceCovarianceGeometricSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

local instance midpointWilsonSourceCovarianceGeometricIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance midpointWilsonSourceCovarianceGeometricCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance midpointWilsonSourceCovarianceGeometricSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance midpointWilsonSourceCovarianceGeometricMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance midpointWilsonSourceCovarianceGeometricBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Pullback to the reflected-left finite Wilson source does not increase the
sup norm of the original fixed-slot bounded continuous observable. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF_norm_le
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
        H N latticeSpacing n J hJ F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).2
  intro A
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF_apply]
  unfold
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
  simpa [Real.norm_eq_abs] using
    F.norm_coe_le_norm
      (fun q : J =>
        ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N) ∘
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n)) A (-q.1))

/-- Pullback to the translated-right finite Wilson source does not increase the
sup norm of the original fixed-slot bounded continuous observable. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF_norm_le
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
        H N latticeSpacing n J hJ r hr F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).2
  intro A
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF_apply]
  unfold
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
  simpa [Real.norm_eq_abs] using
    F.norm_coe_le_norm
      (fun q : J =>
        ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N) ∘
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n)) A ((q.1 + r) + r))

/-- The support-localized midpoint covariance is exactly the canonical Gibbs
covariance of the right and left bounded-continuous source observables.  The
order is chosen so that the support order in the clustering theorem is exactly
`(leftSupport, rightSupport)`. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eq_gibbsCovarianceReal_bcf
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
        H N hN beta hbeta latticeSpacing n J r F =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsCovarianceReal
        (fun A =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
            H N latticeSpacing n J hJ r hr F A)
        (fun A =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
            H N latticeSpacing n J hJ F A) := by
  unfold
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF_apply]
  simp [mul_comm]

/-- Under the concrete finite-scale periodic `SU(N)` Dobrushin threshold, the
actual literal midpoint Wilson-source covariance decays geometrically in the
plaquette-local separation lower bound supplied by the physical-floor geometry. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_abs_le_geometric_of_floor_min_ge
    (H N D : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold : 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
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
    |periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
        H N hN beta hbeta latticeSpacing n J r F| ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
        (∑ e ∈
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
            H latticeSpacing n J r,
          2 * ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
            H N latticeSpacing n J hJ r hr F‖) *
        ∑ i ∈
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
            H latticeSpacing n J,
          2 * ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
            H N latticeSpacing n J hJ F‖ := by
  rcases
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_support_receipt_of_floor_min_ge
      H N latticeSpacing n J hJ r hr D hleftWithin hrightWithin hfloor F with
    ⟨_hLeftRaw, _hRightRaw, hsep⟩
  let Left :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
      H N latticeSpacing n J hJ F
  let Right :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
      H N latticeSpacing n J hJ r hr F
  have hRightDepends :
      ∀ A B,
        (∀ e,
          e ∈
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
              H latticeSpacing n J r →
          A e = B e) →
        Right A = Right B := by
    intro A B hAB
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF_eq_of_eqOn_support
        H N latticeSpacing n J hJ r hr F A B hAB
  have hLeftDepends :
      ∀ A B,
        (∀ e,
          e ∈
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
              H latticeSpacing n J →
          A e = B e) →
        Left A = Left B := by
    intro A B hAB
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF_eq_of_eqOn_support
        H N latticeSpacing n J hJ F A B hAB
  have hCov :=
    periodicHypercubicEvenSpecialUnitary_gibbsCovarianceReal_abs_le_geometric_of_finiteSupportsSeparatedBy
      H N D hH hN beta hbeta hThreshold
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r)
      hsep Right Left hRightDepends hLeftDepends
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eq_gibbsCovarianceReal_bcf
      H N hN beta hbeta latticeSpacing n J hJ r hr F]
  simpa [Left, Right] using hCov

end

end MathlibAnalytic
end MGAP4D

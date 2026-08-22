import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceCovarianceScalingLimitZero
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteMidpointWilsonSourceCovariance
import Mathlib.Tactic

/-!
# Weak-limit transfer of the midpoint Wilson covariance

The finite midpoint covariance now has a scale-uniform geometric route, while
the same-root primary scalar path laws already live on the fixed Polish carrier
`ℚ → ℝ` and admit Prokhorov weak limits.  This file closes the representation
gap between those two layers.

The reflected-left and translated-right midpoint factors are fixed bounded
continuous functions of the scalar rational path.  Their product is likewise
bounded continuous.  Therefore weak convergence of the scalar path probability
measures transports all three expectations, and hence transports their
covariance.

As a consequence, if the explicit scaling assumptions and one uniform finite
Dobrushin ratio `rhoBar < 1` hold, then the continuum-path covariance at every
fixed positive rational midpoint separation is exactly zero.  This last
statement is deliberately read as a conditional ultralocality consequence of a
scale-independent high-temperature ratio, not as a physical mass-gap theorem.
Nothing here proves that the actual factorial Yang--Mills coupling sequence
satisfies such a uniform ratio.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- The reflected-left midpoint test as one fixed bounded-continuous observable
on the scalar rational path carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftPathObservable
    (J : Finset ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  F.compContinuous
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftRestrictionContinuousMap
      J)

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftPathObservable_apply
    (J : Finset ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftPathObservable
        J F x =
      F (fun q : J => x (-q.1)) :=
  rfl

/-- The translated-right midpoint test as one fixed bounded-continuous
observable on the scalar rational path carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightPathObservable
    (J : Finset ℚ)
    (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  F.compContinuous
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightRestrictionContinuousMap
      J r)

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightPathObservable_apply
    (J : Finset ℚ)
    (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightPathObservable
        J r F x =
      F (fun q : J => x ((q.1 + r) + r)) :=
  rfl

/-- Covariance of the fixed reflected-left and translated-right midpoint tests
under an arbitrary scalar rational path probability measure. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPathCovariance
    (μ : ProbabilityMeasure (ℚ → ℝ))
    (J : Finset ℚ)
    (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) : ℝ :=
  let Left :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftPathObservable
      J F
  let Right :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightPathObservable
      J r F
  let Product :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable
      J r F F
  (∫ x, Product x ∂(μ : Measure (ℚ → ℝ))) -
    (∫ x, Left x ∂(μ : Measure (ℚ → ℝ))) *
      (∫ x, Right x ∂(μ : Measure (ℚ → ℝ)))

/-- At every finite scale, the actual Wilson-source midpoint covariance is
exactly the covariance of the corresponding fixed bounded-continuous tests under
the scalar path pushforward law. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eq_pathCovariance
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
        H N hN beta hbeta latticeSpacing n J r F =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPathCovariance
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
          H N hN beta hbeta latticeSpacing n)
        J r F := by
  unfold
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPathCovariance
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
  dsimp
  simp only [Function.comp_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftPathObservable_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightPathObservable_apply]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductExpectation_eq_wilsonSource
      H N hN beta hbeta latticeSpacing n J r F F,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftExpectation_eq_wilsonSource
      H N hN beta hbeta latticeSpacing n J F,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightExpectation_eq_wilsonSource
      H N hN beta hbeta latticeSpacing n J r F]

/-- Weak convergence of the same-root scalar path laws transports the midpoint
covariance because left, right, and product tests are all fixed bounded
continuous functions on `ℚ → ℝ`. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.midpointPathCovariance_tendsto
    (H : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J : Finset ℚ)
    (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPathCovariance
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            latticeSpacing (L.subsequence n))
          J r F)
      atTop
      (nhds
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPathCovariance
          L.continuumMeasure J r F)) := by
  let Left :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftPathObservable
      J F
  let Right :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightPathObservable
      J r F
  let Product :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable
      J r F F
  have hIntegral :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp L.weakConvergence
  have hLeft := hIntegral Left
  have hRight := hIntegral Right
  have hProduct := hIntegral Product
  have hCov := hProduct.sub (hLeft.mul hRight)
  simpa [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPathCovariance,
    Left, Right, Product] using hCov

/-- The actual finite Wilson midpoint covariances along the Prokhorov subsequence
converge to the covariance of the corresponding fixed tests under the continuum
scalar path law. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.midpointWilsonSourceCovariance_tendsto_continuumPathCovariance
    (H : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J : Finset ℚ)
    (r : ℚ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          latticeSpacing (L.subsequence n) J r F)
      atTop
      (nhds
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPathCovariance
          L.continuumMeasure J r F)) := by
  have h := L.midpointPathCovariance_tendsto
    H N hN beta hbeta latticeSpacing J r F
  simpa only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eq_pathCovariance] using h

/-- A scale-independent Dobrushin ratio strictly below one forces the continuum
midpoint covariance at every fixed positive rational separation to vanish.
This is a conditional ultralocality statement: it does not assert that the
factorial Yang--Mills coupling sequence satisfies the uniform-ratio hypothesis. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.midpointPathCovariance_eq_zero_of_uniformGeometric_scaling
    (H : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 < r)
    (rhoBar : ℝ)
    (hrhoBar0 : 0 ≤ rhoBar)
    (hrhoBar1 : rhoBar < 1)
    (hRhoLe :
      ∀ᶠ n : ℕ in atTop,
        18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) ≤ rhoBar)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPathCovariance
        L.continuumMeasure J r F = 0 := by
  have hZero :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_tendsto_zero_of_uniformGeometric_scaling
      H N hN beta hbeta latticeSpacing latticeSpacing_pos
      latticeSpacing_tendsto_zero hreach J hJ r hr rhoBar
      hrhoBar0 hrhoBar1 hRhoLe F
  have hZeroSub := hZero.comp L.subsequence_strictMono.tendsto_atTop
  have hContinuum :=
    L.midpointWilsonSourceCovariance_tendsto_continuumPathCovariance
      H N hN beta hbeta latticeSpacing J r F
  exact tendsto_nhds_unique hContinuum hZeroSub

end

end MathlibAnalytic
end MGAP4D

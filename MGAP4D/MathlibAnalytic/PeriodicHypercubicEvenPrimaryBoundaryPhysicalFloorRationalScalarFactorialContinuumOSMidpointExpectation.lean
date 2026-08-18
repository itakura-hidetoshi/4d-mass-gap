import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialContinuumOSMidpointPairLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumOSBilinearForm
import Mathlib.Tactic

/-!
# Factorial continuum OS midpoint expectation identity

The preceding layer identifies the continuum probability laws of the translated OS symmetric pair
and the midpoint pair on the fixed finite carrier `(J → ℝ) × (J → ℝ)`.

Testing that law equality against the bounded-continuous product observable

`(u,v) ↦ F(u) * F(v)`

immediately gives the scalar midpoint expectation identity

`E[F(x(-(q+t))) F(x(q+t))] = E[F(x(-q)) F(x((q+t)+t))]`.

This is the analytic equality that will next be rewritten as the OS quadratic midpoint identity on
fixed-slot carriers.  No quotient descent, OS contraction, null-space preservation, semigroup,
Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The continuum translated OS quadratic integrand and its midpoint-resolved integrand have equal
expectation for every bounded-continuous fixed-slot observable. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_osMidpoint_expectation_eq
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    (∫ x,
        F (fun q : J => x (-(q.1 + t))) *
          F (fun q : J => x (q.1 + t))
      ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
      ∫ x,
        F (fun q : J => x (-q.1)) *
          F (fun q : J => x ((q.1 + t) + t))
        ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
  let P : C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
      J t
  let Q : C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
      J t
  let φ : ((∀ q : J, ℝ) × (∀ q : J, ℝ)) → ℝ :=
    fun p => F p.1 * F p.2
  have hφ : Continuous φ := by
    dsimp [φ]
    exact
      (F.continuous.comp continuous_fst).mul
        (F.continuous.comp continuous_snd)
  have hPM :=
    L.factorial_continuum_osShiftedPair_law_eq_midpoint
      H N hN beta hbeta J hJ t ht
  have hLaw :
      Measure.map P (L.continuumMeasure : Measure (ℚ → ℝ)) =
        Measure.map Q (L.continuumMeasure : Measure (ℚ → ℝ)) := by
    simpa [P, Q] using congrArg ProbabilityMeasure.toMeasure hPM
  calc
    (∫ x, F (fun q : J => x (-(q.1 + t))) * F (fun q : J => x (q.1 + t))
      ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
        ∫ p, φ p ∂Measure.map P (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      symm
      simpa [P, φ] using
        (MeasureTheory.integral_map
          P.measurable.aemeasurable hφ.aestronglyMeasurable)
    _ = ∫ p, φ p ∂Measure.map Q (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      rw [hLaw]
    _ = ∫ x, F (fun q : J => x (-q.1)) * F (fun q : J => x ((q.1 + t) + t))
        ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
      simpa [Q, φ] using
        (MeasureTheory.integral_map
          Q.measurable.aemeasurable hφ.aestronglyMeasurable)

end

end MathlibAnalytic
end MGAP4D

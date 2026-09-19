import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenDobrushinRandomScanFiniteResolventGeometric
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPlaquetteLocalBaseL1Separation
import Mathlib.Tactic

/-!
# Base-L1 geometric finite resolvent for singleton forcing

This file specializes the current finite random-scan Dobrushin resolvent
estimate to a single physical-link forcing site.

If the periodic link-base L1 distance from `target` to `source` is at least
`2 * D`, the plaquette-local path geometry from the preceding bridge gives
`D` steps of support separation.  A nonnegative singleton forcing of
amplitude `a` therefore satisfies

`w_M(source) <= rho^D / (1-rho) * a`

uniformly in the finite truncation length `M`, where
`rho = 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta`.

This is a certificate for the sparse compact-Wilson Dobrushin proxy.  It does
not identify that proxy with the continuous-vacuum remote kernel-section law,
and it asserts neither an infinite resolvent nor a mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_singletonBaseL1Resolvent
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- A nonnegative forcing profile concentrated at one physical link. -/
def periodicHypercubicEvenSingletonForcing
    {H : ℕ}
    (target : PeriodicHypercubicEvenEdge H)
    (amplitude : ℝ)
    (e : PeriodicHypercubicEvenEdge H) : ℝ :=
  if e = target then amplitude else 0

theorem periodicHypercubicEvenSingletonForcing_nonneg
    {H : ℕ}
    (target : PeriodicHypercubicEvenEdge H)
    (amplitude : ℝ)
    (hAmplitude : 0 ≤ amplitude) :
    ∀ e : PeriodicHypercubicEvenEdge H,
      0 ≤ periodicHypercubicEvenSingletonForcing target amplitude e := by
  intro e
  by_cases hEq : e = target
  · simp [periodicHypercubicEvenSingletonForcing, hEq, hAmplitude]
  · simp [periodicHypercubicEvenSingletonForcing, hEq]

theorem periodicHypercubicEvenSingletonForcing_eq_zero_off
    {H : ℕ}
    (target : PeriodicHypercubicEvenEdge H)
    (amplitude : ℝ) :
    ∀ e : PeriodicHypercubicEvenEdge H,
      e ∉ ({target} : Finset (PeriodicHypercubicEvenEdge H)) →
        periodicHypercubicEvenSingletonForcing target amplitude e = 0 := by
  intro e he
  have hNe : e ≠ target := by
    simpa using he
  simp [periodicHypercubicEvenSingletonForcing, hNe]

@[simp] theorem periodicHypercubicEven_sum_singletonForcing
    {H : ℕ}
    (target : PeriodicHypercubicEvenEdge H)
    (amplitude : ℝ) :
    (∑ e ∈ ({target} : Finset (PeriodicHypercubicEvenEdge H)),
      periodicHypercubicEvenSingletonForcing target amplitude e) = amplitude := by
  simp [periodicHypercubicEvenSingletonForcing]

/-- Singleton forcing inherits the separated-support geometric finite-resolvent
bound directly from a link-base periodic L1 lower bound. -/
theorem
    periodicHypercubicEvenSpecialUnitary_dobrushinRandomScanFiniteResolventProfile_singleton_le_geometric_of_two_mul_le_edgeBaseL1Distance
    (H N D : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (target source : PeriodicHypercubicEvenEdge H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H) target source)
    (amplitude : ℝ)
    (hAmplitude : 0 ≤ amplitude)
    (M : ℕ) :
    let Ddata :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    let w :=
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
        Ddata
        (periodicHypercubicEvenSingletonForcing target amplitude)
        M
    w source ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
          amplitude := by
  have hsep :
      periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy
        H D {target} {source} :=
    periodicHypercubicEven_singletons_plaquetteLocalSeparatedBy_of_two_mul_le_edgeBaseL1Distance
      H D target source hDistance
  have hGeom :=
    periodicHypercubicEvenSpecialUnitary_dobrushinRandomScanFiniteResolventProfile_le_geometric_of_supportsSeparatedBy
      H N D hH hN beta hBeta hThreshold
      {target} {source} hsep
      (periodicHypercubicEvenSingletonForcing target amplitude)
      (periodicHypercubicEvenSingletonForcing_nonneg
        target amplitude hAmplitude)
      (periodicHypercubicEvenSingletonForcing_eq_zero_off
        target amplitude)
      M source (by simp)
  simpa using hGeom

end

end MathlibAnalytic
end MGAP4D

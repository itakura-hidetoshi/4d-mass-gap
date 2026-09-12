import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceGeometricPrefixDomination
import Mathlib.Tactic

/-!
# Periodic separated-support geometric tails for finite heat-bath schedules

The current finite heat-bath route already gives a coefficient-loss-free
geometric bound for any `Nodup` schedule once the unrestricted influence
iterate prefix below a distance `D` vanishes exactly.  The periodic compact
`SU(N)` route already proves that exact prefix vanishing between genuinely
plaquette-local separated supports under the explicit finite-volume current
Dobrushin threshold.

This file composes those same-root facts.  A prescribed `Nodup` heat-bath
schedule whose length is `D + M` inherits the explicit geometric factor

`(18 * q(beta))^D / (1 - 18 * q(beta))`

between a target in the left support and a source in the right support.

This remains finite heat-bath/Dobrushin algebra.  No covariance decay,
continuum clustering, positive physical mass, OS Hamiltonian gap, or uniform
factorial-continuum Dobrushin threshold is asserted.  Heat-bath update count is
not identified with Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_heatBathScheduleGeometricTail
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Under the explicit finite-volume current compact `SU(N)` threshold, actual
plaquette-local support separation supplies the zero prefix needed by the
finite heat-bath schedule geometric domination theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteHeatBathScheduleInfluenceKernel_le_geometric_of_supportsSeparatedBy
    (H N D M : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (targets : List (PeriodicHypercubicEvenEdge H))
    (hNodup : targets.Nodup)
    (hLength : targets.length = D + M)
    (target : PeriodicHypercubicEvenEdge H)
    (htarget : target ∈ S)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    let data :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    finiteHeatBathScheduleInfluenceKernel
        data.influence targets target source ≤
      (18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) := by
  classical
  let C :=
    periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
  let data :=
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hBeta hThreshold
  change
    finiteHeatBathScheduleInfluenceKernel
        data.influence targets target source ≤
      (18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)
  have hStrict : data.coefficient < 1 := by
    simpa [data,
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using
      hThreshold
  have hPrefix :
      (∑ d ∈ Finset.range D,
        finiteInfluenceIterateKernel data.influence d target source) = 0 := by
    have hPrefixAndTail :=
      periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_prefix_zero_and_tail_le_geometric_of_supportsSeparatedBy
        H N D 0 hH hN beta hBeta hThreshold S T hsep
        target htarget source hsource
    simpa [data] using hPrefixAndTail.1
  have hSchedule :=
    continuous_compact_oriented_dobrushin_finiteHeatBathScheduleInfluenceKernel_le_geometric_of_nodup_prefix_zero
      C data hStrict D M targets hNodup hLength target source hPrefix
  simpa [C, data,
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using
    hSchedule

end

end MathlibAnalytic
end MGAP4D

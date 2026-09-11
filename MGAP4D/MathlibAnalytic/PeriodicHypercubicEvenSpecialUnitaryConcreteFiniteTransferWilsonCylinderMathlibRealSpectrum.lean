import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderExplicitJointResolventNeighborhood
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped InnerProductSpace Ring Topology

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

local instance wilsonCylinderMathlibRealSpectrumPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The repository's shifted-unit predicate is exactly Mathlib's native real
resolvent-set predicate for the genuine finite Wilson physical transfer
operator.  This is the normalization point at which the preceding Neumann
arguments enter Mathlib's standard spectral API. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_mem_real_resolventSet_iff
    (H N : ℕ) (hN : 0 < N) (z beta : ℝ) :
    z ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta) ↔
      IsUnit
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta) := by
  simpa [Algebra.algebraMap_eq_smul_one] using
    (spectrum.mem_resolventSet_iff
      (R := ℝ)
      (A := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
      (r := z)
      (a := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta))

/-- Equivalently, the same shifted-unit predicate is exclusion from Mathlib's
native real spectrum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_not_mem_real_spectrum_iff
    (H N : ℕ) (hN : 0 < N) (z beta : ℝ) :
    z ∉ spectrum ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta) ↔
      IsUnit
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta) := by
  simpa [Algebra.algebraMap_eq_smul_one] using
    (spectrum.notMem_iff
      (R := ℝ)
      (A := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
      (r := z)
      (a := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta))

/-- The genuine finite Wilson physical resolvent set is open in the ordinary
real spectral parameter, now as a direct instance of Mathlib's Banach-algebra
spectral theory. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_real_resolventSet_isOpen
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) :
    IsOpen
      (resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta)) := by
  exact
    spectrum.isOpen_resolventSet
      (𝕜 := ℝ)
      (A := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta)

/-- Dually, the real spectrum of the genuine finite Wilson physical transfer
operator is closed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_real_spectrum_isClosed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) :
    IsClosed
      (spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta)) := by
  exact
    spectrum.isClosed
      (𝕜 := ℝ)
      (A := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta)

/-- The explicit joint Neumann estimate from the physical vacuum becomes a
native Mathlib resolvent-set stability theorem: simultaneous motion of the real
spectral parameter and Wilson coupling stays in the resolvent set whenever the
ordinary weighted distance is below the inverse-resolvent norm radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_mem_real_resolventSet_of_joint_abs_lt
    (H N : ℕ) (hN : 0 < N)
    (z w beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hz : z ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta))
    (hnear :
      |w - z| +
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N * |gamma - beta| <
      ‖Ring.inverse
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta)‖⁻¹) :
    w ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN gamma) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_mem_real_resolventSet_iff]
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_abs_lt
      H N hN z w beta gamma hbeta hgamma
  · exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_mem_real_resolventSet_iff
        H N hN z beta).mp hz
  · exact hnear

/-- Every native real resolvent point has the canonical positive Neumann radius,
and that same radius controls a whole joint spectral-parameter/coupling
neighborhood inside Mathlib's resolvent sets. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_exists_positive_joint_real_resolvent_radius
    (H N : ℕ) (hN : 0 < N)
    (z beta : ℝ) (hbeta : 0 ≤ beta)
    (hz : z ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta)) :
    ∃ r : ℝ,
      0 < r ∧
      r =
        ‖Ring.inverse
          (z • (1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN beta)‖⁻¹ ∧
      ∀ w gamma : ℝ, 0 ≤ gamma →
        |w - z| +
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N * |gamma - beta| < r →
        w ∈ resolventSet ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN gamma) := by
  have hunit :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_mem_real_resolventSet_iff
      H N hN z beta).mp hz
  obtain ⟨r, hr, hr_eq, hres⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_exists_positive_joint_resolvent_radius
      H N hN z beta hbeta hunit
  refine ⟨r, hr, hr_eq, ?_⟩
  intro w gamma hgamma hnear
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_mem_real_resolventSet_iff]
  exact hres w gamma hgamma hnear

/-- At fixed Wilson coupling, the canonical inverse-resolvent norm radius is an
actual ordinary metric ball contained in Mathlib's real resolvent set.  This is
the quantitative local form underlying the abstract openness theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_exists_real_resolvent_metric_ball
    (H N : ℕ) (hN : 0 < N)
    (z beta : ℝ) (hbeta : 0 ≤ beta)
    (hz : z ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta)) :
    ∃ r : ℝ,
      0 < r ∧
      r =
        ‖Ring.inverse
          (z • (1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN beta)‖⁻¹ ∧
      Metric.ball z r ⊆
        resolventSet ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta) := by
  obtain ⟨r, hr, hr_eq, hjoint⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_exists_positive_joint_real_resolvent_radius
      H N hN z beta hbeta hz
  refine ⟨r, hr, hr_eq, ?_⟩
  intro w hw
  apply hjoint w beta hbeta
  have hdist : |w - z| < r := by
    simpa [Real.dist_eq] using hw
  simpa using hdist

/-- Audit-visible package: the exact finite Wilson physical transfer family has
entered Mathlib's native real spectral language, with both the abstract
open/closed topology and the sharper physical inverse-norm neighborhood. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonMathlibRealSpectrum_package
    (H N : ℕ) (hN : 0 < N) :
    (∀ beta : ℝ,
      IsOpen
        (resolventSet ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta))) ∧
    (∀ beta : ℝ,
      IsClosed
        (spectrum ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta))) ∧
    (∀ z beta : ℝ, 0 ≤ beta →
      z ∈ resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta) →
      ∃ r : ℝ, 0 < r ∧
        Metric.ball z r ⊆
          resolventSet ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN beta)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro beta
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_real_resolventSet_isOpen
        H N hN beta
  · intro beta
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_real_spectrum_isClosed
        H N hN beta
  · intro z beta hbeta hz
    obtain ⟨r, hr, _, hball⟩ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_exists_real_resolvent_metric_ball
        H N hN z beta hbeta hz
    exact ⟨r, hr, hball⟩

end
end MathlibAnalytic
end MGAP4D

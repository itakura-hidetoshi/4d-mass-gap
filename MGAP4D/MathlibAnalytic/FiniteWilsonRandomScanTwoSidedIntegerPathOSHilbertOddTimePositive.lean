import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertEvenTimePositive
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertOddTimePositive
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTransitionExpectation
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPythagorean
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHilbertRealization
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanRayleighContraction

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A single-link Wilson heat-bath conditional expectation has quadratic form
 equal to the squared Gibbs norm of its projected observable. -/
theorem finite_lattice_singleLinkHeatBathProjection_gibbsPairing_self_eq
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) f =
      L.gibbsPairingReal
        (L.singleLinkHeatBathProjection e f)
        (L.singleLinkHeatBathProjection e f) := by
  calc
    L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) f =
        L.gibbsPairingReal
          (L.singleLinkHeatBathProjection e
            (L.singleLinkHeatBathProjection e f)) f := by
          rw [finite_lattice_singleLinkHeatBathProjection_idempotent]
    _ = L.gibbsPairingReal
        (L.singleLinkHeatBathProjection e f)
        (L.singleLinkHeatBathProjection e f) :=
      finite_lattice_singleLinkHeatBath_gibbsPairing_projection_symm
        L e (L.singleLinkHeatBathProjection e f) f

/-- Every single-link Wilson heat-bath conditional expectation is positive for
 the finite Gibbs pairing. -/
theorem finite_lattice_singleLinkHeatBathProjection_gibbsPairing_self_nonneg
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    0 ≤ L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) f := by
  rw [finite_lattice_singleLinkHeatBathProjection_gibbsPairing_self_eq]
  rw [← finite_lattice_gibbsHilbert_norm_sq_embed]
  exact sq_nonneg _

/-- The actual normalized random-scan Wilson heat-bath sweep is positive for the
 finite Gibbs pairing, because it is a nonnegative average of positive
 single-link conditional-expectation projections. -/
theorem finite_lattice_randomScanHeatBathSweep_gibbsPairing_self_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (f : L.Configuration → ℝ) :
    0 ≤ L.gibbsPairingReal (L.randomScanHeatBathSweep f) f := by
  classical
  have hSweep :
      L.randomScanHeatBathSweep f =
        (Fintype.card L.Edge : ℝ)⁻¹ •
          (fun A =>
            ∑ e : L.Edge, L.singleLinkHeatBathProjection e f A) := by
    funext A
    simp [FiniteLatticeWilsonSystem.randomScanHeatBathSweep,
      FiniteLatticeWilsonSystem.singleLinkHeatBathOperator,
      FiniteLatticeWilsonSystem.singleLinkHeatBathProjection]
  have hSum :
      L.gibbsPairingReal
          (fun A =>
            ∑ e : L.Edge, L.singleLinkHeatBathProjection e f A) f =
        ∑ e : L.Edge,
          L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) f := by
    unfold FiniteLatticeWilsonSystem.gibbsPairingReal
    calc
      (∑ A : L.Configuration,
          L.gibbsProbabilityReal A *
            (∑ e : L.Edge, L.singleLinkHeatBathProjection e f A) * f A) =
        ∑ A : L.Configuration, ∑ e : L.Edge,
          L.gibbsProbabilityReal A *
            L.singleLinkHeatBathProjection e f A * f A := by
              apply Finset.sum_congr rfl
              intro A _hA
              rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ e : L.Edge, ∑ A : L.Configuration,
          L.gibbsProbabilityReal A *
            L.singleLinkHeatBathProjection e f A * f A := by
              rw [Finset.sum_comm]
  rw [hSweep, finite_lattice_gibbsPairingReal_smul_left, hSum]
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun e _he =>
      finite_lattice_singleLinkHeatBathProjection_gibbsPairing_self_nonneg
        L e f)

/-- The actual finite Wilson random-scan transition has nonnegative stationary
 quadratic form. -/
theorem finite_lattice_randomScanTransitionQuadraticNonnegative
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    LinearMarkovTransitionQuadraticNonnegative
      L.gibbsPMF L.randomScanTransitionPMF := by
  intro f
  rw [finite_lattice_finitePMFExpectationReal_gibbsPMF]
  simp_rw [finite_lattice_randomScanTransitionPMF_expectation]
  change 0 ≤ L.gibbsPairingReal (L.randomScanHeatBathSweep f) f
  exact finite_lattice_randomScanHeatBathSweep_gibbsPairing_self_nonneg L f

/-- The actual finite Wilson completed time-one temporal OS shift has
 nonnegative quadratic form. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShift_self_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShift x) x :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftContinuousLinearMap_self_nonneg
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) x

/-- At every odd natural time, the actual finite Wilson temporal OS quadratic
 form is the time-one form of the half-time translate. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add_self_add_one_eq
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup
          (n + n + 1) x) x =
      inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShift
          (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x))
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftSemigroup_add_self_add_one_eq
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n x

/-- Every odd-time member of the actual finite Wilson discrete temporal OS
 semigroup has nonnegative quadratic form. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add_self_add_one_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup
        (n + n + 1) x) x :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftSemigroup_add_self_add_one_nonneg
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n x

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumNormalizedCentered
import Mathlib.Tactic

/-!
# Same-root vacuum-orthogonal OS autocorrelation

This file starts the correlation / effective-mass route directly on the canonical same-root
factorial-Wilson / primary-scalar Prokhorov OS excitation carrier constructed by the regular
Hilbert direct limit.

For an exact vacuum-orthogonal excitation `x`, define

`Cₓ(t) = ⟪x, Tₜ x⟫_ℝ`.

Using only the already-constructed same-root real-time semigroup, its inner-product symmetry,
additive law, and contraction estimate, we prove:

* `Cₓ(0) = ‖x‖²`;
* `Cₓ(s+t) = ⟪Tₛx, Tₜx⟫_ℝ`;
* `Cₓ(t) ≥ 0`;
* `Cₓ` is antitone on nonnegative Euclidean time;
* `Cₓ((s+t)/2)² ≤ Cₓ(s) Cₓ(t)`.

No positive mass, exponential decay rate, spectral gap, numerical value, or equivalence with the
older abstract `PhysicalHilbert` carrier is assumed or imported.  In particular this package does
not prove strict positivity of the infrared decay rate; it puts the next quantitative question on
the exact same-root excitation carrier where a finite-Wilson estimate can be attached without a
carrier change.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Autocorrelation of an exact same-root vacuum-orthogonal excitation. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)
    (t : NNReal) : ℝ :=
  inner ℝ x (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x)

/-- Inner-product symmetry of the ambient same-root real OS semigroup descends exactly to the
vacuum-orthogonal excitation carrier. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x y : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x) y =
      inner ℝ x
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t y) := by
  change
    inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace) =
      inner ℝ
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (y : P.fixedSlotHilbertDirectLimitRegularSubspace))
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_symmetric
    t
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace)

/-- At zero Euclidean time the same-root excitation autocorrelation is the squared Hilbert norm. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x 0 = ‖x‖ ^ 2 := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
  rw [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_zero]
  exact real_inner_self_eq_norm_sq x

/-- Semigroup symmetry moves one time-evolution factor to the first slot. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_eq_inner
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x (s + t) =
      inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector s x)
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x) := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
  rw [← P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_add s t x]
  exact
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_inner_symmetric
      s x
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x)).symm

/-- Correlation at twice a time is exactly the squared norm of the evolved excitation. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_eq_norm_sq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x (t + t) =
      ‖P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x‖ ^ 2 := by
  rw [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_eq_inner t t x]
  exact real_inner_self_eq_norm_sq _

/-- Doubled-time correlations decrease under additional same-root Euclidean-time contraction. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_antitone
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {s t : NNReal}
    (hst : s ≤ t)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x (t + t) ≤
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x (s + s) := by
  rw [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_eq_norm_sq,
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_eq_norm_sq]
  have hop :
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x =
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (t - s)
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector s x) := by
    calc
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x =
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector ((t - s) + s) x := by
        rw [tsub_add_cancel_of_le hst]
      _ =
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (t - s)
            (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector s x) := by
        symm
        exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_add
          (t - s) s x
  rw [hop]
  have hnorm :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_norm_le
      (t - s)
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector s x)
  nlinarith [
    norm_nonneg
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (t - s)
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector s x)),
    norm_nonneg (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector s x)]

/-- The exact same-root excitation autocorrelation is antitone on nonnegative Euclidean time. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_antitone
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    Antitone (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x) := by
  intro s t hst
  have hhalf : s / 2 ≤ t / 2 := by gcongr
  have h :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_antitone
      hhalf x
  have hs : s / 2 + s / 2 = s := by
    apply NNReal.eq
    norm_num
  have ht : t / 2 + t / 2 = t := by
    apply NNReal.eq
    norm_num
  simpa only [hs, ht] using h

/-- Every exact same-root excitation autocorrelation is nonnegative. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    0 ≤ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x t := by
  have hhalf :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_eq_norm_sq
      (t / 2) x
  have ht : t / 2 + t / 2 = t := by
    apply NNReal.eq
    norm_num
  rw [ht] at hhalf
  rw [hhalf]
  positivity

/-- Multiplicative midpoint inequality directly on the same-root excitation carrier.  This is the
zero-assumption log-convex-type input needed before constructing an unregularized effective mass. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_midpoint_sq_le_mul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x ((s + t) / 2) ^ 2 ≤
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x s *
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x t := by
  let u := P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (s / 2) x
  let v := P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (t / 2) x
  have hmidTime : s / 2 + t / 2 = (s + t) / 2 := by
    apply NNReal.eq
    ring
  have hsTime : s / 2 + s / 2 = s := by
    apply NNReal.eq
    ring
  have htTime : t / 2 + t / 2 = t := by
    apply NNReal.eq
    ring
  have hmid :
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x ((s + t) / 2) =
        inner ℝ u v := by
    rw [← hmidTime]
    exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_eq_inner
      (s / 2) (t / 2) x
  have hsCorr :
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x s = ‖u‖ ^ 2 := by
    rw [← hsTime]
    exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_eq_norm_sq
      (s / 2) x
  have htCorr :
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x t = ‖v‖ ^ 2 := by
    rw [← htTime]
    exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_eq_norm_sq
      (t / 2) x
  have hcauchy : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have hinnerNonneg : 0 ≤ inner ℝ u v := by
    rw [← hmid]
    exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_nonneg
      ((s + t) / 2) x
  have hprodNonneg : 0 ≤ ‖u‖ * ‖v‖ :=
    mul_nonneg (norm_nonneg u) (norm_nonneg v)
  have hfactor :
      0 ≤ (‖u‖ * ‖v‖ - inner ℝ u v) *
        (‖u‖ * ‖v‖ + inner ℝ u v) :=
    mul_nonneg (sub_nonneg.mpr hcauchy)
      (add_nonneg hprodNonneg hinnerNonneg)
  rw [hmid, hsCorr, htCorr]
  nlinarith

/-- Collected qualitative same-root correlation package.  The strict-positive infrared lower bound
is deliberately not included: it remains the next model-derived quantitative obligation. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x 0 = ‖x‖ ^ 2 ∧
      Antitone (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x) ∧
      (∀ t : NNReal,
        0 ≤ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x t) ∧
      (∀ s t : NNReal,
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x ((s + t) / 2) ^ 2 ≤
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x s *
            P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x t) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_zero x,
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_antitone x,
    fun t => P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_nonneg t x,
    fun s t =>
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_midpoint_sq_le_mul s t x⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D

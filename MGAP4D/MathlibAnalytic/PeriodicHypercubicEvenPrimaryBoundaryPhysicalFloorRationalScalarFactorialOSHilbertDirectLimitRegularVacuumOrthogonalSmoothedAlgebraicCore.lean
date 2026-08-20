import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularSmoothedAlgebraicCore
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumNormalizedCentered
import Mathlib.Tactic

/-!
# Dense centered smoothed algebraic core of the same-root excitation sector

The preceding same-root layers establish two complementary facts:

* strictly positive rational OS time sends every completed direct-limit vector into the canonical
  zero-time regular sector;
* positive-time translates of the actual algebraic fixed-slot direct-limit carrier are dense in
  that regular sector.

The normalized constant vacuum and exact centering map are already available on the same carrier.
This file combines those constructions and passes the smoothed algebraic regular core to the exact
vacuum-orthogonal excitation Hilbert space.

The only estimate needed for centering is the elementary Hilbert bound

`‖center x - center y‖ ≤ 2 ‖x - y‖`.

It follows from Cauchy--Schwarz and `‖Ω‖ = 1`; no spectral projection machinery is required.  Thus
centering a dense positive-time-smoothed algebraic family remains dense in the exact same-root
`Ω⊥` carrier.

This is a carrier/core theorem only.  It does not assert that the excitation sector is nontrivial,
that a particular Wilson cylinder survives positive time, or that the canonical infrared mass is
strictly positive.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
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

/-- Centering is `2`-Lipschitz on the canonical regular Hilbert sector.  The deliberately simple
constant is sufficient for transferring density to `Ω⊥`. -/
theorem fixedSlotHilbertDirectLimitRegularCentered_sub_norm_le_two
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖P.fixedSlotHilbertDirectLimitRegularCentered x -
        P.fixedSlotHilbertDirectLimitRegularCentered y‖ ≤
      2 * ‖x - y‖ := by
  have hcoeff :
      ‖P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient x -
          P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient y‖ ≤
        ‖x - y‖ := by
    change
      ‖inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum x -
          inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum y‖ ≤
        ‖x - y‖
    rw [← inner_sub_right]
    calc
      ‖inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum (x - y)‖ ≤
          ‖P.fixedSlotHilbertDirectLimitRegularVacuum‖ * ‖x - y‖ :=
        norm_inner_le_norm _ _
      _ = ‖x - y‖ := by
        rw [P.fixedSlotHilbertDirectLimitRegularVacuum_norm, one_mul]
  calc
    ‖P.fixedSlotHilbertDirectLimitRegularCentered x -
        P.fixedSlotHilbertDirectLimitRegularCentered y‖ =
      ‖(x - y) -
        (P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient x -
          P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient y) •
            P.fixedSlotHilbertDirectLimitRegularVacuum‖ := by
        unfold fixedSlotHilbertDirectLimitRegularCentered
        congr 1
        module
    _ ≤ ‖x - y‖ +
        ‖(P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient x -
          P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient y) •
            P.fixedSlotHilbertDirectLimitRegularVacuum‖ :=
      norm_sub_le _ _
    _ = ‖x - y‖ +
        ‖P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient x -
          P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient y‖ := by
      rw [norm_smul, P.fixedSlotHilbertDirectLimitRegularVacuum_norm, mul_one]
    _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add_right hcoeff _
    _ = 2 * ‖x - y‖ := by ring

/-- A positive-time-smoothed algebraic vector, regarded canonically as a regular vector. -/
noncomputable def fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicRegular
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (y : P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ⟨y.1,
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet_subset_regularSubspace y.2⟩

/-- Center a positive-time-smoothed algebraic regular vector and corestrict it to exact `Ω⊥`. -/
noncomputable def fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedAlgebraicExcitation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (y : P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet) :
    P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
  ⟨P.fixedSlotHilbertDirectLimitRegularCentered
      (P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicRegular y),
    P.fixedSlotHilbertDirectLimitRegularCentered_mem_vacuumOrthogonal
      (P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicRegular y)⟩

/-- The exact excitation-core set obtained by centering all positive-time-smoothed algebraic
fixed-slot states. -/
def fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedAlgebraicExcitationSet
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Set P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
  Set.range P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedAlgebraicExcitation

/-- Every exact same-root excitation is in the closure of centered positive-time-smoothed algebraic
fixed-slot states.  This is the dense `Ω⊥` core statement. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mem_closure_centeredSmoothedAlgebraic
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (ξ : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    ξ ∈ closure
      P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedAlgebraicExcitationSet := by
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  have hxcl :
      ((ξ.1 : P.fixedSlotHilbertDirectLimitRegularSubspace) :
        P.fixedSlotHilbertDirectLimitCompletion) ∈
      closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet :=
    P.fixedSlotHilbertDirectLimitRegularSubspace_subset_closure_smoothedAlgebraic ξ.1.2
  obtain ⟨y, hy, hdist⟩ :=
    (Metric.mem_closure_iff.1 hxcl) (ε / 2) (half_pos hε)
  let ys : P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet := ⟨y, hy⟩
  let yr : P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicRegular ys
  let η : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
    P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedAlgebraicExcitation ys
  refine ⟨η, ?_, ?_⟩
  · exact ⟨ys, rfl⟩
  · have hyr : ‖yr - ξ.1‖ < ε / 2 := by
      change
        ‖y - ((ξ.1 : P.fixedSlotHilbertDirectLimitRegularSubspace) :
          P.fixedSlotHilbertDirectLimitCompletion)‖ < ε / 2
      simpa only [dist_eq_norm, norm_sub_rev] using hdist
    have hcenter := P.fixedSlotHilbertDirectLimitRegularCentered_sub_norm_le_two yr ξ.1
    have hcenter' :
        ‖P.fixedSlotHilbertDirectLimitRegularCentered yr - ξ.1‖ ≤
          2 * ‖yr - ξ.1‖ := by
      simpa only [
        P.fixedSlotHilbertDirectLimitRegularCentered_eq_self_of_mem_vacuumOrthogonal
          ξ.1 ξ.2] using hcenter
    have hη :
        (η.1 : P.fixedSlotHilbertDirectLimitRegularSubspace) =
          P.fixedSlotHilbertDirectLimitRegularCentered yr := by
      rfl
    rw [dist_eq_norm, norm_sub_rev]
    change ‖(η.1 : P.fixedSlotHilbertDirectLimitRegularSubspace) - ξ.1‖ < ε
    rw [hη]
    calc
      ‖P.fixedSlotHilbertDirectLimitRegularCentered yr - ξ.1‖ ≤
          2 * ‖yr - ξ.1‖ := hcenter'
      _ < 2 * (ε / 2) := mul_lt_mul_of_pos_left hyr (by norm_num)
      _ = ε := by ring

/-- Equivalently, the centered positive-time-smoothed algebraic excitation core has full closure in
exact same-root `Ω⊥`. -/
theorem fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedAlgebraicExcitationSet_closure_eq_univ
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    closure P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedAlgebraicExcitationSet =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro ξ
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mem_closure_centeredSmoothedAlgebraic ξ

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D

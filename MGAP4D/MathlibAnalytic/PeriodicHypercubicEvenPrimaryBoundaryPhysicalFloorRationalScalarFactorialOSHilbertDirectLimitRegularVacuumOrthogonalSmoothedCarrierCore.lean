import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitCylinderReflectionFormBridge
import Mathlib.Tactic

/-!
# Dense centered positive-time-smoothed literal cylinder core

The preceding same-root layers provide two complementary ingredients:

* the exact finite-Wilson / continuum-reflection-form bridge for literal bounded-continuous
  fixed-slot cylinders; and
* a dense centered positive-time-smoothed algebraic core of the exact vacuum-orthogonal regular
  Hilbert carrier.

For a future model-derived quantitative estimate it is preferable to work on literal cylinders,
not arbitrary vectors in a finite-slot Hilbert completion.  This file proves that no density is lost
by making that restriction.

Every finite-slot Hilbert vector is approximated by a literal wrapped cylinder because the
separated OS quotient is dense in its Hilbert completion.  The canonical finite-slot Hilbert
embedding into the completed algebraic direct limit is an isometry, and positive rational-time
translation is a contraction.  Hence every positive-time-smoothed algebraic vector is approximated
by a positive-time translate of a literal cylinder state.

Combining this with the already-canonical regular-core density theorem and the `2`-Lipschitz
centering estimate gives a literal-cylinder dense core in the exact same-root excitation carrier:

`closure { center (T_s x_F) | s > 0, F literal fixed-slot cylinder } = univ`.

Thus a future scale-uniform finite-Wilson quantitative estimate may be proved directly on actual
bounded-continuous cylinders and then extended by continuity/density.  No non-collapse statement,
positive variance floor, decay constant, positive mass, or old-carrier identification is asserted
here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology UniformSpace
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

/-- Canonical isometric insertion of one finite-slot Hilbert sector into the completed algebraic
same-root direct limit. -/
noncomputable def fixedSlotHilbertDirectLimitLinearIsometry
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    P.fixedSlotIndexedHilbert J →ₗᵢ[ℝ]
      P.fixedSlotHilbertDirectLimitCompletion :=
  (UniformSpace.Completion.toComplₗᵢ :
      P.fixedSlotHilbertAlgebraicDirectLimit →ₗᵢ[ℝ]
        P.fixedSlotHilbertDirectLimitCompletion).comp
    (P.fixedSlotHilbertAlgebraicLinearIsometry J)

@[simp]
theorem fixedSlotHilbertDirectLimitLinearIsometry_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertDirectLimitLinearIsometry J x =
      ((P.fixedSlotHilbertAlgebraicLinearIsometry J x :
          P.fixedSlotHilbertAlgebraicDirectLimit) :
        P.fixedSlotHilbertDirectLimitCompletion) :=
  rfl

/-- The literal cylinder state from the previous bridge is exactly the canonical isometric
insertion of its fixed-slot Hilbert state. -/
@[simp]
theorem fixedSlotHilbertDirectLimitLinearIsometry_hilbertState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitLinearIsometry J
        ((P.fixedSlotDataOfIndex J).hilbertState F) =
      P.fixedSlotHilbertDirectLimitCarrierState J F :=
  rfl

/-- Every algebraic direct-limit vector can be approximated arbitrarily well in the completed
direct limit by a literal fixed-slot cylinder state. -/
theorem fixedSlotHilbertDirectLimit_algebraic_carrier_approximation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier,
        dist (P.fixedSlotHilbertDirectLimitCarrierState J F)
          (z : P.fixedSlotHilbertDirectLimitCompletion) < ε := by
  obtain ⟨J, x, hx⟩ := P.fixedSlotHilbertAlgebraic_exists_representation z
  obtain ⟨u, hu⟩ :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk u
  refine ⟨J, F, ?_⟩
  rw [← hx]
  change
    dist
      (P.fixedSlotHilbertDirectLimitLinearIsometry J
        ((P.fixedSlotDataOfIndex J).hilbertState F))
      (P.fixedSlotHilbertDirectLimitLinearIsometry J x) < ε
  rw [LinearIsometry.dist_map]
  change dist x ((P.fixedSlotDataOfIndex J).hilbertState F) < ε at hu
  simpa only [dist_comm] using hu

/-- Positive rational-time translates of literal fixed-slot cylinders. -/
def fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Set P.fixedSlotHilbertDirectLimitCompletion :=
  {y | ∃ s : NNRat, 0 < s ∧
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier,
        y = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          (P.fixedSlotHilbertDirectLimitCarrierState J F)}

/-- Every positive-time-smoothed literal cylinder is automatically in the canonical regular
sector. -/
theorem fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet_subset_regularSubspace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet ⊆
      P.fixedSlotHilbertDirectLimitRegularSubspace := by
  rintro y ⟨s, hs, J, F, rfl⟩
  exact
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_mem_regularSubspace_of_pos
      s hs (P.fixedSlotHilbertDirectLimitCarrierState J F)

/-- At a fixed positive rational time, every smoothed algebraic vector can be approximated by a
smoothed literal cylinder state. -/
theorem fixedSlotHilbertDirectLimit_positiveTime_carrier_approximation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat) (hs : 0 < s)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier,
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (P.fixedSlotHilbertDirectLimitCarrierState J F) ∈
          P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet ∧
        dist
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (z : P.fixedSlotHilbertDirectLimitCompletion))
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (P.fixedSlotHilbertDirectLimitCarrierState J F)) < ε := by
  obtain ⟨J, F, hdist⟩ :=
    P.fixedSlotHilbertDirectLimit_algebraic_carrier_approximation z ε hε
  refine ⟨J, F, ?_, ?_⟩
  · exact ⟨s, hs, J, F, rfl⟩
  · calc
      dist
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (z : P.fixedSlotHilbertDirectLimitCompletion))
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (P.fixedSlotHilbertDirectLimitCarrierState J F)) =
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          ((z : P.fixedSlotHilbertDirectLimitCompletion) -
            P.fixedSlotHilbertDirectLimitCarrierState J F)‖ := by
              rw [dist_eq_norm, map_sub]
      _ ≤ ‖(z : P.fixedSlotHilbertDirectLimitCompletion) -
            P.fixedSlotHilbertDirectLimitCarrierState J F‖ :=
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le s _
      _ = dist
          (z : P.fixedSlotHilbertDirectLimitCompletion)
          (P.fixedSlotHilbertDirectLimitCarrierState J F) := by
            rw [dist_eq_norm]
      _ = dist
          (P.fixedSlotHilbertDirectLimitCarrierState J F)
          (z : P.fixedSlotHilbertDirectLimitCompletion) := dist_comm _ _
      _ < ε := hdist

/-- Every positive-time-smoothed algebraic vector lies in the closure of the positive-time-smoothed
literal-cylinder set. -/
theorem fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet_subset_closure_smoothedCarrier
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet ⊆
      closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet := by
  rintro y ⟨s, hs, z, rfl⟩
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨J, F, hmem, hdist⟩ :=
    P.fixedSlotHilbertDirectLimit_positiveTime_carrier_approximation
      s hs z ε hε
  exact
    ⟨P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (P.fixedSlotHilbertDirectLimitCarrierState J F), hmem, hdist⟩

/-- The literal positive-time-smoothed cylinder family is already dense in the whole canonical
regular sector. -/
theorem fixedSlotHilbertDirectLimitRegularSubspace_subset_closure_smoothedCarrier
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    (P.fixedSlotHilbertDirectLimitRegularSubspace :
      Set P.fixedSlotHilbertDirectLimitCompletion) ⊆
      closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet := by
  intro x hx
  have hxalg : x ∈ closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet :=
    P.fixedSlotHilbertDirectLimitRegularSubspace_subset_closure_smoothedAlgebraic hx
  have hsubset :
      P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet ⊆
        closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet :=
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet_subset_closure_smoothedCarrier
  exact (closure_minimal hsubset isClosed_closure) hxalg

/-- A positive-time-smoothed literal cylinder, regarded canonically as a regular vector. -/
noncomputable def fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierRegular
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (y : P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ⟨y.1,
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet_subset_regularSubspace y.2⟩

/-- Center a positive-time-smoothed literal cylinder and corestrict it to exact `Ω⊥`. -/
noncomputable def fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (y : P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet) :
    P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
  ⟨P.fixedSlotHilbertDirectLimitRegularCentered
      (P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierRegular y),
    P.fixedSlotHilbertDirectLimitRegularCentered_mem_vacuumOrthogonal
      (P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierRegular y)⟩

/-- Exact excitation-core set made only from centered positive-time translates of literal
fixed-slot cylinders. -/
def fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitationSet
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Set P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
  Set.range P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitation

/-- Every exact same-root excitation is in the closure of centered positive-time-smoothed literal
cylinder states. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mem_closure_centeredSmoothedCarrier
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (ξ : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    ξ ∈ closure
      P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitationSet := by
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  have hxcl :
      ((ξ.1 : P.fixedSlotHilbertDirectLimitRegularSubspace) :
        P.fixedSlotHilbertDirectLimitCompletion) ∈
      closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet :=
    P.fixedSlotHilbertDirectLimitRegularSubspace_subset_closure_smoothedCarrier ξ.1.2
  obtain ⟨y, hy, hdist⟩ :=
    (Metric.mem_closure_iff.1 hxcl) (ε / 2) (half_pos hε)
  let ys : P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet := ⟨y, hy⟩
  let yr : P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierRegular ys
  let η : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
    P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitation ys
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

/-- Equivalently, centered positive-time-smoothed literal cylinders have full closure in the exact
same-root excitation Hilbert carrier. -/
theorem fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitationSet_closure_eq_univ
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    closure P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitationSet =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro ξ
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mem_closure_centeredSmoothedCarrier ξ

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D

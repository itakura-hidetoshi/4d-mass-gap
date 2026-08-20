import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonal
import Mathlib.Tactic

/-!
# Normalized same-root vacuum, centered decomposition, and excitation semigroup

The previous package constructs the canonical constant vacuum directly from the same Wilson /
primary-scalar Prokhorov OS root, proves that the real `C₀` semigroup fixes it, identifies its
closed Hamiltonian energy as zero, and constructs the exact vacuum-orthogonal closed Hamiltonian
sector.

This file adds the normalization and decomposition layer needed before any coercive mass-gap
transport.  The key point is that the vacuum is represented by the literal constant-one cylinder,
so its fixed-slot OS norm is exactly the expectation of `1`, hence exactly one because the
continuum law is a probability measure.  The finite-slot Hilbert embedding, algebraic direct-limit
embedding, and completion embedding are all isometric, so the same vector has norm one in the
regular completed carrier.

We then center arbitrary regular vectors against this normalized vacuum, prove exact orthogonal
membership and decomposition, show centering commutes with the original real OS semigroup, and
corestrict the semigroup pointwise to the canonical excitation Hilbert carrier.  Finally we expose
the exact ambient Rayleigh expression of the restricted graph-closed Hamiltonian.

No positive mass lower bound, spectral gap, numerical mass value, or identification with the older
abstract `PhysicalHilbert` carrier is assumed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology Set
open scoped InnerProductSpace LinearPMap

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

/-- At the empty fixed slot, the literal constant-one vacuum cylinder has OS inner square one. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuumCarrier_inner_self
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    inner ℝ P.fixedSlotHilbertDirectLimitVacuumCarrier
        P.fixedSlotHilbertDirectLimitVacuumCarrier = 1 := by
  rw [(P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).inner_eq_fixedSlotOSBilinForm]
  rw [L.fixedSlotOSBilinForm_apply]
  simp only [P.fixedSlotDataOfIndex_slots,
    fixedSlotHilbertDirectLimitVacuumIndex_val,
    P.fixedSlotHilbertDirectLimitVacuumCarrier_observable]
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  simp only [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply]
  simp

/-- The empty-slot vacuum cylinder has seminorm exactly one before OS separation. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuumCarrier_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    ‖P.fixedSlotHilbertDirectLimitVacuumCarrier‖ = 1 := by
  have hsq : ‖P.fixedSlotHilbertDirectLimitVacuumCarrier‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact P.fixedSlotHilbertDirectLimitVacuumCarrier_inner_self
  nlinarith [norm_nonneg P.fixedSlotHilbertDirectLimitVacuumCarrier]

/-- The fixed-slot Hilbert state of the constant cylinder is normalized. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuumHilbertState_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    ‖(P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).hilbertState
        P.fixedSlotHilbertDirectLimitVacuumCarrier‖ = 1 := by
  change
    ‖(UniformSpace.Completion.toComplₗᵢ :
      (P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).Separated →ₗᵢ[ℝ]
        UniformSpace.Completion
          (P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).Separated)
      ((P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).osClass
        P.fixedSlotHilbertDirectLimitVacuumCarrier)‖ = 1
  rw [LinearIsometry.norm_map]
  change ‖SeparationQuotient.mk P.fixedSlotHilbertDirectLimitVacuumCarrier‖ = 1
  rw [SeparationQuotient.norm_mk]
  exact P.fixedSlotHilbertDirectLimitVacuumCarrier_norm

/-- The algebraic direct-limit representative of the constant vacuum is normalized. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuumAlgebraic_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    ‖P.fixedSlotHilbertDirectLimitVacuumAlgebraic‖ = 1 := by
  unfold fixedSlotHilbertDirectLimitVacuumAlgebraic
  change
    ‖P.fixedSlotHilbertAlgebraicLinearIsometry fixedSlotHilbertDirectLimitVacuumIndex
      ((P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).hilbertState
        P.fixedSlotHilbertDirectLimitVacuumCarrier)‖ = 1
  rw [LinearIsometry.norm_map]
  exact P.fixedSlotHilbertDirectLimitVacuumHilbertState_norm

/-- The completed same-root constant vacuum has norm one. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuum_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    ‖P.fixedSlotHilbertDirectLimitVacuum‖ = 1 := by
  unfold fixedSlotHilbertDirectLimitVacuum
  rw [UniformSpace.Completion.norm_coe]
  exact P.fixedSlotHilbertDirectLimitVacuumAlgebraic_norm

/-- The canonical vacuum is normalized in the actual regular Hilbert sector. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuum_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    ‖P.fixedSlotHilbertDirectLimitRegularVacuum‖ = 1 := by
  change ‖P.fixedSlotHilbertDirectLimitVacuum‖ = 1
  exact P.fixedSlotHilbertDirectLimitVacuum_norm

/-- Hence the canonical regular vacuum is nonzero. -/
theorem fixedSlotHilbertDirectLimitRegularVacuum_ne_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularVacuum ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  simpa using hnorm

/-- The normalized vacuum has self-inner-product one in the regular Hilbert carrier. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuum_inner_self
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum
        P.fixedSlotHilbertDirectLimitRegularVacuum = 1 := by
  rw [real_inner_self_eq_norm_sq, P.fixedSlotHilbertDirectLimitRegularVacuum_norm]
  norm_num

/-- Vacuum coefficient of an arbitrary regular same-root OS vector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumCoefficient
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) : ℝ :=
  inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum x

/-- Center a regular vector by subtracting its normalized vacuum component. -/
noncomputable def fixedSlotHilbertDirectLimitRegularCentered
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  x - P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient x •
    P.fixedSlotHilbertDirectLimitRegularVacuum

/-- Centering removes the vacuum coefficient exactly. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuum_inner_centered
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum
      (P.fixedSlotHilbertDirectLimitRegularCentered x) = 0 := by
  simp only [fixedSlotHilbertDirectLimitRegularCentered,
    fixedSlotHilbertDirectLimitRegularVacuumCoefficient]
  change
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
      ((x : P.fixedSlotHilbertDirectLimitCompletion) -
        inner ℝ P.fixedSlotHilbertDirectLimitVacuum
            (x : P.fixedSlotHilbertDirectLimitCompletion) •
          P.fixedSlotHilbertDirectLimitVacuum) = 0
  rw [inner_sub_right, inner_smul_right]
  rw [real_inner_self_eq_norm_sq, P.fixedSlotHilbertDirectLimitVacuum_norm]
  simp

/-- Every centered regular vector belongs to the canonical excitation sector. -/
theorem fixedSlotHilbertDirectLimitRegularCentered_mem_vacuumOrthogonal
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularCentered x ∈
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal := by
  rw [P.mem_fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_iff]
  exact P.fixedSlotHilbertDirectLimitRegularVacuum_inner_centered x

/-- Exact vacuum plus excitation decomposition of every regular vector. -/
theorem fixedSlotHilbertDirectLimitRegular_vacuum_add_centered
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient x •
        P.fixedSlotHilbertDirectLimitRegularVacuum +
      P.fixedSlotHilbertDirectLimitRegularCentered x = x := by
  simp [fixedSlotHilbertDirectLimitRegularCentered]

/-- A vector already orthogonal to the vacuum is fixed by centering. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularCentered_eq_self_of_mem_vacuumOrthogonal
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (hx : x ∈ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal) :
    P.fixedSlotHilbertDirectLimitRegularCentered x = x := by
  have hinner :=
    (P.mem_fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_iff x).mp hx
  simp [fixedSlotHilbertDirectLimitRegularCentered,
    fixedSlotHilbertDirectLimitRegularVacuumCoefficient, hinner]

/-- The real OS semigroup preserves the vacuum coefficient exactly. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumCoefficient_timeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) =
      P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient x := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumCoefficient
  calc
    inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) =
      inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          P.fixedSlotHilbertDirectLimitRegularVacuum) x := by
        symm
        exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_symmetric
          t P.fixedSlotHilbertDirectLimitRegularVacuum x
    _ = inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum x := by
      rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_vacuum]

/-- Centering commutes with the original real same-root OS semigroup. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_centered
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularCentered x) =
      P.fixedSlotHilbertDirectLimitRegularCentered
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) := by
  unfold fixedSlotHilbertDirectLimitRegularCentered
  rw [map_sub, map_smul]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_vacuum]
  rw [P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient_timeTranslate]

/-- Pointwise real-time action corestricted to the complete vacuum-orthogonal excitation carrier. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
  ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace),
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_timeTranslate t
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace) x.property⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    ((P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
      P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :=
  rfl

/-- The excitation-sector real-time action is contractive in the inherited Hilbert norm. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    ‖P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x‖ ≤ ‖x‖ := by
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le t
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)

/-- Zero time is the identity on the excitation carrier. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector 0 x = x := by
  apply Subtype.ext
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_zero_apply
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)

/-- Additive semigroup law after exact corestriction to the excitation carrier. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector s
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x) =
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (s + t) x := by
  apply Subtype.ext
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply s t
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)

/-- Exact ambient Rayleigh expression of the graph-closed Hamiltonian restricted to excitations. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonian_rayleigh_ambient
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
    inner ℝ
        (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace)
        (((P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonian x :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace)) =
      inner ℝ
        (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x)) := by
  rw [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonian_apply]

/-- Coercive lower-bound statement on the exact same-root excitation Hamiltonian domain.  This is a
property, not an assumption installed by the construction. -/
def FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) : Prop :=
  ∀ x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain,
    m * ‖((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)‖ ^ 2 ≤
      inner ℝ
        (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))

/-- Collected normalization / centered-excitation package. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumNormalizedCentered_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    ‖P.fixedSlotHilbertDirectLimitRegularVacuum‖ = 1 ∧
    P.fixedSlotHilbertDirectLimitRegularVacuum ≠ 0 ∧
    (∀ x : P.fixedSlotHilbertDirectLimitRegularSubspace,
      P.fixedSlotHilbertDirectLimitRegularCentered x ∈
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal) ∧
    (∀ (t : NNReal) (x : P.fixedSlotHilbertDirectLimitRegularSubspace),
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularCentered x) =
        P.fixedSlotHilbertDirectLimitRegularCentered
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x)) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularVacuum_norm,
    P.fixedSlotHilbertDirectLimitRegularVacuum_ne_zero,
    P.fixedSlotHilbertDirectLimitRegularCentered_mem_vacuumOrthogonal,
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_centered⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
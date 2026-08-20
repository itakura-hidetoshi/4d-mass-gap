import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularClosedGeneratorIdentification
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic

/-!
# Canonical vacuum and vacuum-orthogonal sector of the same-root regular factorial OS Hilbert space

The regular factorial OS `C₀` semigroup is already constructed directly from the same Wilson /
primary-scalar Prokhorov root, and its actual right generator is already identified with the
nonnegative self-adjoint graph-closed Hamiltonian.  This file now isolates the canonical vacuum
inside that same carrier rather than importing an abstract vacuum from the older physical OS
interface.

The vacuum is the direct-limit class of the constant-one cylinder in the empty finite slot sector.
Because translation of the empty slot set is again empty and translation of the constant-one
observable is literally constant one, the rational OS semigroup fixes this vector exactly.  The
canonical `NNRat -> NNReal` extension then fixes it at every nonnegative real time.  Consequently
its actual right-generator value is zero, so the closed Hamiltonian annihilates it by the generator
identification package.

We then define the vacuum line and its orthogonal complement, prove invariance of the excitation
sector under the original OS semigroup, prove that the graph-closed Hamiltonian maps its domain
into that orthogonal sector, and package the exact closed-domain restriction.

No vacuum invariance, generator value, spectral gap, or mass bound is assumed.  The vacuum facts are
all derived from the literal constant cylinder on the same continuum root.
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

/-- The empty finite nonnegative rational slot sector.  It is the canonical home of the constant
vacuum cylinder. -/
def fixedSlotHilbertDirectLimitVacuumIndex : PrimaryScalarFiniteNonnegativeSlotIndex :=
  ⟨∅, by simp⟩

@[simp]
theorem fixedSlotHilbertDirectLimitVacuumIndex_val :
    fixedSlotHilbertDirectLimitVacuumIndex.1 = (∅ : Finset ℚ) :=
  rfl

/-- Positive rational time translation fixes the empty slot index exactly. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuumIndex_timeTranslate
    (t : ℚ) (ht : 0 ≤ t) :
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht
        fixedSlotHilbertDirectLimitVacuumIndex =
      fixedSlotHilbertDirectLimitVacuumIndex := by
  apply Subtype.ext
  simp [fixedSlotHilbertDirectLimitVacuumIndex,
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate]

/-- Constant-one wrapped OS cylinder in the empty slot sector. -/
noncomputable def fixedSlotHilbertDirectLimitVacuumCarrier
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    (P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).FixedSlotCarrier :=
  ⟨1⟩

@[simp]
theorem fixedSlotHilbertDirectLimitVacuumCarrier_observable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitVacuumCarrier.observable = 1 :=
  rfl

/-- Translating the empty-slot constant cylinder still has constant-one observable. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuumCarrier_timeTranslate_observable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    ((P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).fixedSlotCarrierTimeTranslate
        t ht P.fixedSlotHilbertDirectLimitVacuumCarrier).observable = 1 := by
  rw [fixedSlotCarrierTimeTranslate_observable]
  ext v
  rfl

/-- Algebraic direct-limit representative of the canonical constant vacuum. -/
noncomputable def fixedSlotHilbertDirectLimitVacuumAlgebraic
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertAlgebraicDirectLimit :=
  P.fixedSlotHilbertAlgebraicOf fixedSlotHilbertDirectLimitVacuumIndex
    ((P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).hilbertState
      P.fixedSlotHilbertDirectLimitVacuumCarrier)

/-- The descended algebraic rational-time operator fixes the constant vacuum representative. -/
theorem fixedSlotHilbertAlgebraicTimeTranslate_vacuumAlgebraic
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.fixedSlotHilbertAlgebraicTimeTranslate t ht
        P.fixedSlotHilbertDirectLimitVacuumAlgebraic =
      P.fixedSlotHilbertDirectLimitVacuumAlgebraic := by
  unfold fixedSlotHilbertDirectLimitVacuumAlgebraic
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  rw [fixedSlotHilbertTimeTranslateCLM_hilbertState]
  apply congrArg
    (P.fixedSlotHilbertAlgebraicOf fixedSlotHilbertDirectLimitVacuumIndex)
  apply congrArg
    ((P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).hilbertState)
  apply FixedSlotCarrier.observable_injective _
  rw [P.fixedSlotHilbertDirectLimitVacuumCarrier_timeTranslate_observable,
    P.fixedSlotHilbertDirectLimitVacuumCarrier_observable]

/-- Canonical constant vacuum in the completed algebraic direct limit. -/
noncomputable def fixedSlotHilbertDirectLimitVacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitCompletion :=
  (P.fixedSlotHilbertDirectLimitVacuumAlgebraic :
    P.fixedSlotHilbertDirectLimitCompletion)

/-- Every nonnegative-rational direct-limit contraction fixes the canonical constant vacuum. -/
@[simp]
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_vacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (q : NNRat) :
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
        P.fixedSlotHilbertDirectLimitVacuum =
      P.fixedSlotHilbertDirectLimitVacuum := by
  unfold fixedSlotHilbertDirectLimitVacuum
  change
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM (q : ℚ) q.2
        (P.fixedSlotHilbertDirectLimitVacuumAlgebraic :
          P.fixedSlotHilbertDirectLimitCompletion) =
      (P.fixedSlotHilbertDirectLimitVacuumAlgebraic :
        P.fixedSlotHilbertDirectLimitCompletion)
  rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
  change
    (P.fixedSlotHilbertAlgebraicTimeTranslateCLM (q : ℚ) q.2
        P.fixedSlotHilbertDirectLimitVacuumAlgebraic :
      P.fixedSlotHilbertDirectLimitCompletion) =
      (P.fixedSlotHilbertDirectLimitVacuumAlgebraic :
        P.fixedSlotHilbertDirectLimitCompletion)
  rw [P.fixedSlotHilbertAlgebraicTimeTranslateCLM_apply]
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_vacuumAlgebraic]

/-- The constant vacuum is a genuine vector of the maximal zero-time regular sector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ⟨P.fixedSlotHilbertDirectLimitVacuum, by
    change Tendsto
      (fun q : NNRat =>
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
          P.fixedSlotHilbertDirectLimitVacuum)
      (𝓝 0) (𝓝 P.fixedSlotHilbertDirectLimitVacuum)
    have hfun :
        (fun q : NNRat =>
          P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
            P.fixedSlotHilbertDirectLimitVacuum) =
          (fun _ : NNRat => P.fixedSlotHilbertDirectLimitVacuum) := by
      funext q
      exact P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_vacuum q
    rw [hfun]
    exact tendsto_const_nhds⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuum_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    ((P.fixedSlotHilbertDirectLimitRegularVacuum :
      P.fixedSlotHilbertDirectLimitRegularSubspace) :
      P.fixedSlotHilbertDirectLimitCompletion) =
      P.fixedSlotHilbertDirectLimitVacuum :=
  rfl

/-- The original real `C₀` OS semigroup fixes the same constant vacuum at every nonnegative time. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_vacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        P.fixedSlotHilbertDirectLimitRegularVacuum =
      P.fixedSlotHilbertDirectLimitRegularVacuum := by
  apply Subtype.ext
  change
    P.fixedSlotHilbertDirectLimitRegularRealOrbit
        P.fixedSlotHilbertDirectLimitRegularVacuum t =
      P.fixedSlotHilbertDirectLimitVacuum
  let S : Set NNReal := {s |
    P.fixedSlotHilbertDirectLimitRegularRealOrbit
        P.fixedSlotHilbertDirectLimitRegularVacuum s =
      P.fixedSlotHilbertDirectLimitVacuum}
  have hclosed : IsClosed S := by
    exact isClosed_eq
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous
        P.fixedSlotHilbertDirectLimitRegularVacuum).continuous
      continuous_const
  have hrange : Set.range MGAP4D.nnratToNNReal ⊆ S := by
    intro s hs
    rcases hs with ⟨q, rfl⟩
    change
      P.fixedSlotHilbertDirectLimitRegularRealOrbit
          P.fixedSlotHilbertDirectLimitRegularVacuum
          (MGAP4D.nnratToNNReal q) =
        P.fixedSlotHilbertDirectLimitVacuum
    rw [P.fixedSlotHilbertDirectLimitRegularRealOrbit_nnrat]
    exact P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_vacuum q
  have hclosure : closure (Set.range MGAP4D.nnratToNNReal) ⊆ S :=
    closure_minimal hrange hclosed
  apply hclosure
  rw [MGAP4D.nnratToNNReal_denseRange.closure_eq]
  trivial

/-- The right difference quotient of the actual OS semigroup vanishes identically on the vacuum. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_vacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
        P.fixedSlotHilbertDirectLimitRegularVacuum t = 0 := by
  unfold fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_vacuum]
  simp

/-- The canonical vacuum has actual right-generator value zero. -/
theorem fixedSlotHilbertDirectLimitRegularVacuum_hasRightGeneratorValue_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
      P.fixedSlotHilbertDirectLimitRegularVacuum 0 := by
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_vacuum] using
    (tendsto_const_nhds : Tendsto
      (fun _ : NNReal => (0 : P.fixedSlotHilbertDirectLimitRegularSubspace))
      (nhdsWithin 0 (Ioi 0)) (nhds 0))

/-- The canonical vacuum as a point of the actual right-generator domain. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumRightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularVacuum,
    ⟨0, P.fixedSlotHilbertDirectLimitRegularVacuum_hasRightGeneratorValue_zero⟩⟩

/-- The actual original OS right generator annihilates the canonical vacuum. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_vacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightGenerator
        P.fixedSlotHilbertDirectLimitRegularVacuumRightGeneratorDomain = 0 := by
  apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
      P.fixedSlotHilbertDirectLimitRegularVacuumRightGeneratorDomain)
  exact P.fixedSlotHilbertDirectLimitRegularVacuum_hasRightGeneratorValue_zero

/-- The original right Hamiltonian therefore annihilates the canonical vacuum on its actual domain. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_vacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        P.fixedSlotHilbertDirectLimitRegularVacuumRightGeneratorDomain = 0 := by
  rw [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply]
  rw [P.fixedSlotHilbertDirectLimitRegularRightGenerator_vacuum]
  simp

/-- The canonical vacuum, now as a point of the full graph-closed Hamiltonian domain. -/
noncomputable def fixedSlotHilbertDirectLimitRegularClosedVacuumDomainPoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularVacuum, by
    rw [← P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_eq_closedRightHamiltonian_domain]
    exact P.fixedSlotHilbertDirectLimitRegularVacuumRightGeneratorDomain.property⟩

/-- The graph-closed Hamiltonian annihilates the same canonical vacuum.  This is derived from the
actual right-generator value and the #1894 closed-generator identification. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_vacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        P.fixedSlotHilbertDirectLimitRegularClosedVacuumDomainPoint = 0 := by
  have hclosed :=
    P.fixedSlotHilbertDirectLimitRegularClosedDomain_hasRightGeneratorValue
      P.fixedSlotHilbertDirectLimitRegularClosedVacuumDomainPoint
  have hclosed' :
      P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
        P.fixedSlotHilbertDirectLimitRegularVacuum
        (-P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          P.fixedSlotHilbertDirectLimitRegularClosedVacuumDomainPoint) := by
    simpa [fixedSlotHilbertDirectLimitRegularClosedVacuumDomainPoint] using hclosed
  have hzero :=
    P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
      hclosed'
      P.fixedSlotHilbertDirectLimitRegularVacuum_hasRightGeneratorValue_zero
  exact neg_eq_zero.mp hzero

/-- The one-dimensional canonical vacuum line in the regular same-root Hilbert sector. -/
def fixedSlotHilbertDirectLimitRegularVacuumLine
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Submodule ℝ P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ℝ ∙ P.fixedSlotHilbertDirectLimitRegularVacuum

/-- The canonical same-root excitation sector. -/
def fixedSlotHilbertDirectLimitRegularVacuumOrthogonal
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Submodule ℝ P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularVacuumLineᗮ

/-- Complete Hilbert carrier of same-root vacuum-orthogonal excitations. -/
abbrev FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) : Type :=
  P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal

instance fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCompleteSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    CompleteSpace P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert := by
  change CompleteSpace ↥P.fixedSlotHilbertDirectLimitRegularVacuumLineᗮ
  exact Submodule.instOrthogonalCompleteSpace P.fixedSlotHilbertDirectLimitRegularVacuumLine

/-- Excitation-sector membership is exactly orthogonality to the canonical constant vacuum. -/
theorem mem_fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_iff
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (psi : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    psi ∈ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal ↔
      inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum psi = 0 := by
  simpa [fixedSlotHilbertDirectLimitRegularVacuumOrthogonal,
    fixedSlotHilbertDirectLimitRegularVacuumLine] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ)
      (u := P.fixedSlotHilbertDirectLimitRegularVacuum)
      (v := psi))

/-- The original real OS semigroup preserves the full vacuum-orthogonal excitation sector. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_timeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (psi : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (hpsi : psi ∈ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t psi ∈
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal := by
  rw [P.mem_fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_iff]
  calc
    inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t psi) =
      inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          P.fixedSlotHilbertDirectLimitRegularVacuum) psi := by
        symm
        exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_symmetric
          t P.fixedSlotHilbertDirectLimitRegularVacuum psi
    _ = inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum psi := by
      rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_vacuum]
    _ = 0 :=
      (P.mem_fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_iff psi).mp hpsi

/-- Self-adjointness and zero vacuum energy force the closed Hamiltonian range into the same
vacuum-orthogonal sector. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_range_mem_vacuumOrthogonal
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (psi : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian psi ∈
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal := by
  rw [P.mem_fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_iff]
  have hSymmetric :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isFormalAdjoint
  calc
    inner ℝ P.fixedSlotHilbertDirectLimitRegularVacuum
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian psi) =
      inner ℝ (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian psi)
        P.fixedSlotHilbertDirectLimitRegularVacuum :=
      real_inner_comm _ _
    _ = inner ℝ (psi : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          P.fixedSlotHilbertDirectLimitRegularClosedVacuumDomainPoint) :=
      hSymmetric psi P.fixedSlotHilbertDirectLimitRegularClosedVacuumDomainPoint
    _ = 0 := by
      rw [P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_vacuum,
        inner_zero_right]

/-- Closed-Hamiltonian domain intersected with the canonical vacuum-orthogonal Hilbert sector. -/
def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Submodule ℝ P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert where
  carrier := {psi |
    ((psi : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
      P.fixedSlotHilbertDirectLimitRegularSubspace) ∈
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain}
  zero_mem' := P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain.zero_mem
  add_mem' := by
    intro x y hx hy
    change
      ((x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace) +
        ((y : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace) ∈
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain
    exact P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain.add_mem hx hy
  smul_mem' := by
    intro c x hx
    change
      c • ((x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
        P.fixedSlotHilbertDirectLimitRegularSubspace) ∈
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain
    exact P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain.smul_mem c hx

/-- A restricted excitation-domain point viewed in the ambient graph-closed Hamiltonian domain. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :=
  ⟨(((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
      P.fixedSlotHilbertDirectLimitRegularSubspace), x.property⟩

/-- Closed Hamiltonian action bundled into the same-root excitation sector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonianLinearMap
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain →ₗ[ℝ]
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert where
  toFun := fun x =>
    ⟨P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x),
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_range_mem_vacuumOrthogonal
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x)⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simpa [fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint] using
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.toFun.map_add
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x)
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint y)
  map_smul' := by
    intro c x
    apply Subtype.ext
    have hDomain :
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint (c • x) =
          c • P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x := by
      apply Subtype.ext
      rfl
    change
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint (c • x)) =
        c • P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x)
    rw [hDomain]
    exact P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.toFun.map_smul c
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x)

/-- Exact graph-closed Hamiltonian restricted to the canonical same-root excitation sector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonian
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert →ₗ.[ℝ]
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
  { domain := P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain
    toFun := P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonianLinearMap }

@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonian_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonian.domain) :
    (((P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonian x :
        P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
        P.fixedSlotHilbertDirectLimitRegularSubspace)) =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x) :=
  rfl

/-- Ambient formal self-adjointness descends as the exact inner-product symmetry relation on the
vacuum-orthogonal closed domain.  This formulation avoids choosing a second, non-definitionally
equal `Module` instance for the nested orthogonal submodule while retaining the operator identity
needed by later Rayleigh and spectral arguments. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedRightHamiltonian_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))
        (((y : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace) =
      inner ℝ
        (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint y)) := by
  exact P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isFormalAdjoint
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x)
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint y)

/-- Collected same-root vacuum/orthogonal package. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    (∀ t : NNReal,
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          P.fixedSlotHilbertDirectLimitRegularVacuum =
        P.fixedSlotHilbertDirectLimitRegularVacuum) ∧
    (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        P.fixedSlotHilbertDirectLimitRegularClosedVacuumDomainPoint = 0) ∧
    (∀ (t : NNReal)
      (psi : P.fixedSlotHilbertDirectLimitRegularSubspace),
      psi ∈ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal →
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t psi ∈
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal) ∧
    (∀ psi : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain,
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian psi ∈
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_vacuum,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_vacuum,
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_timeTranslate,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_range_mem_vacuumOrthogonal⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
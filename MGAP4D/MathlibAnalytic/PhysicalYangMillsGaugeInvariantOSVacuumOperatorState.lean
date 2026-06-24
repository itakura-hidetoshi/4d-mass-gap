import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumVacuum
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Quadratic-form positivity for a bounded real-linear operator on the
completed physical OS Hilbert space. -/
def IsQuadraticNonnegative
    (P : D.OSPreHilbertData)
    (T : P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert) : Prop :=
  ∀ x, 0 ≤ inner ℝ x (T x)

/-- The vector functional selected by the completed physical OS vacuum. -/
def vacuumOperatorState
    (P : D.OSPreHilbertData) :
    (P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert) →ₗ[ℝ] ℝ where
  toFun T := inner ℝ P.vacuum (T P.vacuum)
  map_add' T U := by
    simp only [ContinuousLinearMap.add_apply, inner_add_right]
  map_smul' r T := by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right]

@[simp] theorem vacuumOperatorState_apply
    (P : D.OSPreHilbertData)
    (T : P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert) :
    P.vacuumOperatorState T = inner ℝ P.vacuum (T P.vacuum) :=
  rfl

/-- The vacuum vector functional is nonnegative on every quadratically
nonnegative bounded operator. -/
theorem vacuumOperatorState_nonnegative
    (P : D.OSPreHilbertData)
    {T : P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert}
    (hT : P.IsQuadraticNonnegative T) :
    0 ≤ P.vacuumOperatorState T :=
  hT P.vacuum

/-- The identity expectation is the squared norm of the physical vacuum. -/
theorem vacuumOperatorState_identity
    (P : D.OSPreHilbertData) :
    P.vacuumOperatorState
      (ContinuousLinearMap.id ℝ P.PhysicalHilbert) = ‖P.vacuum‖ ^ 2 := by
  rw [P.vacuumOperatorState_apply]
  change inner ℝ P.vacuum P.vacuum = ‖P.vacuum‖ ^ 2
  exact real_inner_self_eq_norm_sq P.vacuum

/-- A normalized OS state induces a normalized vector state on bounded
operators of the completed physical Hilbert space. -/
theorem vacuumOperatorState_normalized
    (P : D.OSPreHilbertData) (hP : P.IsNormalized) :
    P.vacuumOperatorState
      (ContinuousLinearMap.id ℝ P.PhysicalHilbert) = 1 := by
  rw [P.vacuumOperatorState_identity, P.norm_vacuum hP]
  norm_num

/-- The identity bounded operator is quadratically nonnegative. -/
theorem identity_isQuadraticNonnegative
    (P : D.OSPreHilbertData) :
    P.IsQuadraticNonnegative
      (ContinuousLinearMap.id ℝ P.PhysicalHilbert) := by
  intro x
  change 0 ≤ inner ℝ x x
  exact real_inner_self_nonneg

/-- Symmetric Euclidean time evolution acts on a bounded observable by the
OS sandwich `U_t T U_t`. -/
def PhysicalSemigroup.euclideanSandwich
    {P : D.OSPreHilbertData}
    (U : P.PhysicalSemigroup) (t : NNReal)
    (T : P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert) :
    P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert :=
  (U.operator t).comp (T.comp (U.operator t))

/-- A symmetric physical Euclidean semigroup that fixes the vacuum leaves the
vacuum vector state invariant under the OS sandwich action. -/
theorem vacuumOperatorState_euclideanSandwich_invariant
    (P : D.OSPreHilbertData)
    (U : P.PhysicalSemigroup)
    (hSymmetric : U.IsInnerSymmetric)
    (t : NNReal)
    (T : P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert) :
    P.vacuumOperatorState (U.euclideanSandwich t T) =
      P.vacuumOperatorState T := by
  change
    inner ℝ P.vacuum
        (U.operator t (T (U.operator t P.vacuum))) =
      inner ℝ P.vacuum (T P.vacuum)
  rw [← hSymmetric t P.vacuum (T (U.operator t P.vacuum))]
  rw [U.fixes_vacuum t, U.fixes_vacuum t]

/-- The physical OS vacuum vector state is a normalized positive linear
functional on the bounded-operator carrier, with positivity understood through
the actual Hilbert quadratic cone. -/
theorem physical_vacuum_operator_state_package
    (P : D.OSPreHilbertData) (hP : P.IsNormalized) :
    P.vacuumOperatorState
        (ContinuousLinearMap.id ℝ P.PhysicalHilbert) = 1 ∧
      (∀ T : P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert,
        P.IsQuadraticNonnegative T → 0 ≤ P.vacuumOperatorState T) := by
  refine ⟨P.vacuumOperatorState_normalized hP, ?_⟩
  intro T hT
  exact P.vacuumOperatorState_nonnegative hT

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- The concrete continuum even-periodic Wilson OS construction supplies a
normalized positive vacuum vector state on the bounded operators of its
completed physical Hilbert space. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_continuum_vacuumOperatorState_package
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    let P := physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
    P.vacuumOperatorState
        (ContinuousLinearMap.id ℝ P.PhysicalHilbert) = 1 ∧
      (∀ T : P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert,
        P.IsQuadraticNonnegative T → 0 ≤ P.vacuumOperatorState T) := by
  dsimp only
  apply PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
    .physical_vacuum_operator_state_package
  exact physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
    S D halfExtent N hN beta hbeta B hInvariant

end

end MathlibAnalytic
end MGAP4D

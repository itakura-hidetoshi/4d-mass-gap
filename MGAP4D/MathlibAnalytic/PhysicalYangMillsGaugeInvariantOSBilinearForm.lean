import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSWeakStarReflectionPositivity
import Mathlib.LinearAlgebra.BilinearForm.Properties

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Reflection invariance of a weak-star state on the physical gauge-invariant
observable algebra. -/
def PhysicalYangMillsGaugeInvariantOSReflectionData.WeakStarReflectionInvariant
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S)) : Prop :=
  ∀ O, omega (D.reflection O) = omega O

/-- The real Osterwalder--Schrader bilinear form
`B_omega(F,G) = omega(Theta(F) * G)` on positive-time observables.

The carrier is written through `positiveTimeSubalgebra.toSubmodule`.  This keeps
only the additive and scalar structure needed by `LinearMap.BilinForm`, while
retaining definitionally the same positive-time observables. -/
noncomputable def PhysicalYangMillsGaugeInvariantOSReflectionData.osBilinForm
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S)) :
    LinearMap.BilinForm ℝ D.positiveTimeSubalgebra.toSubmodule :=
  LinearMap.mk₂ ℝ
    (fun F G =>
      omega
        (D.reflection
            (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
          (G : physicalYangMillsGaugeInvariantObservableSubalgebra S)))
    (by
      intro F G H
      simp [add_mul])
    (by
      intro r F G
      simp)
    (by
      intro F G H
      simp [mul_add])
    (by
      intro r F G
      simp)

@[simp]
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.osBilinForm_apply
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (F G : D.positiveTimeSubalgebra.toSubmodule) :
    D.osBilinForm omega F G =
      omega
        (D.reflection
            (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
          (G : physicalYangMillsGaugeInvariantObservableSubalgebra S)) := by
  rfl

/-- Reflection invariance of the state makes the OS bilinear form symmetric. -/
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.osBilinForm_isSymm
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (hInvariant : D.WeakStarReflectionInvariant omega) :
    (D.osBilinForm omega).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro F G
  rw [D.osBilinForm_apply, D.osBilinForm_apply]
  calc
    omega
          (D.reflection
              (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
            (G : physicalYangMillsGaugeInvariantObservableSubalgebra S)) =
        omega
          (D.reflection
            (D.reflection
                (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
              (G : physicalYangMillsGaugeInvariantObservableSubalgebra S))) := by
      symm
      exact hInvariant _
    _ = omega
          (D.reflection
              (G : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
            (F : physicalYangMillsGaugeInvariantObservableSubalgebra S)) := by
      apply congrArg omega
      rw [map_mul, D.reflection_involutive, D.reflection_involutive, mul_comm]

/-- Weak-star reflection positivity is exactly nonnegativity of the diagonal of
its OS bilinear form. -/
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.osBilinForm_isNonneg
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (hPositive : D.WeakStarReflectionPositive omega) :
    (D.osBilinForm omega).IsNonneg := by
  rw [LinearMap.BilinForm.isNonneg_def]
  intro F
  rw [D.osBilinForm_apply]
  simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable]
    using hPositive F

/-- A reflection-invariant reflection-positive weak-star state generates a
positive semidefinite Osterwalder--Schrader bilinear form. -/
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.osBilinForm_isPosSemidef
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (hInvariant : D.WeakStarReflectionInvariant omega)
    (hPositive : D.WeakStarReflectionPositive omega) :
    (D.osBilinForm omega).IsPosSemidef := by
  rw [LinearMap.BilinForm.isPosSemidef_def]
  exact ⟨D.osBilinForm_isSymm omega hInvariant,
    D.osBilinForm_isNonneg omega hPositive⟩

/-- Reflection invariance is sequentially closed for the weak-star topology. -/
theorem physical_yang_mills_weakStarReflectionInvariant_of_tendsto
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : ℕ → WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (omegaLimit : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (homega : Tendsto omega atTop (nhds omegaLimit))
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (omega n)) :
    D.WeakStarReflectionInvariant omegaLimit := by
  intro O
  have hReflected :
      Tendsto
        (fun n : ℕ => omega n (D.reflection O))
        atTop
        (nhds (omegaLimit (D.reflection O))) :=
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp homega)
      (D.reflection O)
  have hOriginal :
      Tendsto
        (fun n : ℕ => omega n O)
        atTop
        (nhds (omegaLimit O)) :=
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp homega) O
  have hFunctions :
      (fun n : ℕ => omega n (D.reflection O)) =
        fun n : ℕ => omega n O := by
    funext n
    exact hInvariant n O
  rw [hFunctions] at hReflected
  exact tendsto_nhds_unique hReflected hOriginal

/-- Reflection invariance of every embedded-lattice physical state passes to
the continuum weak-star state. -/
theorem physical_yang_mills_gaugeInvariantWeakStarReflectionInvariance_passes_to_limit
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (hFinite : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    D.WeakStarReflectionInvariant
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) := by
  exact physical_yang_mills_weakStarReflectionInvariant_of_tendsto
    D
    (fun n : ℕ => physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
    (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
    (physical_yang_mills_gaugeInvariantWeakStarState_converges S)
    hFinite

/-- At every scale, actual even-periodic Wilson Gibbs reflection positivity and
reflection invariance produce a positive semidefinite OS bilinear form on the
physical positive-time observable algebra. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_isPosSemidef
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    (D.osBilinForm
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)).IsPosSemidef := by
  exact D.osBilinForm_isPosSemidef
    (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
    (hInvariant n)
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_weakStarReflectionPositive
      S D halfExtent N hN beta hbeta B n)

/-- The continuum gauge-invariant state generated from the actual finite-volume
even-periodic `SU(N)` Wilson Gibbs laws carries a positive semidefinite
Osterwalder--Schrader bilinear form. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_continuum_osBilinForm_isPosSemidef
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
    (D.osBilinForm
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S)).IsPosSemidef := by
  exact D.osBilinForm_isPosSemidef
    (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
    (physical_yang_mills_gaugeInvariantWeakStarReflectionInvariance_passes_to_limit
      S D hInvariant)
    (physical_yang_mills_evenPeriodicWilsonOS_continuum_weakStarReflectionPositive
      S D halfExtent N hN beta hbeta B)

end

end MathlibAnalytic
end MGAP4D

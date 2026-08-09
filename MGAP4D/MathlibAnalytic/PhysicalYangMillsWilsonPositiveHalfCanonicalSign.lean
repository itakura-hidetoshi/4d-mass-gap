import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The multiplicative unit of the positive-time OS submodule. -/
private def positiveTimeUnit : D.positiveTimeSubalgebra.toSubmodule :=
  ⟨(1 : physicalYangMillsGaugeInvariantObservableSubalgebra S),
    D.positiveTimeSubalgebra.one_mem⟩

/-- A distinguished identity-valued open-half gauge configuration.  It is used
only to read off the global sign of a coherent positive-half square root. -/
private def openHalfIdentity (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N :=
  fun _ => 1

/-- A distinguished identity-valued reflection-fixed boundary configuration. -/
private def boundaryIdentity (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N :=
  fun _ => 1

/-- Applying the coherent quadratic pullback identity to the physical unit
observable gives an exact unit product for arbitrary positive and negative
open-half configurations.

No connectedness or positivity choice is needed: the boundary-fibered assembly
allows `x` and `y` to vary independently. -/
theorem positiveHalfPullback_unit_product_eq_one
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ)
    (x y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N) :
    Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D)) x *
        Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D))
          (periodicHypercubicEvenOpenHalfOrientationCorrection (halfExtent n) y) =
      1 := by
  let P := periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)
  let b0 : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N := boundaryIdentity (halfExtent n) N
  let A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
    P.boundaryFiberedAssemble b0 x y
  have hpull :=
    Q.quadraticObservable_pullback n (1 : D.positiveTimeSubalgebra) A
  have hleft :
      D.quadraticBoundedContinuousFunction (1 : D.positiveTimeSubalgebra)
          (Q.interpolate n A) = 1 := by
    simp [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction,
      PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable]
  have hright :
      periodicHypercubicEvenFullReflectedObservable
          (halfExtent n)
          (Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D))) A =
        Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D)) x *
          Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D))
            (periodicHypercubicEvenOpenHalfOrientationCorrection (halfExtent n) y) := by
    unfold periodicHypercubicEvenFullReflectedObservable
    change
      Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D))
          (P.positiveRestriction A) *
        Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D))
          (P.positiveRestriction
            (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) = _
    rw [periodicHypercubicEvenPositiveRestriction_configurationReflection]
    dsimp [A]
    rw [P.positiveRestriction_boundaryFiberedAssemble,
      P.negativeRestriction_boundaryFiberedAssemble]
  rw [hleft] at hpull
  change
    1 = periodicHypercubicEvenFullReflectedObservable
      (halfExtent n)
      (Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D))) A at hpull
  rw [hright] at hpull
  exact hpull.symm

/-- The scale-wise sign read from the unit image at the identity open-half
configuration. -/
def vacuumSign
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ) : ℝ :=
  Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D))
    (openHalfIdentity (halfExtent n) N)

/-- The coherent image of the unit is forced to be constant over the whole
open-half configuration space.  This is stronger than connectedness-based sign
selection and follows directly from independent boundary-fibered assembly. -/
theorem positiveHalfPullback_unit_eq_vacuumSign
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N) :
    Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D)) x =
      Q.vacuumSign n := by
  let x0 : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N := openHalfIdentity (halfExtent n) N
  let y0 : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N := openHalfIdentity (halfExtent n) N
  let d :=
    Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D))
      (periodicHypercubicEvenOpenHalfOrientationCorrection (halfExtent n) y0)
  have hx :
      Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D)) x * d = 1 := by
    simpa [d] using Q.positiveHalfPullback_unit_product_eq_one n x y0
  have h0 : Q.vacuumSign n * d = 1 := by
    simpa [vacuumSign, x0, d] using
      Q.positiveHalfPullback_unit_product_eq_one n x0 y0
  have hd : d ≠ 0 := by
    intro hd0
    rw [hd0, mul_zero] at h0
    norm_num at h0
  have hmul :
      (Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D)) x -
          Q.vacuumSign n) * d = 0 := by
    calc
      _ = Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D)) x * d -
          Q.vacuumSign n * d := by ring
      _ = 1 - 1 := by rw [hx, h0]
      _ = 0 := by ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hd)

/-- The only remaining freedom in the coherent unit square root is a global
scale-wise sign. -/
theorem vacuumSign_mul_self
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ) :
    Q.vacuumSign n * Q.vacuumSign n = 1 := by
  let x0 : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N := openHalfIdentity (halfExtent n) N
  let y0 : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N := openHalfIdentity (halfExtent n) N
  have h := Q.positiveHalfPullback_unit_product_eq_one n x0 y0
  rw [Q.positiveHalfPullback_unit_eq_vacuumSign n x0,
    Q.positiveHalfPullback_unit_eq_vacuumSign n
      (periodicHypercubicEvenOpenHalfOrientationCorrection (halfExtent n) y0)] at h
  exact h

/-- Canonical sign-normalized coherent positive-half pullback at one scale. -/
noncomputable def vacuumNormalizedPositiveHalfPullback
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ) :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
      BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
          (halfExtent n) N) ℝ :=
  Q.vacuumSign n • Q.positiveHalfPullback n

@[simp] theorem vacuumNormalizedPositiveHalfPullback_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra.toSubmodule)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N) :
    Q.vacuumNormalizedPositiveHalfPullback n F x =
      Q.vacuumSign n * Q.positiveHalfPullback n F x := by
  rfl

/-- Every coherent positive-half square root has a canonical scale-wise sign
normalization which preserves the exact reflected quadratic observable.

Multiplying the whole real-linear square root by `s_n` changes both reflected
factors by the same scalar, hence leaves their product unchanged because
`s_n^2 = 1`. -/
noncomputable def vacuumNormalized
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta) :
    PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta where
  interpolate := Q.interpolate
  interpolate_measurable := Q.interpolate_measurable
  approximatingMeasure_toMeasure_eq := Q.approximatingMeasure_toMeasure_eq
  positiveHalfPullback := Q.vacuumNormalizedPositiveHalfPullback
  quadraticObservable_pullback := by
    intro n F A
    rw [Q.quadraticObservable_pullback n F A]
    unfold periodicHypercubicEvenFullReflectedObservable
    rw [Q.vacuumNormalizedPositiveHalfPullback_apply,
      Q.vacuumNormalizedPositiveHalfPullback_apply]
    calc
      Q.positiveHalfPullback n
            (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule)
            ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A) *
          Q.positiveHalfPullback n
            (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule)
            ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
              (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) =
        1 *
          (Q.positiveHalfPullback n
              (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule)
              ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A) *
            Q.positiveHalfPullback n
              (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule)
              ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
                (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))) := by ring
      _ = (Q.vacuumSign n * Q.vacuumSign n) *
          (Q.positiveHalfPullback n
              (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule)
              ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A) *
            Q.positiveHalfPullback n
              (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule)
              ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
                (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))) := by
        rw [Q.vacuumSign_mul_self n]
      _ = (Q.vacuumSign n *
            Q.positiveHalfPullback n
              (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule)
              ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A)) *
          (Q.vacuumSign n *
            Q.positiveHalfPullback n
              (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule)
              ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
                (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))) := by ring

/-- The canonical sign-normalized coherent bridge theorem-generates the unit
compatibility introduced in the preceding common-vacuum package. -/
noncomputable def vacuumNormalizedUnitCompatibility
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q.vacuumNormalized hInvariant where
  positiveHalfPullback_vacuum_eq_one := by
    intro n
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.vacuumNormalized.toWeakStarBridge
          hInvariant n
    apply BoundedContinuousFunction.ext
    intro x
    change
      Q.vacuumSign n *
          Q.positiveHalfPullback n (positiveTimeUnit (S := S) (D := D)) x = 1
    rw [Q.positiveHalfPullback_unit_eq_vacuumSign n x]
    exact Q.vacuumSign_mul_self n

/-- Therefore the sign-normalized bridge sends every completed finite Wilson OS
vacuum to the same constant-one vector in the interacting boundary-product
common carrier, with no additional vacuum-normalization hypothesis. -/
theorem vacuumNormalized_commonEmbedding_vacuum
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Q.vacuumNormalized.physicalHilbertInteractingBoundaryCommonLinearIsometry
          hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta
            Q.vacuumNormalized.toWeakStarBridge hInvariant n) =
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta :=
  (Q.vacuumNormalizedUnitCompatibility hInvariant).commonEmbedding_vacuum n

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D

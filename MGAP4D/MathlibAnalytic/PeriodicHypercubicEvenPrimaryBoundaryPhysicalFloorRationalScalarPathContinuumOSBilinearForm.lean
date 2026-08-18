import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumReflectionInvariance
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Fixed-slot OS bilinear form for the one-sided primary scalar continuum law

For a fixed finite set `J` of nonnegative rational Euclidean times, the natural
observable carrier is the real normed space of bounded continuous functions on
the finite coordinate space `∀ q : J, ℝ`.  Pulling such an observable back to
the complete scalar path `ℚ → ℝ` gives an explicit positive-time cylinder.

This file constructs the Osterwalder--Schrader bilinear form

`B_J(F,G) = ∫ F((Θx)|_J) G(x|_J) dμ_cont(x)`

on that fixed-slot carrier.  The continuum reflection invariance from the
preceding same-root Wilson route makes the form symmetric, while the continuum
positive-cylinder theorem makes its diagonal nonnegative.  Hence each fixed
positive slot set carries a positive semidefinite OS Gram kernel.

This is deliberately below the quotient/completion stage: no closed positive-
time algebra, time-translation semigroup, or Hamiltonian premise is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

/-- Bounded-continuous observables on one fixed finite rational slot set. -/
abbrev PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable
    (J : Finset ℚ) :=
  BoundedContinuousFunction (∀ q : J, ℝ) ℝ

/-- Linear pullback from a fixed finite slot observable to the full scalar
rational path carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
    (J : Finset ℚ) :
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J →ₗ[ℝ]
      BoundedContinuousFunction (ℚ → ℝ) ℝ where
  toFun F :=
    F.compContinuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap J)
  map_add' F G := by
    ext x
    rfl
  map_smul' c F := by
    ext x
    rfl

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply
    (J : Finset ℚ)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J)
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J F x =
      F (fun q : J => x q.1) :=
  rfl

/-- Linear pullback of a bounded-continuous path observable by intrinsic time
reflection. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback :
    BoundedContinuousFunction (ℚ → ℝ) ℝ →ₗ[ℝ]
      BoundedContinuousFunction (ℚ → ℝ) ℝ where
  toFun F :=
    F.compContinuous
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflectionContinuousMap
  map_add' F G := by
    ext x
    rfl
  map_smul' c F := by
    ext x
    rfl

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_apply
    (F : BoundedContinuousFunction (ℚ → ℝ) ℝ)
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback F x =
      F (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x) :=
  rfl

/-- Intrinsic scalar path reflection is an involution. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_involutive
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x) = x := by
  funext q
  simp [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection]

/-- Reflection pullback is involutive on bounded-continuous scalar path
observables. -/
@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_involutive
    (F : BoundedContinuousFunction (ℚ → ℝ) ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback F) = F := by
  ext x
  simp

/-- Reflection pullback respects pointwise multiplication. -/
@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_mul
    (F G : BoundedContinuousFunction (ℚ → ℝ) ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback (F * G) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback F *
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback G := by
  ext x
  rfl

/-- Expectation against a scalar rational path probability law as a real linear
functional on bounded-continuous path observables. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
    (μ : ProbabilityMeasure (ℚ → ℝ)) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ →ₗ[ℝ] ℝ where
  toFun F := ∫ x, F x ∂(μ : Measure (ℚ → ℝ))
  map_add' F G := by
    simpa using integral_add'
      (F.integrable (μ : Measure (ℚ → ℝ)))
      (G.integrable (μ : Measure (ℚ → ℝ)))
  map_smul' c F := by
    simpa using integral_smul c F

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply
    (μ : ProbabilityMeasure (ℚ → ℝ))
    (F : BoundedContinuousFunction (ℚ → ℝ) ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation μ F =
      ∫ x, F x ∂(μ : Measure (ℚ → ℝ)) :=
  rfl

/-- On every Prokhorov continuum scalar law from the same Wilson root,
expectation is invariant under intrinsic reflection pullback. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.expectation_reflectionPullback_eq
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (F : BoundedContinuousFunction (ℚ → ℝ) ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
        L.continuumMeasure
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback F) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
        L.continuumMeasure F := by
  have hrefPM :=
    L.continuumMeasure_reflection_map_eq_self H N hN beta hbeta latticeSpacing
  have href :
      Measure.map
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
          (L.continuumMeasure : Measure (ℚ → ℝ)) =
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
    simpa using congrArg ProbabilityMeasure.toMeasure hrefPM
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  rw [← href]
  exact
    MeasureTheory.integral_map
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_measurable.aemeasurable
      F.continuous.measurable.aestronglyMeasurable

/-- Fixed-slot Osterwalder--Schrader bilinear form on the continuum scalar path
law. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.fixedSlotOSBilinForm
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J : Finset ℚ) :
    LinearMap.BilinForm ℝ
      (PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :=
  LinearMap.mk₂ ℝ
    (fun F G =>
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
        L.continuumMeasure
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
              J F) *
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
            J G))
    (by
      intro F G K
      simp [add_mul])
    (by
      intro c F G
      simp [smul_mul_assoc])
    (by
      intro F G K
      simp [mul_add])
    (by
      intro c F G
      simp [mul_smul_comm])

@[simp]
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.fixedSlotOSBilinForm_apply
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J : Finset ℚ)
    (F G : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing J F G =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
        L.continuumMeasure
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
              J F) *
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
            J G) := by
  rfl

/-- Reflection invariance makes the fixed-slot OS form symmetric. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.fixedSlotOSBilinForm_isSymm
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J : Finset ℚ) :
    (L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing J).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro F G
  rw [L.fixedSlotOSBilinForm_apply, L.fixedSlotOSBilinForm_apply]
  let f :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J F
  let g :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J G
  calc
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
          L.continuumMeasure
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback f * g) =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
          L.continuumMeasure
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback f * g)) := by
      symm
      exact L.expectation_reflectionPullback_eq H N hN beta hbeta latticeSpacing _
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
          L.continuumMeasure
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback g * f) := by
      apply congrArg
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
          L.continuumMeasure)
      simp [mul_comm]

/-- The diagonal of the fixed-slot OS form is nonnegative whenever the slot set
is nonnegative and the explicit primary temporal reach diverges. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.fixedSlotOSBilinForm_isNonneg
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q ∈ J, 0 ≤ q) :
    (L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing J).IsNonneg :=
  { nonneg := fun F => by
      let Cyl :
          PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder :=
        { slots := J
          slots_nonneg := hJ
          observable := F }
      have hOS :=
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorov_continuum_reflectionForm_nonneg
          H N hN beta hbeta latticeSpacing latticeSpacing_pos hreach L Cyl
      rw [L.fixedSlotOSBilinForm_apply]
      simpa [
        Cyl,
        PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionForm,
        PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionIntegrand_apply,
        PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.pathObservable_apply,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_apply,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply,
        mul_comm] using hOS }

/-- Every fixed finite nonnegative rational slot set therefore carries a
positive semidefinite OS Gram bilinear form under the same-root continuum scalar
law. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.fixedSlotOSBilinForm_isPosSemidef
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q ∈ J, 0 ≤ q) :
    (L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing J).IsPosSemidef :=
  { eq :=
      (L.fixedSlotOSBilinForm_isSymm H N hN beta hbeta latticeSpacing J).eq
    nonneg :=
      (L.fixedSlotOSBilinForm_isNonneg H N hN beta hbeta latticeSpacing
        latticeSpacing_pos hreach J hJ).nonneg }

end

end MathlibAnalytic
end MGAP4D

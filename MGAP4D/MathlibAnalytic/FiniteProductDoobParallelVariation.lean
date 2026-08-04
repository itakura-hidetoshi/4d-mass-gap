import MGAP4D.MathlibAnalytic.FinitePositiveWeightParallelVariationSpectral
import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelGroundStateDoobTransform
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteKernelGroundStateDoobData

variable {α : Type} [Fintype α]

/-- The ground-state Doob kernel acting on ordinary real observables. -/
noncomputable def doobObservableLinearMap
    (D : FiniteKernelGroundStateDoobData α) :
    (α → ℝ) →ₗ[ℝ] (α → ℝ) where
  toFun f := fun y => ∑ x : α, D.doobKernel x y * f x
  map_add' f g := by
    funext y
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ x : α, D.doobKernel x y * (c * f x)) =
          ∑ x : α, c * (D.doobKernel x y * f x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = c * ∑ x : α, D.doobKernel x y * f x := by
        rw [Finset.mul_sum]

@[simp] theorem doobObservableLinearMap_apply
    (D : FiniteKernelGroundStateDoobData α)
    (f : α → ℝ)
    (y : α) :
    D.doobObservableLinearMap f y =
      ∑ x : α, D.doobKernel x y * f x :=
  rfl

/-- The reversible positive weight of the Doob chain. -/
def doobWeight
    (D : FiniteKernelGroundStateDoobData α) : α → ℝ :=
  fun x => D.ground x ^ 2

/-- The Doob reversible weight is pointwise strictly positive. -/
theorem doobWeight_pos
    (D : FiniteKernelGroundStateDoobData α)
    (x : α) :
    0 < D.doobWeight x := by
  unfold doobWeight
  exact sq_pos_of_pos (D.ground_pos x)

/-- Stochasticity of the Doob kernel fixes the constant-one observable. -/
theorem doobObservableLinearMap_one
    (D : FiniteKernelGroundStateDoobData α) :
    D.doobObservableLinearMap (fun _ : α => (1 : ℝ)) =
      (fun _ : α => (1 : ℝ)) := by
  funext y
  unfold doobObservableLinearMap
  simpa using D.doobKernel_sum_eq_one y

end FiniteKernelGroundStateDoobData

namespace FiniteKernelGroundStateDoobData

variable {ι G : Type}
  [DecidableEq ι]
  [Fintype ι]
  [Fintype G]
  [Nonempty G]

/-- Detailed balance makes the ordinary-observable Doob operator symmetric for
its ground-square weight on a finite product configuration space. -/
theorem doobObservableLinearMap_pairing_symm
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (f g : (ι → G) → ℝ) :
    finitePositiveWeightPairing D.doobWeight
        (D.doobObservableLinearMap f) g =
      finitePositiveWeightPairing D.doobWeight f
        (D.doobObservableLinearMap g) := by
  classical
  calc
    finitePositiveWeightPairing D.doobWeight
        (D.doobObservableLinearMap f) g =
      ∑ y : ι → G, ∑ x : ι → G,
        D.ground y ^ 2 * D.doobKernel x y * f x * g y := by
      unfold finitePositiveWeightPairing doobWeight
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ x : ι → G, ∑ y : ι → G,
        D.ground y ^ 2 * D.doobKernel x y * f x * g y := by
      rw [Finset.sum_comm]
    _ = ∑ x : ι → G, ∑ y : ι → G,
        D.ground x ^ 2 * f x * D.doobKernel y x * g y := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [D.doobKernel_detailedBalance x y]
      ring
    _ = finitePositiveWeightPairing D.doobWeight f
        (D.doobObservableLinearMap g) := by
      unfold finitePositiveWeightPairing doobWeight
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring

/-- On product configurations, the generic positive-weight pairing is exactly
the existing Doob weighted inner product. -/
theorem weightedInner_eq_positiveWeightPairing
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (f g : FiniteBoundaryHilbert (ι → G)) :
    D.weightedInner f g =
      finitePositiveWeightPairing D.doobWeight
        (fun A : ι → G => f A) (fun A : ι → G => g A) := by
  rfl

/-- The plain-observable Doob action agrees pointwise with the existing finite
kernel operator on product configurations. -/
theorem doobObservableLinearMap_eq_finiteKernelOperator
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (f : FiniteBoundaryHilbert (ι → G)) :
    D.doobObservableLinearMap (fun A : ι → G => f A) =
      (fun B : ι → G => finiteKernelOperator D.doobKernel f B) := by
  funext B
  simp [doobObservableLinearMap, finiteKernelOperator_apply]

/-- The generic positive-weight quadratic form of the plain Doob map is the
existing weighted Doob quadratic form on product configurations. -/
theorem weightedDoobQuadratic_eq_positiveWeightPairing
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (f : FiniteBoundaryHilbert (ι → G)) :
    D.weightedDoobQuadratic f =
      finitePositiveWeightPairing D.doobWeight
        (D.doobObservableLinearMap (fun A : ι → G => f A))
        (fun A : ι → G => f A) := by
  unfold weightedDoobQuadratic
  rw [D.weightedInner_eq_positiveWeightPairing]
  apply congrArg
    (fun h : (ι → G) → ℝ =>
      finitePositiveWeightPairing D.doobWeight h
        (fun A : ι → G => f A))
  exact (D.doobObservableLinearMap_eq_finiteKernelOperator f).symm

/-- The existing weighted squared norm is the generic positive-weight
self-pairing on product configurations. -/
theorem weightedNormSq_eq_positiveWeightPairing
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (f : FiniteBoundaryHilbert (ι → G)) :
    D.weightedNormSq f =
      finitePositiveWeightPairing D.doobWeight
        (fun A : ι → G => f A) (fun A : ι → G => f A) := by
  unfold weightedNormSq
  exact D.weightedInner_eq_positiveWeightPairing f f

end FiniteKernelGroundStateDoobData

/-- A direct parallel variation certificate for a ground-state Doob kernel on
a finite product configuration space. -/
structure FiniteProductDoobParallelVariationCertificate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (D : FiniteKernelGroundStateDoobData (ι → G)) where
  variationData :
    FiniteProductParallelVariationMatrixData D.doobObservableLinearMap

/-- Detailed balance and stochasticity automatically promote a direct Doob
variation certificate to the generic reversible parallel package. -/
noncomputable def
    FiniteProductDoobParallelVariationCertificate.toParallelReversibleData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D) :
    FinitePositiveWeightParallelReversibleData
      D.doobWeight D.doobObservableLinearMap :=
  { variationData := C.variationData
    pairing_symm := D.doobObservableLinearMap_pairing_symm
    constant_fixed := D.doobObservableLinearMap_one }

/-- A direct parallel variation coefficient gives the centered weighted Doob
Rayleigh estimate without passing through a random-scan/local-variance
comparison. -/
theorem finiteProductDoob_centered_parallel_rayleigh_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D)
    (f : FiniteBoundaryHilbert (ι → G))
    (hMean : D.weightedMean f = 0) :
    D.weightedDoobQuadratic f ≤
      C.variationData.coefficient * D.weightedNormSq f := by
  have hCenter :
      finitePositiveWeightSum D.doobWeight
        (fun A : ι → G => f A) = 0 := by
    simpa [FiniteKernelGroundStateDoobData.weightedMean,
      FiniteKernelGroundStateDoobData.doobWeight,
      finitePositiveWeightSum] using hMean
  have hRayleigh :
      finitePositiveWeightPairing D.doobWeight
          (D.doobObservableLinearMap (fun A : ι → G => f A))
          (fun A : ι → G => f A) ≤
        C.variationData.coefficient *
          finitePositiveWeightPairing D.doobWeight
            (fun A : ι → G => f A) (fun A : ι → G => f A) := by
    simpa [FiniteProductDoobParallelVariationCertificate.toParallelReversibleData]
      using
        (finitePositiveWeight_centered_parallel_rayleigh_le
          D.doobWeight D.doobWeight_pos D.doobObservableLinearMap
          C.toParallelReversibleData (fun A : ι → G => f A) hCenter)
  calc
    D.weightedDoobQuadratic f =
        finitePositiveWeightPairing D.doobWeight
          (D.doobObservableLinearMap (fun A : ι → G => f A))
          (fun A : ι → G => f A) :=
      D.weightedDoobQuadratic_eq_positiveWeightPairing f
    _ ≤ C.variationData.coefficient *
        finitePositiveWeightPairing D.doobWeight
          (fun A : ι → G => f A) (fun A : ι → G => f A) :=
      hRayleigh
    _ = C.variationData.coefficient * D.weightedNormSq f := by
      rw [← D.weightedNormSq_eq_positiveWeightPairing f]

/-- The direct parallel Doob rate is strictly below one. -/
theorem finiteProductDoob_parallel_rate_lt_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D) :
    C.variationData.coefficient < 1 :=
  C.variationData.coefficient_lt_one

end

end MathlibAnalytic
end MGAP4D

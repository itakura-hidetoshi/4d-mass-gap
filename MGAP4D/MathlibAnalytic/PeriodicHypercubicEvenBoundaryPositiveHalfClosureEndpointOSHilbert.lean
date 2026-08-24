import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance positiveHalfClosureEndpointOSHilbertSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureEndpointOSHilbertSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureEndpointOSHilbertSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfClosureEndpointOSHilbertSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfClosureEndpointOSHilbertSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfClosureEndpointOSHilbertSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfClosureEndpointOSHilbertSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every natural power of a positive bounded operator on a real Hilbert space
is positive.  The quadratic part uses two-step induction: positivity of
`T^(n+2)` is positivity of `T^n` evaluated at `T x`, while symmetry of every
power is supplied by Mathlib's `LinearMap.IsSymmetric.pow`. -/
theorem realContinuousLinearMap_pow_isPositive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hT : (T : E →ₗ[ℝ] E).IsPositive)
    (n : ℕ) :
    (((T ^ n : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive) := by
  rw [LinearMap.isPositive_iff]
  refine ⟨?_, ?_⟩
  · simpa only [ContinuousLinearMap.toLinearMap_pow] using hT.isSymmetric.pow n
  · induction n using Nat.twoStepInduction with
    | zero =>
        intro x
        simp
    | one =>
        intro x
        exact hT.inner_nonneg_left x
    | more n ih _ihSucc =>
        intro x
        have hpowSymm :
            (((T ^ (n + 1) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric) := by
          simpa only [ContinuousLinearMap.toLinearMap_pow] using
            hT.isSymmetric.pow (n + 1)
        calc
          0 ≤ inner ℝ ((T ^ n) (T x)) (T x) := ih (T x)
          _ = inner ℝ ((T ^ (n + 1)) x) (T x) := by
            rw [pow_succ]
            rfl
          _ = inner ℝ (T x) ((T ^ (n + 1)) x) := real_inner_comm _ _
          _ = inner ℝ ((T ^ (n + 1)) (T x)) x :=
            (hpowSymm (T x) x).symm
          _ = inner ℝ ((T ^ (n + 2)) x) x := by
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
            rfl

/-- The actual physical positive-half transfer power is positive on the
Gauss-law one-slice Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
  exact realContinuousLinearMap_pow_isPositive
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isPositive
      H N hN beta hbeta)
    (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)

/-- The represented positive-half closure endpoint operator is positive. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive := by
  change
    (((periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
        H N hN beta hbeta) •
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_isPositive
      H N hN beta hbeta).smul_of_nonneg
      (periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization_nonneg
        H N hN beta hbeta)

/-- A type-separated copy of the Gauss-law one-slice state space on which the
positive-half closure endpoint form supplies the seminorm. -/
structure PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) where
  state : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N

namespace PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier

variable {H N : ℕ}
variable {hN : 0 < N}
variable {beta : ℝ}
variable {hbeta : 0 ≤ beta}

protected def zero :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta :=
  ⟨0⟩

protected def add
    (F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta :=
  ⟨F.state + G.state⟩

protected def neg
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta :=
  ⟨-F.state⟩

protected def sub
    (F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta :=
  ⟨F.state - G.state⟩

protected def nsmul
    (n : ℕ)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta :=
  ⟨n • F.state⟩

protected def zsmul
    (n : ℤ)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta :=
  ⟨n • F.state⟩

protected def smul
    (r : ℝ)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta :=
  ⟨r • F.state⟩

private theorem state_injective :
    Function.Injective
      (@PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.state
        H N hN beta hbeta) := by
  intro F G h
  cases F
  cases G
  cases h
  rfl

instance carrierAddCommGroup :
    AddCommGroup
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) := by
  letI : Zero
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) := ⟨PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.zero⟩
  letI : Add
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) := ⟨PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.add⟩
  letI : Neg
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) := ⟨PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.neg⟩
  letI : Sub
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) := ⟨PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.sub⟩
  letI : SMul ℕ
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) := ⟨PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.nsmul⟩
  letI : SMul ℤ
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) := ⟨PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.zsmul⟩
  refine Function.Injective.addCommGroup
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.state
    state_injective ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro F G
    rfl
  · intro F
    rfl
  · intro F G
    rfl
  · intro F n
    rfl
  · intro F n
    rfl

instance carrierRealSMul :
    SMul ℝ
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) :=
  ⟨PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.smul⟩

instance carrierModule :
    Module ℝ
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) := by
  refine Function.Injective.module ℝ
    ⟨⟨PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier.state, ?_⟩, ?_⟩
    state_injective ?_
  · rfl
  · intro F G
    rfl
  · intro r F
    rfl

@[simp] theorem state_zero :
    (0 : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta).state = 0 := rfl

@[simp] theorem state_add
    (F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    (F + G).state = F.state + G.state := rfl

@[simp] theorem state_neg
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    (-F).state = -F.state := rfl

@[simp] theorem state_sub
    (F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    (F - G).state = F.state - G.state := rfl

@[simp] theorem state_nsmul
    (n : ℕ)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    (n • F).state = n • F.state := rfl

@[simp] theorem state_zsmul
    (n : ℤ)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    (n • F).state = n • F.state := rfl

@[simp] theorem state_smul
    (r : ℝ)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    (r • F).state = r • F.state := rfl

end PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier

/-- The positive-half closure endpoint operator supplies a positive
semidefinite pre-inner-product core on the type-separated Gauss-law states. -/
@[reducible] noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCore
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PreInnerProductSpace.Core ℝ
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) where
  inner F G :=
    inner ℝ
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta F.state) G.state
  conj_inner_symm F G := by
    let O := periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
      H N hN beta hbeta
    have hO :=
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_isPositive
        H N hN beta hbeta).isSymmetric
    change inner ℝ (O G.state) F.state = inner ℝ (O F.state) G.state
    calc
      inner ℝ (O G.state) F.state = inner ℝ G.state (O F.state) := hO G.state F.state
      _ = inner ℝ (O F.state) G.state := real_inner_comm _ _
  re_inner_nonneg F := by
    change 0 ≤ inner ℝ
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta F.state) F.state
    exact
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_isPositive
        H N hN beta hbeta).inner_nonneg_left F.state
  add_left F G K := by
    change
      inner ℝ
          (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
            H N hN beta hbeta (F.state + G.state)) K.state =
        inner ℝ
            (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
              H N hN beta hbeta F.state) K.state +
          inner ℝ
            (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
              H N hN beta hbeta G.state) K.state
    rw [map_add, inner_add_left]
  smul_left F G r := by
    simp [inner_smul_left]

noncomputable instance periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrierSeminormedAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    SeminormedAddCommGroup
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup
    (c := periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCore
      H N hN beta hbeta)

noncomputable instance periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrierInnerProductSpace
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    InnerProductSpace ℝ
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) :=
  InnerProductSpace.ofCore
    (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCore
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier_inner
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    inner ℝ F G =
      inner ℝ
        (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
          H N hN beta hbeta F.state) G.state := by
  rfl

/-- On endpoint states the new pre-inner product is literally the actual
positive-closure Haar integral proved in the endpoint-operator bridge. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    inner ℝ F G =
      ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ),
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2 *
          (F.state : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) *
          (G.state : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1
              (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier_inner]
  exact
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_inner_eq_integral
      H N hN beta hbeta F.state G.state

/-- Null endpoint states are exactly the vectors invisible to the endpoint
seminorm. -/
def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNullSubmodule
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Submodule ℝ
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta) where
  carrier := {F | ‖F‖ = 0}
  zero_mem' := norm_zero
  add_mem' := by
    intro F G hF hG
    apply le_antisymm
    · calc
        ‖F + G‖ ≤ ‖F‖ + ‖G‖ := norm_add_le F G
        _ = 0 := by rw [hF, hG]; simp
    · exact norm_nonneg _
  smul_mem' := by
    intro r F hF
    change ‖r • F‖ = 0
    rw [norm_smul, hF, mul_zero]

@[simp] theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpoint_mem_nullSubmodule
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    F ∈ periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNullSubmodule
      H N hN beta hbeta ↔ ‖F‖ = 0 :=
  Iff.rfl

/-- The endpoint null condition is exactly vanishing of the represented
operator quadratic form. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpoint_mem_nullSubmodule_iff_quadratic_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    F ∈ periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNullSubmodule
        H N hN beta hbeta ↔
      inner ℝ
        (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
          H N hN beta hbeta F.state) F.state = 0 := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpoint_mem_nullSubmodule]
  constructor
  · intro hF
    calc
      inner ℝ
          (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
            H N hN beta hbeta F.state) F.state = inner ℝ F F := by
        rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier_inner]
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
      _ = 0 := by rw [hF]; simp
  · intro hF
    have hsq : ‖F‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq F,
        periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier_inner]
      exact hF
    exact sq_eq_zero_iff.mp hsq

/-- Equivalently, the null condition is vanishing of the actual positive-half
closure-Haar quadratic endpoint integral. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpoint_mem_nullSubmodule_iff_integral_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    F ∈ periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNullSubmodule
        H N hN beta hbeta ↔
      (∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ),
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2 *
          (F.state : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) *
          (F.state : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1
              (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) = 0 := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpoint_mem_nullSubmodule_iff_quadratic_eq_zero]
  rw [← periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier_inner]
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier_inner_eq_integral]

/-- The separated finite positive-half endpoint OS pre-Hilbert carrier. -/
abbrev PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Type :=
  SeparationQuotient
    (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta)

/-- The completed finite positive-half endpoint OS Hilbert carrier. -/
def PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbert
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Type :=
  UniformSpace.Completion
    (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
      H N hN beta hbeta)

noncomputable instance periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbertNormedAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedAddCommGroup
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbert
        H N hN beta hbeta) := by
  change NormedAddCommGroup
    (UniformSpace.Completion
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
        H N hN beta hbeta))
  exact UniformSpace.Completion.instNormedAddCommGroup _

noncomputable instance periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbertInnerProductSpace
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    InnerProductSpace ℝ
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbert
        H N hN beta hbeta) := by
  change InnerProductSpace ℝ
    (UniformSpace.Completion
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
        H N hN beta hbeta))
  exact UniformSpace.Completion.innerProductSpace

noncomputable instance periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbertCompleteSpace
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbert
        H N hN beta hbeta) := by
  change CompleteSpace
    (UniformSpace.Completion
      (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
        H N hN beta hbeta))
  exact UniformSpace.Completion.completeSpace _

/-- The separated class of an endpoint state. -/
def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClass
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
      H N hN beta hbeta :=
  SeparationQuotient.mk F

/-- The dense completed endpoint state represented by a Gauss-law one-slice
state. -/
def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbert
      H N hN beta hbeta := by
  change UniformSpace.Completion
    (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
      H N hN beta hbeta)
  exact
    (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClass
      H N hN beta hbeta F :
      UniformSpace.Completion
        (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
          H N hN beta hbeta))

@[simp] theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState_inner
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    inner ℝ
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
        H N hN beta hbeta F)
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
        H N hN beta hbeta G) = inner ℝ F G := by
  change inner ℝ
      ((periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClass
        H N hN beta hbeta F :
        PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
          H N hN beta hbeta) :
        UniformSpace.Completion
          (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
            H N hN beta hbeta))
      ((periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClass
        H N hN beta hbeta G :
        PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
          H N hN beta hbeta) :
        UniformSpace.Completion
          (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
            H N hN beta hbeta)) = inner ℝ F G
  rw [UniformSpace.Completion.inner_coe]
  change inner ℝ (SeparationQuotient.mk F) (SeparationQuotient.mk G) = inner ℝ F G
  exact SeparationQuotient.inner_mk_mk F G

@[simp] theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState_norm
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
      H N hN beta hbeta F‖ = ‖F‖ := by
  have hsq :
      ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
          H N hN beta hbeta F‖ ^ 2 = ‖F‖ ^ 2 := by
    calc
      ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
          H N hN beta hbeta F‖ ^ 2 =
        inner ℝ
          (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
            H N hN beta hbeta F)
          (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
            H N hN beta hbeta F) := by
        symm
        exact real_inner_self_eq_norm_sq _
      _ = inner ℝ F F :=
        periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState_inner
          H N hN beta hbeta F F
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
  nlinarith [
    norm_nonneg
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
        H N hN beta hbeta F),
    norm_nonneg F]

/-- The endpoint-class projection is real-linear and surjective onto the
separated pre-Hilbert carrier. -/
def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClassLinearMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
        H N hN beta hbeta where
  toFun := periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClass
    H N hN beta hbeta
  map_add' := by
    intro F G
    exact SeparationQuotient.mk_add F G
  map_smul' := by
    intro r F
    exact SeparationQuotient.mk_smul r F

@[simp] theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClassLinearMap_apply
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClassLinearMap
      H N hN beta hbeta F =
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClass
        H N hN beta hbeta F := rfl

/-- Every separated endpoint class has a Gauss-law endpoint-state
representative. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClassLinearMap_surjective
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Surjective
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClassLinearMap
        H N hN beta hbeta) := by
  intro q
  rcases SeparationQuotient.surjective_mk q with ⟨F, rfl⟩
  exact ⟨F, rfl⟩

/-- The represented endpoint-state map into the completed endpoint OS Hilbert
space, bundled as a real-linear map. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbert
        H N hN beta hbeta := by
  change
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta →ₗ[ℝ]
      UniformSpace.Completion
        (PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
          H N hN beta hbeta)
  exact
    (UniformSpace.Completion.toComplₗᵢ
      (𝕜 := ℝ)
      (E := PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointSeparated
        H N hN beta hbeta)).toLinearMap.comp
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointClassLinearMap
        H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap_apply
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
      H N hN beta hbeta F =
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
        H N hN beta hbeta F := by
  rfl

/-- The kernel of the dense completed endpoint-state map is exactly the null
submodule cut out by the actual closure endpoint form. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap_ker
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    LinearMap.ker
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
        H N hN beta hbeta) =
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNullSubmodule
        H N hN beta hbeta := by
  ext F
  change
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
        H N hN beta hbeta F = 0 ↔ ‖F‖ = 0
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap_apply]
  constructor
  · intro hF
    have hnorm :
        ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
          H N hN beta hbeta F‖ = 0 := by
      rw [hF, norm_zero]
    simpa using hnorm
  · intro hF
    apply norm_eq_zero.mp
    rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState_norm,
      hF]

/-- Represented endpoint states have dense range in the completed endpoint OS
Hilbert carrier. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap_denseRange
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    DenseRange
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
        H N hN beta hbeta) := by
  intro x
  exact closure_mono
    (by
      rintro y ⟨q, rfl⟩
      rcases SeparationQuotient.surjective_mk q with ⟨F, rfl⟩
      refine ⟨F, ?_⟩
      exact
        periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap_apply
          H N hN beta hbeta F)
    (UniformSpace.Completion.denseRange_coe x)

/-- Audit-visible package for the finite positive-half endpoint OS Hilbert
upgrade.  It deliberately stops before identifying this carrier with the
separately constructed approximating observable OS Hilbert space. -/
structure PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOSHilbertPackage
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  endpointPositive :
    ((periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive
  nullIffIntegralZero :
    ∀ F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta,
      F ∈ periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNullSubmodule
          H N hN beta hbeta ↔
        (∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
            (Matrix.specialUnitaryGroup (Fin N) ℂ),
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            (F.state : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
            (F.state : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1
                (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) = 0
  completedInner :
    ∀ F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta,
      inner ℝ
        (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
          H N hN beta hbeta F)
        (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
          H N hN beta hbeta G) = inner ℝ F G
  denseRange :
    DenseRange
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
        H N hN beta hbeta)

/-- Construct the complete finite endpoint OS Hilbert package. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOSHilbertPackage
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOSHilbertPackage
      H N hN beta hbeta :=
  { endpointPositive :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_isPositive
        H N hN beta hbeta
    nullIffIntegralZero :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpoint_mem_nullSubmodule_iff_integral_eq_zero
        H N hN beta hbeta
    completedInner :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState_inner
        H N hN beta hbeta
    denseRange :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap_denseRange
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D

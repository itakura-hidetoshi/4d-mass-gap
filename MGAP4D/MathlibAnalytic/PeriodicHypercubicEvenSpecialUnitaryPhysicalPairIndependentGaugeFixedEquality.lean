import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedGaussProjection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryIndependentGaugeFixedKernelPairingGaussDescent
import Mathlib.Tactic

/-!
# Independent endpoint gauge fixed space equals the completed physical pair carrier

This closes the Hilbert/tensor/fixed-subspace part of H1-D4.

The ingredients are now all theorem-generated:

* the canonical completed pair Gauss projector `Q_G` has
  `range Q_G = PhysicalPairCarrier`;
* independent endpoint gauge fixedness makes every Hilbert--Schmidt pairing
  descend through the one-slice Gauss projections;
* the algebraic external-tensor range is dense in product Haar `L²`.

The final argument is Hilbert-space uniqueness.  First prove `Q_G` is
self-adjoint from the one-slice orthogonal projector on dense algebraic
external tensors.  Then an independently gauge-fixed kernel `K` satisfies

`⟪Q_G K, Jx⟫ = ⟪K, Q_G Jx⟫ = ⟪K, Jx⟫`

for every algebraic tensor `x`.  Density of `J` gives `Q_G K = K`, hence
`K` lies in the completed physical pair carrier.

As a concrete corollary, the canonical-sign vacuum-normalized explicit OS
vacuum pair from #5018 belongs to the physical pair carrier with no additional
compatibility hypothesis.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

local instance physicalPairFixedEqualityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairFixedEqualityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairFixedEqualitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairFixedEqualityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairFixedEqualityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairFixedEqualitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairFixedEqualitySpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance physicalPairFixedEqualitySpatialSliceHaarFinite (H N : ℕ) :
    IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

@[reducible] local instance physicalPairFixedEqualityTensorNormedAddCommGroup
    (H N : ℕ) :
    NormedAddCommGroup
      (Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (F := Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

@[reducible] local instance physicalPairFixedEqualityTensorInnerProductSpace
    (H N : ℕ) :
    InnerProductSpace ℝ
      (Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (F := Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- The one-slice orthogonal Gauss-law projector is self-adjoint in inner-product
form. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_inner
    (H N : ℕ)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection
          H N f) g =
      inner ℝ f
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection
          H N g) := by
  simpa [
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection] using
    (Submodule.inner_starProjection_left_eq_right
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
        H N).toSubmodule f g)

/-- The algebraic tensor square of the one-slice Gauss projector is
self-adjoint for Mathlib's native algebraic Hilbert tensor inner product. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection_inner
    (H N : ℕ)
    (x y :
      Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
          H N x) y =
      inner ℝ x
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
          H N y) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul f' g' =>
          simp only [
            periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection_tmul,
            TensorProduct.inner_tmul]
          rw [
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_inner
              H N f f',
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_inner
              H N g g']
      | add y₁ y₂ hy₁ hy₂ =>
          rw [map_add, inner_add_right, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, inner_add_left, inner_add_left, hx₁, hx₂]

/-- The completed tensor-square Gauss projector on pair Haar `L²` is
self-adjoint.  The proof uses density of algebraic external tensors and no
additional completion model. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_inner
    (H N : ℕ)
    (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
          H N F) G =
      inner ℝ F
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
          H N G) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let J :=
    realL2ExternalTensorLiftLinearIsometry
      (μ := mu) (ν := mu)
  let A :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
      H N
  have hDense : DenseRange J :=
    realL2ExternalTensorLiftLinearIsometry_denseRange
      (μ := mu) (ν := mu)
  refine hDense.induction_on₂
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ F G
  intro x y
  change
    inner ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
          H N (realL2ExternalTensorLift x))
        (realL2ExternalTensorLift y) =
      inner ℝ
        (realL2ExternalTensorLift x)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
          H N (realL2ExternalTensorLift y))
  rw [
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_apply_externalTensorLift
      H N x,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_apply_externalTensorLift
      H N y]
  change
    inner ℝ
        (realL2ExternalTensorLift (A x))
        (realL2ExternalTensorLift y) =
      inner ℝ
        (realL2ExternalTensorLift x)
        (realL2ExternalTensorLift (A y))
  calc
    inner ℝ
        (realL2ExternalTensorLift (A x))
        (realL2ExternalTensorLift y) =
      inner ℝ (A x) y := by
        simpa only [realL2ExternalTensorLiftLinearIsometry_apply] using
          J.inner_map_map (A x) y
    _ = inner ℝ x (A y) :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection_inner
        H N x y
    _ =
      inner ℝ
        (realL2ExternalTensorLift x)
        (realL2ExternalTensorLift (A y)) := by
        simpa only [realL2ExternalTensorLiftLinearIsometry_apply] using
          (J.inner_map_map x (A y)).symm

/-- For an independently gauge-fixed pair kernel, the kernel/external-tensor
inner product is unchanged by the algebraic tensor-square Gauss projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_inner_externalTensorLift_algebraicGaussProjection
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K)
    (x :
      Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ K
        (realL2ExternalTensorLift
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
            H N x)) =
      inner ℝ K (realL2ExternalTensorLift x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul f g =>
      rw [
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection_tmul,
        realL2ExternalTensorLift_tmul,
        realL2ExternalTensorLift_tmul]
      exact
        periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_GaussProjection
          H N K hK f g
  | add x y hx hy =>
      calc
        inner ℝ K
            (realL2ExternalTensorLift
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
                H N (x + y))) =
          inner ℝ K
            (realL2ExternalTensorLift
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
                  H N x +
                periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
                  H N y)) := by
            rw [map_add]
        _ =
          inner ℝ K
            (realL2ExternalTensorLift
                (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
                  H N x) +
              realL2ExternalTensorLift
                (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
                  H N y)) := by
            rw [map_add]
        _ =
          inner ℝ K
              (realL2ExternalTensorLift
                (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
                  H N x)) +
            inner ℝ K
              (realL2ExternalTensorLift
                (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
                  H N y)) :=
          inner_add_right K _ _
        _ =
          inner ℝ K (realL2ExternalTensorLift x) +
            inner ℝ K (realL2ExternalTensorLift y) := by
          rw [hx, hy]
        _ =
          inner ℝ K
            (realL2ExternalTensorLift x + realL2ExternalTensorLift y) :=
          (inner_add_right K _ _).symm
        _ =
          inner ℝ K (realL2ExternalTensorLift (x + y)) := by
            rw [map_add]

/-- Independent endpoint gauge fixedness forces fixedness under the completed
tensor-square Gauss projector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_completedGaussProjection_eq_self
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
        H N K =
      K := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let J :=
    realL2ExternalTensorLiftLinearIsometry
      (μ := mu) (ν := mu)
  let Q :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
      H N
  have hDense : DenseRange J :=
    realL2ExternalTensorLiftLinearIsometry_denseRange
      (μ := mu) (ν := mu)
  refine hDense.eq_of_inner_left ℝ ?_
  intro x
  change
    inner ℝ (Q K) (realL2ExternalTensorLift x) =
      inner ℝ K (realL2ExternalTensorLift x)
  calc
    inner ℝ (Q K) (realL2ExternalTensorLift x) =
      inner ℝ K
        (Q (realL2ExternalTensorLift x)) :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_inner
        H N K (realL2ExternalTensorLift x)
    _ =
      inner ℝ K
        (realL2ExternalTensorLift
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
            H N x)) := by
      rw [
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_apply_externalTensorLift]
      rfl
    _ = inner ℝ K (realL2ExternalTensorLift x) :=
      periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_inner_externalTensorLift_algebraicGaussProjection
        H N K hK x

/-- Reverse H1-D4 inclusion: every common fixed vector of the independent
endpoint gauge action belongs to the completed physical pair carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule_le_physicalPairCarrier
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
      H N).toSubmodule ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
  intro K hK
  apply
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_eq_self_iff
      H N K).1
  apply
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_completedGaussProjection_eq_self
      H N K
  exact
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule_mem
      H N K).1 hK

/-- Full H1-D4 fixed-space identification.  The completed physical pair carrier
is exactly the common fixed space of arbitrary independent primary/antipodal
endpoint gauge pullbacks. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_independentGaugeInvariantL2ClosedSubmodule
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N =
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
        H N).toSubmodule := by
  apply le_antisymm
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_le_independentGaugeInvariantL2ClosedSubmodule
        H N
  · exact
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule_le_physicalPairCarrier
        H N

/-- Pointwise H1-D4 criterion: physical pair membership is equivalent to
independent endpoint gauge fixedness. -/
theorem
    periodicHypercubicEvenSpecialUnitary_mem_physicalPairCarrier_iff_independentGaugeFixed
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    K ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N ↔
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_independentGaugeInvariantL2ClosedSubmodule]
  exact
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule_mem
      H N K

/-- The concrete finite-volume boundary vacuum pair belongs to the completed
physical pair carrier, generated from independent endpoint gauge fixedness. -/
theorem periodicHypercubicEvenBoundaryVacuumPairL2_mem_physicalPairCarrier
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
  rw [
    periodicHypercubicEvenSpecialUnitary_mem_physicalPairCarrier_iff_independentGaugeFixed]
  intro gammaPrimary gammaAntipodal
  exact
    periodicHypercubicEvenBoundaryVacuumPairL2_independentGaugeFixed
      H N hN beta hbeta gammaPrimary gammaAntipodal

section VacuumNormalizedPair

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- H1-D4 closure criterion: the canonical-sign vacuum-normalized explicit OS
vacuum pair is theorem-generated inside the completed physical pair carrier,
with no externally supplied compatibility witness. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_mem_physicalPairCarrier
    (n : ℕ) :
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N := by
  rw [
    periodicHypercubicEvenSpecialUnitary_mem_physicalPairCarrier_iff_independentGaugeFixed]
  intro gammaPrimary gammaAntipodal
  exact
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_independentGaugeFixed
      Q hInvariant n gammaPrimary gammaAntipodal

end VacuumNormalizedPair

/-- Audit-visible H1-D4 closure package. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedEqualityPackage
    (H N : ℕ) : Prop where
  fixedSpaceEq :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N =
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
        H N).toSubmodule
  membershipIff :
    ∀ K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N,
      K ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N ↔
        ∀ gammaPrimary gammaAntipodal :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
              H N gammaPrimary gammaAntipodal K =
            K

/-- Construct the full H1-D4 fixed-space equality receipt. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedEqualityPackage
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedEqualityPackage
      H N :=
  { fixedSpaceEq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_independentGaugeInvariantL2ClosedSubmodule
        H N
    membershipIff :=
      periodicHypercubicEvenSpecialUnitary_mem_physicalPairCarrier_iff_independentGaugeFixed
        H N }

end

end MathlibAnalytic
end MGAP4D

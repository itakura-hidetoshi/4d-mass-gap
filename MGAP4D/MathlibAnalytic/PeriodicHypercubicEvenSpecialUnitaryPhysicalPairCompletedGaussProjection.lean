import MGAP4D.MathlibAnalytic.HilbertTensorCompactCompletion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAlgebraicGaussProjectionRange
import MGAP4D.MathlibAnalytic.RealL2ExternalTensorCompletionEquiv
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Tactic

/-!
# Completed tensor-square Gauss projection on pair Haar L²

The preceding layers provide:

* the genuine one-slice orthogonal Gauss-law projector `P_G`;
* the algebraic tensor-square range equality
  `range(J ∘ (P_G ⊗ P_G)) = PhysicalPairSpan`;
* density of the real external tensor realization `J`;
* a canonical Hilbert-completion equivalence
  `Completion(L² ⊗ L²) ≃ₗᵢ L²(product)`.

This file transports the completed tensor square of `P_G` across that
canonical equivalence.  The resulting bounded projection `Q_G` on pair Haar
`L²` has range exactly equal to the completed physical pair carrier.

No gauge-fixed-space converse is used here.  The final H1-D4 step is therefore
reduced to proving that independent endpoint gauge fixed vectors are fixed by
this concrete completed projector.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

local instance physicalPairCompletedGaussTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairCompletedGaussCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairCompletedGaussSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairCompletedGaussMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairCompletedGaussBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairCompletedGaussSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairCompletedGaussSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance physicalPairCompletedGaussSpatialSliceHaarFinite (H N : ℕ) :
    IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

@[reducible] local instance physicalPairCompletedGaussTensorNormedAddCommGroup
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

@[reducible] local instance physicalPairCompletedGaussTensorInnerProductSpace
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

/-- Completion of the algebraic tensor-square Gauss projector, transported
through the canonical external-tensor Hilbert-completion equivalence to the
actual pair Haar `L²` carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let U :=
    realL2ExternalTensorHilbertCompletionEquiv
      (μ := mu) (ν := mu)
  let P :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N
  exact
    ((U :
      UniformSpace.Completion
          (Lp ℝ 2 mu ⊗[ℝ] Lp ℝ 2 mu) →L[ℝ]
        Lp ℝ 2 (mu.prod mu)) ∘L
      (hilbertTensorMap P P).completion) ∘L
        (U.symm :
          Lp ℝ 2 (mu.prod mu) →L[ℝ]
            UniformSpace.Completion
              (Lp ℝ 2 mu ⊗[ℝ] Lp ℝ 2 mu))

/-- On the canonical algebraic external-tensor image, the completed pair Gauss
projection is exactly the previously defined algebraic tensorwise Gauss
projection realization. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_apply_externalTensorLift
    (H N : ℕ)
    (x :
      Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
        H N (realL2ExternalTensorLift x) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
        H N x := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let U :=
    realL2ExternalTensorHilbertCompletionEquiv
      (μ := mu) (ν := mu)
  let P :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N
  have hU :
      U
          (x : UniformSpace.Completion
            (Lp ℝ 2 mu ⊗[ℝ] Lp ℝ 2 mu)) =
        realL2ExternalTensorLift x := by
    exact
      realL2ExternalTensorHilbertCompletionEquiv_apply_coe
        (μ := mu) (ν := mu) x
  have hUsymm :
      U.symm (realL2ExternalTensorLift x) =
        (x : UniformSpace.Completion
          (Lp ℝ 2 mu ⊗[ℝ] Lp ℝ 2 mu)) := by
    rw [← hU, U.symm_apply_apply]
  change
    U
        ((hilbertTensorMap P P).completion
          (U.symm (realL2ExternalTensorLift x))) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
        H N x
  rw [hUsymm, ContinuousLinearMap.completion_apply_coe]
  rw [realL2ExternalTensorHilbertCompletionEquiv_apply_coe]
  rw [hilbertTensorMap_apply]
  rfl

/-- The completed pair Gauss projector is idempotent, stated directly as
composition equality to keep the completion/conjugation implementation opaque
to Lean's definitional equality checker. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_comp_self
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection H N).comp
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection H N) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection H N := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let J :=
    realL2ExternalTensorLiftLinearIsometry
      (μ := mu) (ν := mu)
  let P :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N
  let A :=
    hilbertTensorMap P P
  let Q :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection H N
  have hDense : DenseRange J :=
    realL2ExternalTensorLiftLinearIsometry_denseRange
      (μ := mu) (ν := mu)
  have hP :
      P ∘L P = P :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_idempotent
      H N
  have hA :
      A ∘L A = A := by
    dsimp [A]
    rw [← hilbertTensorMap_comp P P P P, hP]
  have hQ :
      ∀ x : Lp ℝ 2 mu ⊗[ℝ] Lp ℝ 2 mu,
        Q (J x) = J (A x) := by
    intro x
    change
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
          H N (realL2ExternalTensorLift x) =
        realL2ExternalTensorLift (A x)
    rw [
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_apply_externalTensorLift]
    change
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
          H N x =
        realL2ExternalTensorLift (A x)
    rw [hilbertTensorMap_apply]
    rfl
  apply ContinuousLinearMap.ext
  intro F
  change Q (Q F) = Q F
  refine hDense.induction_on F (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  calc
    Q (Q (J x)) = Q (J (A x)) := by rw [hQ x]
    _ = J (A (A x)) := hQ (A x)
    _ = J (A x) := by
      have hAx :=
        congrArg
          (fun T :
            (Lp ℝ 2 mu ⊗[ℝ] Lp ℝ 2 mu) →L[ℝ]
              (Lp ℝ 2 mu ⊗[ℝ] Lp ℝ 2 mu) =>
            T x)
          hA
      simpa only [ContinuousLinearMap.comp_apply] using congrArg J hAx
    _ = Q (J x) := (hQ x).symm

/-- The completed pair Gauss-projector range is contained in the completed
physical pair carrier.  Density of algebraic external tensors propagates the
algebraic range statement to all pair-Haar `L²` vectors. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_range_le_physicalPairCarrier
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
      H N).range ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
  rintro y ⟨F, rfl⟩
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let J :=
    realL2ExternalTensorLiftLinearIsometry
      (μ := mu) (ν := mu)
  have hDense : DenseRange J :=
    realL2ExternalTensorLiftLinearIsometry_denseRange
      (μ := mu) (ν := mu)
  refine hDense.induction_on F ?_ ?_
  · change
      IsClosed
        {z : Lp ℝ 2 (mu.prod mu) |
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
              H N z ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N}
    exact
      (Submodule.isClosed_topologicalClosure
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N)).preimage
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
            H N).continuous
  · intro x
    change
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
          H N (realL2ExternalTensorLift x) ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N
    rw [
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_apply_externalTensorLift]
    change
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
          H N x ∈
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N).topologicalClosure
    apply
      Submodule.le_topologicalClosure
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N)
    exact
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization_range_le_physicalPairSpan
        H N ⟨x, rfl⟩

/-- The completed physical pair carrier is contained in the range of the
completed pair Gauss projector.  The algebraic projected range is already in
the projector range, and idempotence makes that range closed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_le_spatialSlicePairCompletedGaussProjection_range
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N ≤
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
        H N).range := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_algebraicGaussProjectionRealization_range_topologicalClosure]
  apply
    (LinearMap.range
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
        H N)).topologicalClosure_minimal
  · rintro y ⟨x, rfl⟩
    refine ⟨realL2ExternalTensorLift x, ?_⟩
    exact
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_apply_externalTensorLift
        H N x
  · let Q :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
        H N
    have hComp : Q.comp Q = Q :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_comp_self
        H N
    have hIdem : IsIdempotentElem Q := by
      simpa only [ContinuousLinearMap.mul_def] using hComp
    exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hIdem

/-- Exact completion-level H1-D4 range theorem: the range of the canonical
completed tensor-square Gauss projector is exactly the physical pair carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_range
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
      H N).range =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
  apply le_antisymm
  · exact
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_range_le_physicalPairCarrier
        H N
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_le_spatialSlicePairCompletedGaussProjection_range
        H N

/-- A pair-Haar `L²` vector is physical exactly when the completed tensor-square
Gauss projector fixes it. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_eq_self_iff
    (H N : ℕ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
        H N F = F ↔
      F ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
  rw [←
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_range
      H N]
  constructor
  · intro hF
    exact ⟨F, hF⟩
  · rintro ⟨G, rfl⟩
    let Q :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
        H N
    have hComp : Q.comp Q = Q :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_comp_self
        H N
    change Q (Q G) = Q G
    have hApply :=
      congrArg
        (fun T :
          PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N =>
          T G)
        hComp
    simpa only [ContinuousLinearMap.comp_apply] using hApply

/-- Audit-visible completed pair-Gauss projection package. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedGaussProjectionPackage
    (H N : ℕ) : Prop where
  idempotent :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection H N).comp
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection H N) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection H N
  rangeEq :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
      H N).range =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N
  fixedIff :
    ∀ F : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection
          H N F = F ↔
        F ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N

/-- Construct the completion-level tensor-square Gauss projection receipt. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedGaussProjectionPackage
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedGaussProjectionPackage
      H N :=
  { idempotent :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_comp_self
        H N
    rangeEq :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_range
        H N
    fixedIff :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairCompletedGaussProjection_eq_self_iff
        H N }

end

end MathlibAnalytic
end MGAP4D

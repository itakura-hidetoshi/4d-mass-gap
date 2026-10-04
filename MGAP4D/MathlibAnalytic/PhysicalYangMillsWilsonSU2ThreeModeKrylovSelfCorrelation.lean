import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovScalarStrongLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferSelfAdjoint
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOSHilbert
import Mathlib.Tactic

/-!
# Replace SU(2) Krylov norm-square convergence by scalar self-correlation

PR #5092 reduces strong convergence of each finite Krylov mode to two scalar
limits: its norm square and its overlap with the candidate continuum limit.

For the finite norm square, even that is more data than necessary.

The normalized physical pair transfer is a real scalar multiple of the
symmetric literal pair-Haar transfer, hence is symmetric. Therefore for every
natural time m,

  ||S^m u||^2 = <S^(2m) u, u>.

The projective continuum embedding is isometric, so the same identity is the
norm square of the common-carrier Krylov image.

This file replaces the norm-square convergence field of #5092 by convergence
of the concrete scalar 2m-step self-correlation. The remaining vector-valued
overlap field is kept unchanged for the next reduction.

Thus one half of the #5092 scalar strong-limit input is now an ordinary finite
transfer matrix coefficient.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

/-- A symmetric real bounded operator satisfies the exact even-time moment
identity ||T^m u||^2 = <T^(2m)u,u>. -/
theorem realContinuousLinearMap_pow_apply_norm_sq_eq_inner_two_mul
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (m : ℕ) (u : E) :
    ‖(T ^ m) u‖ ^ 2 =
      inner ℝ ((T ^ (2 * m)) u) u := by
  rw [← real_inner_self_eq_norm_sq]
  have hpow :
      (((T ^ m : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric) :=
    realContinuousLinearMap_pow_isSymmetric T hT m
  calc
    inner ℝ ((T ^ m) u) ((T ^ m) u) =
        inner ℝ u ((T ^ m) ((T ^ m) u)) :=
      hpow u ((T ^ m) u)
    _ = inner ℝ u ((T ^ (m + m)) u) := by
      rw [pow_add]
      rfl
    _ = inner ℝ u ((T ^ (2 * m)) u) := by
      congr 2
      omega
    _ = inner ℝ ((T ^ (2 * m)) u) u := by
      rw [real_inner_comm]

local instance su2KrylovSelfCorrelationTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovSelfCorrelationCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovSelfCorrelationSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovSelfCorrelationMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovSelfCorrelationBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovSelfCorrelationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovSelfCorrelationSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2KrylovSelfCorrelationNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section KrylovSelfCorrelation

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- The normalized physical pair transfer is symmetric on the ambient
pair-Haar real Hilbert carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_isSymmetric
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive b hb :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2) :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2).IsSymmetric := by
  unfold periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
  exact
    LinearMap.IsSymmetric.smul (by simp)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_isSymmetric
        H 2 specialUnitaryTwoWilsonRankPositive b hb)

/-- Concrete finite 2m-step scalar self-correlation of the k-th first-three
Gram--Schmidt pair mode. -/
noncomputable def physicalYangMillsSU2ThreeModeFiniteKrylovSelfCorrelation
    (n m : ℕ) (k : Fin 3) : ℝ :=
  inner ℝ
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) ^ (2 * m))
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent n) k))
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
      (halfExtent n) k)

/-- The common-carrier Krylov norm square is exactly the finite 2m-step
self-correlation. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_norm_sq_eq_selfCorrelation
    (n m : ℕ) (k : Fin 3) :
    ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
        Q R L n m k‖ ^ 2 =
      physicalYangMillsSU2ThreeModeFiniteKrylovSelfCorrelation
        Q R L n m k := by
  rw [
    physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_norm_sq
      Q R L n m k]
  unfold physicalYangMillsSU2ThreeModeFiniteKrylovSelfCorrelation
  exact
    realContinuousLinearMap_pow_apply_norm_sq_eq_inner_two_mul
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_isSymmetric
        Q R L (halfExtent n) (beta n) (hbeta n))
      m
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent n) k)

/-- Scalar H1-C3 input with the norm-square field replaced by a concrete finite
2m-step transfer self-correlation. -/
structure PhysicalYangMillsSU2ThreeModeKrylovSelfCorrelationStrongLimitInput where
  continuumKrylovMode :
    ℕ → Fin 3 → Lp ℝ 2 L.continuumMeasure
  selfCorrelation_tendsto :
    ∀ (m : ℕ) (k : Fin 3),
      Tendsto
        (fun n =>
          physicalYangMillsSU2ThreeModeFiniteKrylovSelfCorrelation
            Q R L n m k)
        atTop
        (𝓝 (‖continuumKrylovMode m k‖ ^ 2))
  overlap_tendsto :
    ∀ (m : ℕ) (k : Fin 3),
      Tendsto
        (fun n =>
          inner ℝ
            (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
              Q R L n m k)
            (continuumKrylovMode m k))
        atTop
        (𝓝 (‖continuumKrylovMode m k‖ ^ 2))

namespace PhysicalYangMillsSU2ThreeModeKrylovSelfCorrelationStrongLimitInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeKrylovSelfCorrelationStrongLimitInput
        Q R L)

/-- The finite self-correlation convergence theorem-generates the norm-square
convergence field of #5092. -/
theorem normSq_tendsto
    (m : ℕ) (k : Fin 3) :
    Tendsto
      (fun n =>
        ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k‖ ^ 2)
      atTop
      (𝓝 (‖C.continuumKrylovMode m k‖ ^ 2)) := by
  apply (C.selfCorrelation_tendsto m k).congr'
  exact Filter.Eventually.of_forall fun n =>
    (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_norm_sq_eq_selfCorrelation
      Q R L n m k).symm

/-- The self-correlation package theorem-generates the #5092 scalar
strong-limit package. -/
noncomputable def toKrylovScalarStrongLimitInput :
    PhysicalYangMillsSU2ThreeModeKrylovScalarStrongLimitInput
      Q R L where
  continuumKrylovMode := C.continuumKrylovMode
  normSq_tendsto := C.normSq_tendsto
  overlap_tendsto := C.overlap_tendsto

/-- Concrete 2m-step self-correlation convergence plus continuum overlap
convergence is enough for all evolved strong limits. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
            (fun j =>
              physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                Q R L hInvariant (phi j) m)
            atTop
            (𝓝
              (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                ((C.toKrylovScalarStrongLimitInput).toEvolvedBasisCoherenceInput)
                m cInf)) := by
  exact
    PhysicalYangMillsSU2ThreeModeKrylovScalarStrongLimitInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (C.toKrylovScalarStrongLimitInput)
      hInvariant

/-- The same scalar moment data retain the scale-uniform q0^m estimate. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝
                (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                  Q R L
                  ((C.toKrylovScalarStrongLimitInput).toEvolvedBasisCoherenceInput)
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                ((C.toKrylovScalarStrongLimitInput).toEvolvedBasisCoherenceInput)
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ThreeModeKrylovScalarStrongLimitInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (C.toKrylovScalarStrongLimitInput)
      hInvariant s hs hcut

end PhysicalYangMillsSU2ThreeModeKrylovSelfCorrelationStrongLimitInput

end KrylovSelfCorrelation

end

end MathlibAnalytic
end MGAP4D

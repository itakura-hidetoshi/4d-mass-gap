import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedOSVacuumPairProjectiveOne
import Mathlib.Tactic

/-!
# Pair-top convergence is exactly vacuum/top overlap convergence

PR #5072 removes the canonical-sign OS-vacuum pair from the projective
strong-convergence frontier: its common-carrier image is exactly constant one
at every scale.

The remaining static sequence is the physical pair-top common image.  Both it
and the continuum constant-one vacuum are unit vectors.  In a real Hilbert
space, for unit vectors u and v,

  norm (u - v)^2 = 2 - 2 * inner v u.

Therefore u_n converges strongly to v if and only if inner v u_n converges to
one.

For the Wilson sequence, exact isometry of the common carrier identifies that
inner product with the literal finite vacuum-pair / physical pair-top overlap.
Thus pair-top strong convergence is equivalent to one scalar asymptotic:

  inner (OS vacuum pair_n) (physical pair-top_n) -> 1.

Under that scalar input, the canonical projected non-top excitation converges
to the already-existing vacuum-centered continuum Wilson mode.  At least one
of the two continuum modes is nonzero by orthonormality, with no additional
vacuum compatibility assumption.

This is a static convergence theorem only.  It does not yet identify finite q0
dynamics with continuum Euclidean-time evolution.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Unit vectors converge strongly exactly when their real inner product with
the limiting unit vector converges to one. -/
theorem realHilbert_unitSequence_tendsto_iff_inner_tendsto_one
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (u : ℕ → E)
    (v : E)
    (hu : ∀ n : ℕ, ‖u n‖ = 1)
    (hv : ‖v‖ = 1) :
    Tendsto u atTop (𝓝 v) ↔
      Tendsto (fun n => inner ℝ v (u n)) atTop (𝓝 (1 : ℝ)) := by
  constructor
  · intro hStrong
    have hInner :
        Tendsto (fun n => inner ℝ v (u n)) atTop
          (𝓝 (inner ℝ v v)) :=
      tendsto_const_nhds.inner hStrong
    have hvSelf : inner ℝ v v = 1 := by
      rw [real_inner_self_eq_norm_sq, hv]
      norm_num
    simpa [hvSelf] using hInner
  · intro hInner
    have hRhs :
        Tendsto
          (fun n => (2 : ℝ) - 2 * inner ℝ v (u n))
          atTop
          (𝓝 0) := by
      have hMul :
          Tendsto
            (fun n => (2 : ℝ) * inner ℝ v (u n))
            atTop
            (𝓝 ((2 : ℝ) * 1)) :=
        tendsto_const_nhds.mul hInner
      have hSub :
          Tendsto
            (fun n => (2 : ℝ) - 2 * inner ℝ v (u n))
            atTop
            (𝓝 ((2 : ℝ) - (2 : ℝ) * 1)) :=
        tendsto_const_nhds.sub hMul
      simpa using hSub
    have hSq :
        Tendsto
          (fun n => ‖u n - v‖ ^ 2)
          atTop
          (𝓝 0) := by
      apply hRhs.congr'
      filter_upwards with n
      rw [norm_sub_sq_real, hu n, hv, real_inner_comm (u n) v]
      ring
    have hSqrt :
        Tendsto
          (fun n => Real.sqrt (‖u n - v‖ ^ 2))
          atTop
          (𝓝 0) := by
      simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).comp hSq
    have hNorm :
        Tendsto
          (fun n => ‖u n - v‖)
          atTop
          (𝓝 0) := by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg, norm_nonneg] using hSqrt
    exact (tendsto_iff_norm_sub_tendsto_zero).2 hNorm

local instance pairTopOverlapCriterionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairTopOverlapCriterionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairTopOverlapCriterionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairTopOverlapCriterionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairTopOverlapCriterionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairTopOverlapCriterionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairTopOverlapCriterionSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance pairTopOverlapCriterionContinuumProbability
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

section PairTopOverlapCriterion

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
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- The physical pair-top common image has unit norm at every finite scale. -/
@[simp] theorem
    physicalYangMillsSUNPhysicalPairTopContinuumImage_norm
    (n : ℕ) :
    ‖physicalYangMillsSUNPhysicalPairTopContinuumImage
        (Q := Q) R L n‖ = 1 := by
  change
    ‖R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
        (halfExtent n) N hN (beta n) (hbeta n))‖ = 1
  rw [R.spatialSlicePairHaarProjectiveContinuumL2Isometry_norm]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_norm
      (halfExtent n) N hN (beta n) (hbeta n)

/-- The continuum constant-one vacuum has unit norm, recovered from the exact
canonical-sign vacuum-pair image rather than from an extra assumption. -/
theorem physicalYangMillsProjectiveContinuumOne_norm :
    ‖Lp.const 2 L.continuumMeasure (1 : ℝ)‖ = 1 := by
  rw [
    ← physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage_eq_one
      Q hInvariant R L 0]
  rw [R.spatialSlicePairHaarProjectiveContinuumL2Isometry_norm]
  exact
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_norm
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) 0

/-- The common-carrier overlap with constant one is exactly the literal finite
OS-vacuum-pair / physical-pair-top overlap. -/
theorem
    physicalYangMillsSUNPhysicalPairTopContinuumImage_inner_one_eq_vacuumPair_inner_pairTop
    (n : ℕ) :
    inner ℝ
        (Lp.const 2 L.continuumMeasure (1 : ℝ))
        (physicalYangMillsSUNPhysicalPairTopContinuumImage
          (Q := Q) R L n) =
      inner ℝ
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) N hN (beta n) (hbeta n)) := by
  rw [
    ← physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage_eq_one
      Q hInvariant R L n]
  exact
    R.spatialSlicePairHaarProjectiveContinuumL2Isometry_inner L n
      (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
        (halfExtent n) N hN (beta n) (hbeta n))

/-- Pair-top strong convergence to the continuum vacuum is equivalent to the
single scalar condition that the finite vacuum/top overlap tends to one. -/
theorem
    physicalYangMillsSUNPhysicalPairTopContinuumImage_tendsto_one_iff_vacuumTopOverlap_tendsto_one
    (scale : ℕ → ℕ) :
    Tendsto
        (fun j =>
          physicalYangMillsSUNPhysicalPairTopContinuumImage
            (Q := Q) R L (scale j))
        atTop
        (𝓝 (Lp.const 2 L.continuumMeasure (1 : ℝ))) ↔
      Tendsto
        (fun j =>
          inner ℝ
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant)
              (scale j))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
              (halfExtent (scale j)) N hN
              (beta (scale j)) (hbeta (scale j))))
        atTop
        (𝓝 (1 : ℝ)) := by
  let u : ℕ → Lp ℝ 2 L.continuumMeasure := fun j =>
    physicalYangMillsSUNPhysicalPairTopContinuumImage
      (Q := Q) R L (scale j)
  let one : Lp ℝ 2 L.continuumMeasure :=
    Lp.const 2 L.continuumMeasure (1 : ℝ)
  have hCriterion :=
    realHilbert_unitSequence_tendsto_iff_inner_tendsto_one
      u one
      (fun j => by
        simpa [u] using
          physicalYangMillsSUNPhysicalPairTopContinuumImage_norm
            Q hInvariant R L (scale j))
      (by
        simpa [one] using
          physicalYangMillsProjectiveContinuumOne_norm
            Q hInvariant R L)
  have hInnerFun :
      (fun j => inner ℝ one (u j)) =
        (fun j =>
          inner ℝ
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant)
              (scale j))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
              (halfExtent (scale j)) N hN
              (beta (scale j)) (hbeta (scale j)))) := by
    funext j
    simpa [u, one] using
      physicalYangMillsSUNPhysicalPairTopContinuumImage_inner_one_eq_vacuumPair_inner_pairTop
        Q hInvariant R L (scale j)
  simpa [u, one, hInnerFun] using hCriterion

/-- At least one of the two fixed continuum Wilson modes has a nonzero
constant-one-centered component, using only orthonormality and the theorem-
generated norm of the continuum vacuum. -/
theorem
    physicalYangMillsSUNTwoMode_exists_nonzero_centeredContinuumMode
    {hN2 : 2 ≤ N}
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant) :
    ∃ k : Fin 2,
      finiteVacuumCentered
          (Lp.const 2 L.continuumMeasure (1 : ℝ))
          ((C.toTwoModeCylinderData L).continuumMode k) ≠ 0 := by
  let C2 := C.toTwoModeCylinderData L
  let one : Lp ℝ 2 L.continuumMeasure :=
    Lp.const 2 L.continuumMeasure (1 : ℝ)
  have hNonzero :=
    realHilbert_exists_nonzero_finiteVacuumCentered_of_two_orthogonal_unit
      one
      (C2.continuumMode 0)
      (C2.continuumMode 1)
      (by
        simpa [one] using
          physicalYangMillsProjectiveContinuumOne_norm
            Q hInvariant R L)
      (C2.continuumMode_norm 0)
      (C2.continuumMode_norm 1)
      (C2.continuumMode_inner_eq_zero (by norm_num))
  rcases hNonzero with h0 | h1
  · exact ⟨0, by simpa [C2, one] using h0⟩
  · exact ⟨1, by simpa [C2, one] using h1⟩

/-- Scalar overlap convergence alone now theorem-generates strong convergence
of each canonical projected non-top mode to its constant-one-centered continuum
Wilson mode. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_centeredMode_of_vacuumTopOverlap_tendsto_one
    {hN2 : 2 ≤ N}
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2)
    (scale : ℕ → ℕ)
    (hScale : Tendsto scale atTop atTop)
    (hOverlap :
      Tendsto
        (fun j =>
          inner ℝ
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant)
              (scale j))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
              (halfExtent (scale j)) N hN
              (beta (scale j)) (hbeta (scale j))))
        atTop
        (𝓝 (1 : ℝ))) :
    Tendsto
      (fun j =>
        physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
          (hN2 := hN2) Q hInvariant R L k (scale j))
      atTop
      (𝓝
        (finiteVacuumCentered
          (Lp.const 2 L.continuumMeasure (1 : ℝ))
          ((C.toTwoModeCylinderData L).continuumMode k))) := by
  let one : Lp ℝ 2 L.continuumMeasure :=
    Lp.const 2 L.continuumMeasure (1 : ℝ)
  let centeredLimit :=
    finiteVacuumCentered one ((C.toTwoModeCylinderData L).continuumMode k)
  have hTop :
      Tendsto
        (fun j =>
          physicalYangMillsSUNPhysicalPairTopContinuumImage
            (Q := Q) R L (scale j))
        atTop
        (𝓝 one) := by
    exact
      (physicalYangMillsSUNPhysicalPairTopContinuumImage_tendsto_one_iff_vacuumTopOverlap_tendsto_one
        Q hInvariant R L scale).2 hOverlap
  have hProjected :=
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_of_top_tendsto
      Q hInvariant R L C k scale hScale one hTop
  have hOneNorm : ‖one‖ = 1 := by
    simpa [one] using
      physicalYangMillsProjectiveContinuumOne_norm Q hInvariant R L
  have hOrth : inner ℝ one centeredLimit = 0 := by
    simpa [centeredLimit] using
      inner_finiteVacuumCentered_eq_zero_of_norm_one
        one ((C.toTwoModeCylinderData L).continuumMode k) hOneNorm
  simpa [one, centeredLimit, hOrth] using hProjected

/-- Terminal static consequence: if the finite vacuum/top overlap tends to one
along a cofinal scale map, there is a genuine nonzero projected physical
non-top strong limit in the common projective carrier. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_projectedNonTop_projectiveStrongLimit_of_vacuumTopOverlap_tendsto_one
    {hN2 : 2 ≤ N}
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (scale : ℕ → ℕ)
    (hScale : Tendsto scale atTop atTop)
    (hOverlap :
      Tendsto
        (fun j =>
          inner ℝ
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant)
              (scale j))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
              (halfExtent (scale j)) N hN
              (beta (scale j)) (hbeta (scale j))))
        atTop
        (𝓝 (1 : ℝ))) :
    ∃ k : Fin 2, ∃ y : Lp ℝ 2 L.continuumMeasure,
      y ≠ 0 ∧
      Tendsto
        (fun j =>
          physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
            (hN2 := hN2) Q hInvariant R L k (scale j))
        atTop
        (𝓝 y) := by
  rcases
    physicalYangMillsSUNTwoMode_exists_nonzero_centeredContinuumMode
      Q hInvariant R L C with
    ⟨k, hk⟩
  let y :=
    finiteVacuumCentered
      (Lp.const 2 L.continuumMeasure (1 : ℝ))
      ((C.toTwoModeCylinderData L).continuumMode k)
  refine ⟨k, y, ?_, ?_⟩
  · simpa [y] using hk
  · simpa [y] using
      physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_centeredMode_of_vacuumTopOverlap_tendsto_one
        Q hInvariant R L C k scale hScale hOverlap

end PairTopOverlapCriterion

end

end MathlibAnalytic
end MGAP4D

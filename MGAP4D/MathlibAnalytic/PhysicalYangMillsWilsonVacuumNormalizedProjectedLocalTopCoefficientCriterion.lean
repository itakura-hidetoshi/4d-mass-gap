import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedPairTopOverlapConvergenceCriterion
import Mathlib.Tactic

/-!
# Local top-coefficient criterion for projected non-top strong limits

PR #5073 closes a sufficient global route: if the finite OS-vacuum / physical
pair-top overlap tends to one, then the physical pair-top common image converges
strongly to constant one and the projected non-top excitation has a nonzero
strong limit.

For the projected vector itself this global convergence is stronger than
necessary.  PR #5070 gives the exact identity

  projected_n = centered_n - inner(top_n, centered_n) * top_n.

The physical pair-top image has norm one at every scale.  Therefore the
correction term converges strongly to zero as soon as the single local scalar

  inner(top_n, centered_n)

tends to zero, even if top_n has no strong limit at all.

After #5071 and #5072, centered_n already converges to the fixed
constant-one-centered continuum Wilson mode.  Hence local top-coefficient decay
alone gives the desired nonzero projected strong limit.

This criterion is strictly weaker than global vacuum/top fidelity tending to
one.  It is the natural target for positive-half transfer mixing of the fixed
local Wilson modes.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- A moving rank-one correction disappears strongly when its scalar
coefficient tends to zero and its direction has unit norm.  No convergence of
the direction is needed. -/
theorem realHilbert_tendsto_sub_inner_smul_unit_of_inner_tendsto_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (c t : ℕ → E)
    (cLimit : E)
    (hc : Tendsto c atTop (𝓝 cLimit))
    (htNorm : ∀ n : ℕ, ‖t n‖ = 1)
    (hInner :
      Tendsto (fun n => inner ℝ (t n) (c n)) atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun n => c n - inner ℝ (t n) (c n) • t n)
      atTop
      (𝓝 cLimit) := by
  let corr : ℕ → E := fun n => inner ℝ (t n) (c n) • t n
  have hInnerNorm :
      Tendsto
        (fun n => ‖inner ℝ (t n) (c n)‖)
        atTop
        (𝓝 0) := by
    simpa using hInner.norm
  have hCorrNorm :
      Tendsto
        (fun n => ‖corr n‖)
        atTop
        (𝓝 0) := by
    apply hInnerNorm.congr'
    filter_upwards with n
    dsimp [corr]
    rw [norm_smul, htNorm n, mul_one, Real.norm_eq_abs]
  have hCorr :
      Tendsto corr atTop (𝓝 (0 : E)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero] using hCorrNorm
  simpa [corr] using hc.sub hCorr

local instance projectedLocalCriterionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance projectedLocalCriterionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance projectedLocalCriterionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance projectedLocalCriterionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance projectedLocalCriterionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance projectedLocalCriterionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance projectedLocalCriterionSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance projectedLocalCriterionContinuumProbability
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

section ProjectedLocalCriterion

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

/-- The finite top coefficient from #5070 is exactly the local common-carrier
matrix coefficient appearing in the rank-one projection formula. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient_tendsto_zero_iff_common_inner_tendsto_zero
    {hN2 : 2 ≤ N}
    (k : Fin 2)
    (scale : ℕ → ℕ) :
    Tendsto
        (fun j =>
          physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient
            (hN2 := hN2) Q hInvariant k (scale j))
        atTop
        (𝓝 (0 : ℝ)) ↔
      Tendsto
        (fun j =>
          inner ℝ
            (physicalYangMillsSUNPhysicalPairTopContinuumImage
              (Q := Q) R L (scale j))
            (physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage
              (hN2 := hN2) Q hInvariant R L k (scale j)))
        atTop
        (𝓝 (0 : ℝ)) := by
  have hFun :
      (fun j =>
        physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient
          (hN2 := hN2) Q hInvariant k (scale j)) =
      (fun j =>
        inner ℝ
          (physicalYangMillsSUNPhysicalPairTopContinuumImage
            (Q := Q) R L (scale j))
          (physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage
            (hN2 := hN2) Q hInvariant R L k (scale j))) := by
    funext j
    exact
      physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient_eq_common_inner
        (hN2 := hN2) Q hInvariant R L k (scale j)
  rw [hFun]

/-- Along a cofinal scale map, vanishing of one finite local top coefficient is
enough for the corresponding projected non-top mode to converge strongly to
its fixed constant-one-centered continuum Wilson mode.  No convergence of the
pair-top direction is assumed. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_centeredMode_of_topCoefficient_tendsto_zero
    {hN2 : 2 ≤ N}
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2)
    (scale : ℕ → ℕ)
    (hScale : Tendsto scale atTop atTop)
    (hCoeff :
      Tendsto
        (fun j =>
          physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient
            (hN2 := hN2) Q hInvariant k (scale j))
        atTop
        (𝓝 (0 : ℝ))) :
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
  let c : ℕ → Lp ℝ 2 L.continuumMeasure := fun j =>
    physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage
      (hN2 := hN2) Q hInvariant R L k (scale j)
  let t : ℕ → Lp ℝ 2 L.continuumMeasure := fun j =>
    physicalYangMillsSUNPhysicalPairTopContinuumImage
      (Q := Q) R L (scale j)
  have hCentered :
      Tendsto c atTop (𝓝 centeredLimit) := by
    simpa [c, centeredLimit, one] using
      physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage_tendsto_of_vacuumPair_tendsto
        (hN2 := hN2) Q hInvariant R L C k scale hScale one
        (physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage_tendsto_one
          Q hInvariant R L scale)
  have hInner :
      Tendsto (fun j => inner ℝ (t j) (c j)) atTop (𝓝 (0 : ℝ)) := by
    exact
      (physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient_tendsto_zero_iff_common_inner_tendsto_zero
        (hN2 := hN2) Q hInvariant R L k scale).1 hCoeff
  have hAbstract :
      Tendsto
        (fun j => c j - inner ℝ (t j) (c j) • t j)
        atTop
        (𝓝 centeredLimit) :=
    realHilbert_tendsto_sub_inner_smul_unit_of_inner_tendsto_zero
      c t centeredLimit hCentered
      (fun j => by
        simpa [t] using
          physicalYangMillsSUNPhysicalPairTopContinuumImage_norm
            Q hInvariant R L (scale j))
      hInner
  apply hAbstract.congr'
  filter_upwards with j
  simpa [c, t] using
    (physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_eq_centered_sub_inner_smul_top
      (hN2 := hN2) Q hInvariant R L k (scale j)).symm

/-- If both selected local top coefficients vanish asymptotically, one of the
two canonical projected non-top sequences has a genuine nonzero strong limit.
This is strictly weaker than requiring global vacuum/top overlap to tend to
one. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_projectedNonTop_projectiveStrongLimit_of_topCoefficients_tendsto_zero
    {hN2 : 2 ≤ N}
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (scale : ℕ → ℕ)
    (hScale : Tendsto scale atTop atTop)
    (hCoeff :
      ∀ k : Fin 2,
        Tendsto
          (fun j =>
            physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient
              (hN2 := hN2) Q hInvariant k (scale j))
          atTop
          (𝓝 (0 : ℝ))) :
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
      physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_centeredMode_of_topCoefficient_tendsto_zero
        Q hInvariant R L C k scale hScale (hCoeff k)

end ProjectedLocalCriterion

end

end MathlibAnalytic
end MGAP4D

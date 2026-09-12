import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderWeakLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Precomposition of real bounded-continuous functions by a self-homeomorphism
preserves the sup norm exactly. -/
theorem boundedContinuousPrecompAlgEquiv_norm
    {X : Type*} [TopologicalSpace X]
    (h : Homeomorph X X)
    (O : BoundedContinuousFunction X ℝ) :
    ‖boundedContinuousPrecompAlgEquiv h O‖ = ‖O‖ := by
  apply le_antisymm
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg O)).2 ?_
    intro x
    rw [boundedContinuousPrecompAlgEquiv_apply]
    exact O.norm_coe_le_norm (h x)
  · have hle :
        ‖boundedContinuousPrecompAlgEquiv h.symm
            (boundedContinuousPrecompAlgEquiv h O)‖ ≤
          ‖boundedContinuousPrecompAlgEquiv h O‖ := by
      refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 ?_
      intro x
      rw [boundedContinuousPrecompAlgEquiv_apply]
      exact
        (boundedContinuousPrecompAlgEquiv h O).norm_coe_le_norm (h.symm x)
    have heq :
        boundedContinuousPrecompAlgEquiv h.symm
            (boundedContinuousPrecompAlgEquiv h O) = O := by
      ext x
      change O (h (h.symm x)) = O x
      rw [h.apply_symm_apply]
    rw [heq] at hle
    exact hle

/-- Precomposition by a self-homeomorphism is an isometry of the real BCF
Banach algebra. -/
theorem boundedContinuousPrecompAlgEquiv_isometry
    {X : Type*} [TopologicalSpace X]
    (h : Homeomorph X X) :
    Isometry (boundedContinuousPrecompAlgEquiv h) := by
  intro F K
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm,
    ← map_sub, boundedContinuousPrecompAlgEquiv_norm]

/-- The reflected quadratic operation on real bounded-continuous functions. -/
noncomputable def boundedContinuousReflectedQuadratic
    {X : Type*} [TopologicalSpace X]
    (h : Homeomorph X X)
    (F : BoundedContinuousFunction X ℝ) :
    BoundedContinuousFunction X ℝ :=
  boundedContinuousPrecompAlgEquiv h F * F

/-- The reflected quadratic operation is continuous in the BCF sup norm. -/
theorem boundedContinuousReflectedQuadratic_continuous
    {X : Type*} [TopologicalSpace X]
    (h : Homeomorph X X) :
    Continuous (boundedContinuousReflectedQuadratic h) := by
  simpa [boundedContinuousReflectedQuadratic] using
    (boundedContinuousPrecompAlgEquiv_isometry h).continuous.mul continuous_id

private abbrev physicalPositiveTimeBCF
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (F : D.positiveTimeSubalgebra) :
    BoundedContinuousFunction S.Configuration ℝ :=
  ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    BoundedContinuousFunction S.Configuration ℝ)

/-- Under the primitive configuration-reflection realization, the physical OS
quadratic BCF is literally the reflected quadratic operation on the underlying
positive-time BCF. -/
theorem PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry.quadraticBoundedContinuousFunction_eq_reflectedQuadratic
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta)
    (F : D.positiveTimeSubalgebra) :
    D.quadraticBoundedContinuousFunction F =
      boundedContinuousReflectedQuadratic G.configurationReflection
        (physicalPositiveTimeBCF F) := by
  ext A
  unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction
  unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable
  unfold boundedContinuousReflectedQuadratic
  rw [G.reflection_realization]
  rfl

/-- Sup-norm convergence of positive-time physical observables implies sup-norm
convergence of their reflected quadratic BCFs. -/
theorem PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry.quadraticBoundedContinuousFunction_tendsto_of_bcf_tendsto
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta)
    (F : ℕ → D.positiveTimeSubalgebra)
    (Flim : D.positiveTimeSubalgebra)
    (hF : Tendsto (fun n => physicalPositiveTimeBCF (F n)) atTop
      (nhds (physicalPositiveTimeBCF Flim))) :
    Tendsto (fun n => D.quadraticBoundedContinuousFunction (F n)) atTop
      (nhds (D.quadraticBoundedContinuousFunction Flim)) := by
  have hcont :
      Tendsto (boundedContinuousReflectedQuadratic G.configurationReflection)
        (nhds (physicalPositiveTimeBCF Flim))
        (nhds (boundedContinuousReflectedQuadratic G.configurationReflection
          (physicalPositiveTimeBCF Flim))) :=
    (boundedContinuousReflectedQuadratic_continuous
      G.configurationReflection).tendsto (physicalPositiveTimeBCF Flim)
  have hQ := hcont.comp hF
  simpa only [G.quadraticBoundedContinuousFunction_eq_reflectedQuadratic] using hQ

/-- The same convergence is exactly the norm-to-zero condition consumed by the
uniformly-varying weak-limit route. -/
theorem PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry.quadraticBoundedContinuousFunction_norm_sub_tendsto_zero_of_bcf_tendsto
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta)
    (F : ℕ → D.positiveTimeSubalgebra)
    (Flim : D.positiveTimeSubalgebra)
    (hF : Tendsto (fun n => physicalPositiveTimeBCF (F n)) atTop
      (nhds (physicalPositiveTimeBCF Flim))) :
    Tendsto
      (fun n => ‖D.quadraticBoundedContinuousFunction (F n) -
        D.quadraticBoundedContinuousFunction Flim‖)
      atTop (nhds 0) := by
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  exact G.quadraticBoundedContinuousFunction_tendsto_of_bcf_tendsto F Flim hF

/-- Primitive normalized-trace cylinder realizations therefore need only
sup-norm convergence of their generated positive-time physical BCFs.  The
quadratic convergence required by the varying-observable weak-limit theorem is
generated automatically by continuity of `F ↦ Theta(F) * F`. -/
theorem normalizedTracePower_varying_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_bcf_tendsto
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta)
    (j : ℕ)
    (R : ∀ n,
      PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (Flim : D.positiveTimeSubalgebra)
    (hF : Tendsto
      (fun n => physicalPositiveTimeBCF ((R n).positiveTimeTracePowerObservable j))
      atTop (nhds (physicalPositiveTimeBCF Flim))) :
    0 ≤ ∫ A, D.quadraticBoundedContinuousFunction Flim A
      ∂(S.continuumMeasure : Measure S.Configuration) := by
  exact
    normalizedTracePower_varying_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_uniform
      S D halfExtent beta hbeta G j R
      (D.quadraticBoundedContinuousFunction Flim)
      (G.quadraticBoundedContinuousFunction_norm_sub_tendsto_zero_of_bcf_tendsto
        (fun n => (R n).positiveTimeTracePowerObservable j) Flim hF)

end

end MathlibAnalytic
end MGAP4D

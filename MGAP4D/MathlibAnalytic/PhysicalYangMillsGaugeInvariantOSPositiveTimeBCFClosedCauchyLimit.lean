import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSQuadraticBCFNormContinuity
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- The underlying real bounded-continuous function of a physical positive-time
observable. -/
def PhysicalYangMillsGaugeInvariantOSReflectionData.positiveTimeBCF
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F : D.positiveTimeSubalgebra) :
    BoundedContinuousFunction S.Configuration ℝ :=
  ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    BoundedContinuousFunction S.Configuration ℝ)

@[simp] theorem PhysicalYangMillsGaugeInvariantOSReflectionData.positiveTimeBCF_apply
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F : D.positiveTimeSubalgebra) (A : S.Configuration) :
    D.positiveTimeBCF F A =
      ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) A :=
  rfl

/-- The set of bounded-continuous physical observables represented by the
pre-existing positive-time subalgebra.  Closedness of this range is the exact
analytic condition needed to recover a positive-time observable from an
ambient BCF norm limit. -/
def PhysicalYangMillsGaugeInvariantOSReflectionData.positiveTimeBCFRange
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S) :
    Set (BoundedContinuousFunction S.Configuration ℝ) :=
  Set.range D.positiveTimeBCF

@[simp] theorem PhysicalYangMillsGaugeInvariantOSReflectionData.positiveTimeBCF_mem_range
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F : D.positiveTimeSubalgebra) :
    D.positiveTimeBCF F ∈ D.positiveTimeBCFRange :=
  ⟨F, rfl⟩

/-- A Cauchy sequence of physical positive-time BCFs has a positive-time limit
whenever the underlying positive-time BCF range is closed.

The ambient BCF space is complete because the real target is complete.  Thus no
completion object and no hand-supplied limiting observable are required. -/
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.exists_positiveTime_limit_of_bcfRange_closed_of_cauchy
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (hclosed : IsClosed D.positiveTimeBCFRange)
    (F : ℕ → D.positiveTimeSubalgebra)
    (hCauchy : CauchySeq (fun n => D.positiveTimeBCF (F n))) :
    ∃ Flim : D.positiveTimeSubalgebra,
      Tendsto (fun n => D.positiveTimeBCF (F n)) atTop
        (nhds (D.positiveTimeBCF Flim)) := by
  obtain ⟨Olim, hlim⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hmem : Olim ∈ D.positiveTimeBCFRange :=
    hclosed.mem_of_tendsto hlim
      (Eventually.of_forall fun n => D.positiveTimeBCF_mem_range (F n))
  rcases hmem with ⟨Flim, hFlim⟩
  refine ⟨Flim, ?_⟩
  rw [hFlim]
  exact hlim

/-- Primitive normalized-trace cylinder observables need no hand-chosen
continuum positive-time observable once their underlying BCFs are Cauchy and
the physical positive-time BCF range is closed.

The theorem constructs `Flim` and simultaneously supplies its continuum OS
quadratic nonnegativity. -/
theorem normalizedTracePower_varying_exists_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_closedRange_cauchy
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta) (j : ℕ)
    (R : ∀ n, PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (hclosed : IsClosed D.positiveTimeBCFRange)
    (hCauchy : CauchySeq (fun n => D.positiveTimeBCF ((R n).positiveTimeTracePowerObservable j))) :
    ∃ Flim : D.positiveTimeSubalgebra,
      Tendsto (fun n => D.positiveTimeBCF ((R n).positiveTimeTracePowerObservable j))
        atTop (nhds (D.positiveTimeBCF Flim)) ∧
      0 ≤ ∫ A, D.quadraticBoundedContinuousFunction Flim A
        ∂(S.continuumMeasure : Measure S.Configuration) := by
  obtain ⟨Flim, hlim⟩ :=
    D.exists_positiveTime_limit_of_bcfRange_closed_of_cauchy hclosed
      (fun n => (R n).positiveTimeTracePowerObservable j) hCauchy
  refine ⟨Flim, hlim, ?_⟩
  exact
    normalizedTracePower_varying_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_bcf_tendsto
      S D halfExtent beta hbeta G j R Flim
      (by simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.positiveTimeBCF] using hlim)

end

end MathlibAnalytic
end MGAP4D

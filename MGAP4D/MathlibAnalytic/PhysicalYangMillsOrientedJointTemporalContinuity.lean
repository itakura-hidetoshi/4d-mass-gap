import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDenseTemporalApproximation
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

/-- The time-configuration evaluation map associated with a physical temporal action. -/
def jointTranslate
    (A : E.PhysicalDiscreteTemporalAction) :
    ℝ × E.PhysicalConfiguration → E.PhysicalConfiguration :=
  fun p => A.physicalTranslate p.1 p.2

/-- Joint continuity in physical time and physical configuration. -/
structure JointContinuity (A : E.PhysicalDiscreteTemporalAction) : Prop where
  jointTranslate_continuous : Continuous A.jointTranslate

namespace JointContinuity

variable {A : E.PhysicalDiscreteTemporalAction}

private theorem jointTranslate_comp_prodMk
    (s : ℝ) :
    A.jointTranslate ∘ Prod.mk s = A.physicalTranslate s := by
  funext x
  rfl

private theorem map_jointTranslate_map_prodMk
    (J : A.JointContinuity) (s : ℝ)
    (μ : Measure E.PhysicalConfiguration) [SFinite μ] :
    Measure.map A.jointTranslate (Measure.map (Prod.mk s) μ) =
      Measure.map (A.physicalTranslate s) μ := by
  calc
    Measure.map A.jointTranslate (Measure.map (Prod.mk s) μ) =
      Measure.map (A.jointTranslate ∘ Prod.mk s) μ :=
        Measure.map_map J.jointTranslate_continuous.measurable
          measurable_prodMk_left
    _ = Measure.map (A.physicalTranslate s) μ :=
      congrArg
        (fun f : E.PhysicalConfiguration → E.PhysicalConfiguration =>
          Measure.map f μ)
        (jointTranslate_comp_prodMk (A := A) s)

private theorem map_jointTranslate_dirac_prod
    (J : A.JointContinuity) (s : ℝ)
    (μ : Measure E.PhysicalConfiguration) [SFinite μ] :
    Measure.map A.jointTranslate ((Measure.dirac s).prod μ) =
      Measure.map (A.physicalTranslate s) μ := by
  rw [Measure.dirac_prod]
  exact map_jointTranslate_map_prodMk J s μ

private theorem toMeasure_diracProba_prod_map_jointTranslate
    (J : A.JointContinuity) (s : ℝ)
    (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    ((((diracProba s).prod μ).map
        J.jointTranslate_continuous.measurable.aemeasurable) :
      Measure E.PhysicalConfiguration) =
      ((μ.map
        (A.physicalTranslate s).continuous.measurable.aemeasurable) :
      Measure E.PhysicalConfiguration) := by
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_prod]
  change
    Measure.map A.jointTranslate
        ((Measure.dirac s).prod (μ : Measure E.PhysicalConfiguration)) =
      Measure.map (A.physicalTranslate s)
        (μ : Measure E.PhysicalConfiguration)
  exact map_jointTranslate_dirac_prod J s μ

private def diracProductImage
    (J : A.JointContinuity) (s : ℝ)
    (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    ProbabilityMeasure E.PhysicalConfiguration :=
  ((diracProba s).prod μ).map
    J.jointTranslate_continuous.measurable.aemeasurable

private def translatedImage
    (A : E.PhysicalDiscreteTemporalAction) (s : ℝ)
    (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    ProbabilityMeasure E.PhysicalConfiguration :=
  μ.map (A.physicalTranslate s).continuous.measurable.aemeasurable

theorem diracProba_prod_map_jointTranslate
    (J : A.JointContinuity) (s : ℝ)
    (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    diracProductImage J s μ = translatedImage A s μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    ((((diracProba s).prod μ).map
        J.jointTranslate_continuous.measurable.aemeasurable) :
      Measure E.PhysicalConfiguration) =
      ((μ.map
        (A.physicalTranslate s).continuous.measurable.aemeasurable) :
      Measure E.PhysicalConfiguration)
  exact toMeasure_diracProba_prod_map_jointTranslate J s μ

private def diracPath (τ : ℕ → ℝ) : ℕ → ProbabilityMeasure ℝ :=
  fun n => diracProba (τ n)

private def diracLimit (t : ℝ) : ProbabilityMeasure ℝ :=
  diracProba t

private theorem diracPath_tendsto
    {τ : ℕ → ℝ} {t : ℝ}
    (hτ : Tendsto τ atTop (nhds t)) :
    Tendsto (diracPath τ) atTop (nhds (diracLimit t)) := by
  exact continuous_diracProba.continuousAt.tendsto.comp hτ

private def productPath
    (τ : ℕ → ℝ)
    (μs : ℕ → ProbabilityMeasure E.PhysicalConfiguration) :
    ℕ → ProbabilityMeasure (ℝ × E.PhysicalConfiguration) :=
  fun n => (diracPath τ n).prod (μs n)

private def productLimit
    (t : ℝ) (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    ProbabilityMeasure (ℝ × E.PhysicalConfiguration) :=
  (diracLimit t).prod μ

private theorem productPath_tendsto
    {τ : ℕ → ℝ} {t : ℝ}
    {μs : ℕ → ProbabilityMeasure E.PhysicalConfiguration}
    {μ : ProbabilityMeasure E.PhysicalConfiguration}
    (hτ : Tendsto τ atTop (nhds t))
    (hμ : Tendsto μs atTop (nhds μ)) :
    Tendsto (productPath τ μs) atTop (nhds (productLimit t μ)) := by
  have hpair :
      Tendsto (fun n => (diracPath τ n, μs n)) atTop
        (nhds (diracLimit t, μ)) :=
    (Prod.tendsto_iff _ _).2 ⟨diracPath_tendsto hτ, hμ⟩
  exact (ProbabilityMeasure.continuous_prod.tendsto
    (diracLimit t, μ)).comp hpair

private theorem diracProductImage_tendsto_of_tendsto
    (J : A.JointContinuity)
    {τ : ℕ → ℝ} {t : ℝ}
    {μs : ℕ → ProbabilityMeasure E.PhysicalConfiguration}
    {μ : ProbabilityMeasure E.PhysicalConfiguration}
    (hτ : Tendsto τ atTop (nhds t))
    (hμ : Tendsto μs atTop (nhds μ)) :
    Tendsto
      (fun n => diracProductImage J (τ n) (μs n))
      atTop
      (nhds (diracProductImage J t μ)) := by
  have hmap :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (productPath τ μs) (productLimit t μ)
      (productPath_tendsto hτ hμ) J.jointTranslate_continuous
  simpa only [productPath, productLimit, diracPath, diracLimit,
    diracProductImage] using hmap

private theorem translatedImage_tendsto_of_tendsto
    (J : A.JointContinuity)
    {τ : ℕ → ℝ} {t : ℝ}
    {μs : ℕ → ProbabilityMeasure E.PhysicalConfiguration}
    {μ : ProbabilityMeasure E.PhysicalConfiguration}
    (hτ : Tendsto τ atTop (nhds t))
    (hμ : Tendsto μs atTop (nhds μ)) :
    Tendsto
      (fun n => translatedImage A (τ n) (μs n))
      atTop
      (nhds (translatedImage A t μ)) := by
  have h := diracProductImage_tendsto_of_tendsto J hτ hμ
  have hSequence :
      (fun n => diracProductImage J (τ n) (μs n)) =
        (fun n => translatedImage A (τ n) (μs n)) := by
    funext n
    exact J.diracProba_prod_map_jointTranslate (τ n) (μs n)
  have hLimit :
      diracProductImage J t μ = translatedImage A t μ :=
    J.diracProba_prod_map_jointTranslate t μ
  rw [hSequence, hLimit] at h
  exact h

private theorem weakLimitContinuity_of_joint
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    D.WeakLimitContinuity L := by
  intro t
  let τ : ℕ → ℝ := fun n =>
    A.latticeTime (L.subsequence n)
      (D.approximateStep t (L.subsequence n))
  let μs : ℕ → ProbabilityMeasure E.PhysicalConfiguration := fun n =>
    E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)
  have hτ : Tendsto τ atTop (nhds t) := by
    simpa only [τ] using D.approximateTime_tendsto_subsequence L t
  have hμ : Tendsto μs atTop (nhds L.continuumMeasure) := by
    simpa only [μs] using L.weakConvergence
  have h := translatedImage_tendsto_of_tendsto J hτ hμ
  simpa only [τ, μs, translatedImage] using h

/-- Joint continuity supplies varying-time weak convergence at every target time. -/
theorem mappedApproximating_tendsto
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    D.WeakLimitContinuity L :=
  weakLimitContinuity_of_joint J D L

/-- Joint continuity discharges the varying-time weak-limit continuity input. -/
theorem toWeakLimitContinuity
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    D.WeakLimitContinuity L :=
  J.mappedApproximating_tendsto D L

end JointContinuity

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

end

end MathlibAnalytic
end MGAP4D

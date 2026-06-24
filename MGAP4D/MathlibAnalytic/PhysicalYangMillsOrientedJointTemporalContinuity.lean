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

private def approximatePhysicalTime
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) (n : ℕ) : ℝ :=
  A.latticeTime (L.subsequence n)
    (D.approximateStep t (L.subsequence n))

private def subsequenceMeasure
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (n : ℕ) : ProbabilityMeasure E.PhysicalConfiguration :=
  E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)

private theorem approximatePhysicalTime_tendsto
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) :
    Tendsto (approximatePhysicalTime D L t) atTop (nhds t) := by
  simpa only [approximatePhysicalTime] using
    D.approximateTime_tendsto_subsequence L t

private theorem diracApproximateTime_tendsto
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) :
    Tendsto
      (fun n => diracProba (approximatePhysicalTime D L t n))
      atTop (nhds (diracProba t)) :=
  continuous_diracProba.continuousAt.comp
    (approximatePhysicalTime_tendsto D L t)

private theorem subsequenceMeasure_tendsto
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    Tendsto (subsequenceMeasure L) atTop (nhds L.continuumMeasure) := by
  simpa only [subsequenceMeasure] using L.weakConvergence

private theorem pairMeasure_tendsto
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) :
    Tendsto
      (fun n =>
        (diracProba (approximatePhysicalTime D L t n),
          subsequenceMeasure L n))
      atTop
      (nhds (diracProba t, L.continuumMeasure)) :=
  (Prod.tendsto_iff _ _).2
    ⟨diracApproximateTime_tendsto D L t, subsequenceMeasure_tendsto L⟩

private theorem productMeasure_tendsto
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) :
    Tendsto
      (fun n =>
        (diracProba (approximatePhysicalTime D L t n)).prod
          (subsequenceMeasure L n))
      atTop
      (nhds ((diracProba t).prod L.continuumMeasure)) :=
  ProbabilityMeasure.continuous_prod.continuousAt.comp
    (pairMeasure_tendsto D L t)

private theorem diracProductImage_tendsto
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) :
    Tendsto
      (fun n =>
        diracProductImage J (approximatePhysicalTime D L t n)
          (subsequenceMeasure L n))
      atTop
      (nhds (diracProductImage J t L.continuumMeasure)) := by
  simpa only [diracProductImage] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n =>
        (diracProba (approximatePhysicalTime D L t n)).prod
          (subsequenceMeasure L n))
      ((diracProba t).prod L.continuumMeasure)
      (productMeasure_tendsto D L t)
      J.jointTranslate_continuous

private theorem translatedImage_tendsto
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) :
    Tendsto
      (fun n =>
        translatedImage A (approximatePhysicalTime D L t n)
          (subsequenceMeasure L n))
      atTop
      (nhds (translatedImage A t L.continuumMeasure)) := by
  have h := diracProductImage_tendsto J D L t
  have hSequence :
      (fun n =>
        diracProductImage J (approximatePhysicalTime D L t n)
          (subsequenceMeasure L n)) =
      (fun n =>
        translatedImage A (approximatePhysicalTime D L t n)
          (subsequenceMeasure L n)) := by
    funext n
    exact J.diracProba_prod_map_jointTranslate
      (approximatePhysicalTime D L t n) (subsequenceMeasure L n)
  have hLimit :
      diracProductImage J t L.continuumMeasure =
        translatedImage A t L.continuumMeasure :=
    J.diracProba_prod_map_jointTranslate t L.continuumMeasure
  rw [hSequence, hLimit] at h
  exact h

set_option maxHeartbeats 400000 in
private theorem weakLimitContinuity_of_joint
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    D.WeakLimitContinuity L := by
  intro t
  simpa only [approximatePhysicalTime, subsequenceMeasure, translatedImage] using
    translatedImage_tendsto J D L t

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

import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsProjectiveMarginals

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Coherent finite-Wilson realization of continuum finite-dimensional
marginals.

For `J ⊆ I`, `coarseGrain I J` transports configurations from the lattice scale
used for `I` to the lattice scale used for `J`.  It preserves the Wilson Gibbs
measure, and observing after coarse graining agrees pointwise with restricting
the `I`-observation to `J`.  These two concrete conditions imply projective
consistency of the pushforward marginals. -/
structure FiniteWilsonGibbsCoherentProjectiveRealization
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  fieldValue : EuclideanFourSpace → Type
  [fieldValueMeasurableSpace :
    ∀ x, MeasurableSpace (fieldValue x)]
  scale : Finset EuclideanFourSpace → W.index
  observe :
    ∀ J : Finset EuclideanFourSpace,
      (W.system (scale J)).Configuration →
        (∀ x : J, fieldValue x)
  observe_measurable : ∀ J, Measurable (observe J)
  coarseGrain :
    ∀ (I J : Finset EuclideanFourSpace), J ⊆ I →
      (W.system (scale I)).Configuration →
        (W.system (scale J)).Configuration
  coarseGrain_measurable :
    ∀ I J hJI, Measurable (coarseGrain I J hJI)
  gibbsMeasure_map_coarseGrain :
    ∀ I J hJI,
      (W.system (scale I)).gibbsMeasure.map
          (coarseGrain I J hJI) =
        (W.system (scale J)).gibbsMeasure
  observe_coarseGrain :
    ∀ I J hJI (A : (W.system (scale I)).Configuration),
      observe J (coarseGrain I J hJI A) =
        Finset.restrict₂ hJI (observe I A)

attribute [instance]
  FiniteWilsonGibbsCoherentProjectiveRealization.fieldValueMeasurableSpace

/-- The finite-dimensional Wilson Gibbs pushforwards associated with a coherent
realization. -/
noncomputable def FiniteWilsonGibbsCoherentProjectiveRealization.finiteMarginal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (J : Finset EuclideanFourSpace) :
    Measure (∀ x : J, R.fieldValue x) :=
  (W.system (R.scale J)).gibbsMeasure.map (R.observe J)

/-- Coordinate restriction between dependent finite products is measurable. -/
theorem finite_wilson_gibbs_finset_restrict_measurable
    {α : EuclideanFourSpace → Type}
    [∀ x, MeasurableSpace (α x)]
    {I J : Finset EuclideanFourSpace}
    (hJI : J ⊆ I) :
    Measurable (Finset.restrict₂ hJI :
      (∀ x : I, α x) → (∀ x : J, α x)) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- Gibbs-measure preservation under coarse graining and pointwise observation
compatibility imply projective consistency of all finite-dimensional
pushforward distributions. -/
theorem finite_wilson_gibbs_coherent_pushforwards_projective
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W) :
    IsProjectiveMeasureFamily R.finiteMarginal := by
  intro I J hJI
  let μI := (W.system (R.scale I)).gibbsMeasure
  let μJ := (W.system (R.scale J)).gibbsMeasure
  let c := R.coarseGrain I J hJI
  let oI := R.observe I
  let oJ := R.observe J
  let r : (∀ x : I, R.fieldValue x) → (∀ x : J, R.fieldValue x) :=
    Finset.restrict₂ hJI
  have hc : Measurable c := R.coarseGrain_measurable I J hJI
  have hoI : Measurable oI := R.observe_measurable I
  have hoJ : Measurable oJ := R.observe_measurable J
  have hr : Measurable r :=
    finite_wilson_gibbs_finset_restrict_measurable hJI
  change μJ.map oJ = (μI.map oI).map r
  calc
    μJ.map oJ = (μI.map c).map oJ := by
      rw [R.gibbsMeasure_map_coarseGrain I J hJI]
    _ = μI.map (oJ ∘ c) := Measure.map_map hoJ hc
    _ = μI.map (r ∘ oI) := by
      congr 1
      funext A
      exact R.observe_coarseGrain I J hJI A
    _ = (μI.map oI).map r := (Measure.map_map hr hoI).symm

/-- The explicit restriction equation underlying the projective-family
predicate. -/
theorem finite_wilson_gibbs_coherent_marginal_restriction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (I J : Finset EuclideanFourSpace)
    (hJI : J ⊆ I) :
    R.finiteMarginal J =
      (R.finiteMarginal I).map (Finset.restrict₂ hJI) := by
  exact finite_wilson_gibbs_coherent_pushforwards_projective R I J hJI

/-- Forget the explicit coarse-graining witnesses after deriving the projective
compatibility theorem. -/
def FiniteWilsonGibbsCoherentProjectiveRealization.toProjectiveRealization
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W) :
    FiniteWilsonGibbsProjectiveRealization W :=
  { fieldValue := R.fieldValue
    fieldValueMeasurableSpace := R.fieldValueMeasurableSpace
    scale := R.scale
    observe := R.observe
    observe_measurable := R.observe_measurable
    pushforward_projective :=
      finite_wilson_gibbs_coherent_pushforwards_projective R }

/-- The projective cylinder family generated from coherent finite Wilson data has
marginals definitionally equal to the concrete Wilson Gibbs pushforwards. -/
theorem finite_wilson_gibbs_coherent_projective_family_marginal_eq_map
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (J : Finset EuclideanFourSpace) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J =
      (W.system (R.scale J)).gibbsMeasure.map (R.observe J) := by
  rfl

/-- Every coherent finite-Wilson marginal is a probability measure. -/
theorem finite_wilson_gibbs_coherent_marginal_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (J : Finset EuclideanFourSpace) :
    IsProbabilityMeasure
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) := by
  exact finite_wilson_gibbs_projective_marginal_probability
    R.toProjectiveRealization J

/-- On a measurable finite-dimensional event, the coherent marginal equals the
finite Wilson Gibbs probability of the observation preimage. -/
theorem finite_wilson_gibbs_coherent_marginal_apply
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J s =
      (W.system (R.scale J)).gibbsMeasure
        ((R.observe J) ⁻¹' s) := by
  exact finite_wilson_gibbs_projective_marginal_apply
    R.toProjectiveRealization J hs

/-- Once a projective-limit measure exists, every measurable continuum cylinder
has exactly the finite Wilson Gibbs probability prescribed by the coherent
observation map. -/
theorem finite_wilson_gibbs_coherent_projective_limit_cylinder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (L : EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    L.continuumMeasure (cylinder J s) =
      (W.system (R.scale J)).gibbsMeasure
        ((R.observe J) ⁻¹' s) := by
  exact finite_wilson_gibbs_projective_limit_cylinder_eq_gibbs_preimage
    R.toProjectiveRealization L J hs

/-- Audit-visible certificate showing that projectivity is derived from an
explicit measure-preserving coarse-graining diagram rather than supplied as an
unstructured proposition. -/
structure FiniteWilsonGibbsCoherentProjectiveCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W) where
  coarseGrainingMeasurable :
    ∀ I J hJI, Measurable (R.coarseGrain I J hJI)
  coarseGrainingPreservesGibbsMeasure :
    ∀ I J hJI,
      (W.system (R.scale I)).gibbsMeasure.map
          (R.coarseGrain I J hJI) =
        (W.system (R.scale J)).gibbsMeasure
  observationDiagramCommutes :
    ∀ I J hJI (A : (W.system (R.scale I)).Configuration),
      R.observe J (R.coarseGrain I J hJI A) =
        Finset.restrict₂ hJI (R.observe I A)
  projectiveMarginals :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal
  marginalProbability :
    ∀ J : Finset EuclideanFourSpace,
      IsProbabilityMeasure
        (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J)

/-- Construct the coherent coarse-graining/projectivity certificate. -/
def finiteWilsonGibbsCoherentProjectiveCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W) :
    FiniteWilsonGibbsCoherentProjectiveCertificate R :=
  { coarseGrainingMeasurable := R.coarseGrain_measurable
    coarseGrainingPreservesGibbsMeasure := R.gibbsMeasure_map_coarseGrain
    observationDiagramCommutes := R.observe_coarseGrain
    projectiveMarginals :=
      finite_wilson_gibbs_coherent_pushforwards_projective R
    marginalProbability :=
      finite_wilson_gibbs_coherent_marginal_probability R }

end

end MathlibAnalytic
end MGAP4D

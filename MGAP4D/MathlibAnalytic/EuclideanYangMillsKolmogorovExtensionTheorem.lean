import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- The measure-theoretic continuity hypothesis at the core of the general
Kolmogorov extension theorem.

For every decreasing sequence of measurable cylinder sets with empty
intersection, the associated projective cylinder content tends to zero.  Since
the cylinder content is finite, this condition upgrades finite additivity to
countable additivity on the cylinder ring. -/
structure EuclideanYangMillsKolmogorovExtensionCondition
    (F : EuclideanYangMillsProjectiveCylinderFamily) where
  cylinderContent_tendsto_zero :
    ∀ ⦃s : ℕ → Set F.Configuration⦄,
      (∀ n, s n ∈ measurableCylinders F.fieldValue) →
      Antitone s →
      (⋂ n, s n) = ∅ →
      Tendsto (fun n => F.cylinderContent (s n)) atTop (𝓝 0)

/-- Under the Kolmogorov continuity condition, the projective cylinder content
is sigma-subadditive and hence extends by Carathéodory to the product sigma
algebra. -/
theorem euclidean_yang_mills_projective_cylinderContent_sigmaSubadditive
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    F.cylinderContent.IsSigmaSubadditive := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  apply isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders
  intro f hf hfUnion hfDisjoint
  exact addContent_iUnion_eq_sum_of_tendsto_zero
    isSetRing_measurableCylinders
    F.cylinderContent
    (fun _ _ => projectiveFamilyContent_ne_top F.projective)
    K.cylinderContent_tendsto_zero
    hf hfUnion hfDisjoint

/-- The continuum measure obtained by extending the projective cylinder content
through Carathéodory's theorem. -/
noncomputable def euclideanYangMillsKolmogorovMeasure
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    Measure F.Configuration :=
  F.cylinderContent.measure
    isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    (euclidean_yang_mills_projective_cylinderContent_sigmaSubadditive K)

/-- The Carathéodory extension agrees with the projective content on every
measurable cylinder. -/
theorem euclidean_yang_mills_kolmogorovMeasure_cylinder
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, F.fieldValue x)}
    (hs : MeasurableSet s) :
    euclideanYangMillsKolmogorovMeasure K (cylinder J s) =
      F.finiteMarginal J s := by
  rw [euclideanYangMillsKolmogorovMeasure, AddContent.measure_eq]
  · exact projectiveFamilyContent_cylinder F.projective hs
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders J s hs

/-- The Carathéodory extension realizes all prescribed finite-dimensional
marginals and therefore is a projective-limit measure. -/
theorem euclidean_yang_mills_kolmogorovMeasure_isProjectiveLimit
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    IsProjectiveLimit (euclideanYangMillsKolmogorovMeasure K)
      F.finiteMarginal := by
  intro J
  ext s hs
  rw [Measure.map_apply]
  · exact euclidean_yang_mills_kolmogorovMeasure_cylinder K J hs
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  · exact hs

/-- The projective-limit object produced by the general Kolmogorov extension
route. -/
noncomputable def euclideanYangMillsKolmogorovProjectiveLimitMeasure
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    EuclideanYangMillsProjectiveLimitMeasure F :=
  { continuumMeasure := euclideanYangMillsKolmogorovMeasure K
    projectiveLimit :=
      euclidean_yang_mills_kolmogorovMeasure_isProjectiveLimit K }

/-- General Kolmogorov extension theorem for the typed Euclidean Yang--Mills
projective family: continuity from above of the finite projective cylinder
content implies existence of a measure with exactly the prescribed finite laws. -/
theorem euclidean_yang_mills_kolmogorov_projective_limit_exists
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    ∃ μ : Measure F.Configuration,
      IsProjectiveLimit μ F.finiteMarginal :=
  ⟨euclideanYangMillsKolmogorovMeasure K,
    euclidean_yang_mills_kolmogorovMeasure_isProjectiveLimit K⟩

/-- Structure-level existence form of the general Kolmogorov extension theorem. -/
theorem euclidean_yang_mills_kolmogorov_projective_limit_nonempty
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    Nonempty (EuclideanYangMillsProjectiveLimitMeasure F) :=
  ⟨euclideanYangMillsKolmogorovProjectiveLimitMeasure K⟩

/-- The Kolmogorov extension is a probability measure because all prescribed
finite-dimensional marginals are probability measures. -/
theorem euclidean_yang_mills_kolmogorovMeasure_probability
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    IsProbabilityMeasure (euclideanYangMillsKolmogorovMeasure K) := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact (euclidean_yang_mills_kolmogorovMeasure_isProjectiveLimit K)
    .isProbabilityMeasure

/-- The Kolmogorov extension is uniquely determined by its finite-dimensional
marginals. -/
theorem euclidean_yang_mills_kolmogorovMeasure_unique
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F)
    (ν : Measure F.Configuration)
    (hν : IsProjectiveLimit ν F.finiteMarginal) :
    ν = euclideanYangMillsKolmogorovMeasure K := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact hν.unique
    (euclidean_yang_mills_kolmogorovMeasure_isProjectiveLimit K)

/-- Audit-visible certificate for the general Kolmogorov extension route. -/
structure EuclideanYangMillsKolmogorovExtensionCertificate
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) where
  sigmaSubadditive : F.cylinderContent.IsSigmaSubadditive
  projectiveLimit :
    IsProjectiveLimit (euclideanYangMillsKolmogorovMeasure K)
      F.finiteMarginal
  probability :
    IsProbabilityMeasure (euclideanYangMillsKolmogorovMeasure K)
  cylinderFormula :
    ∀ (J : Finset EuclideanFourSpace)
      (s : Set (∀ x : J, F.fieldValue x)),
      MeasurableSet s →
        euclideanYangMillsKolmogorovMeasure K (cylinder J s) =
          F.finiteMarginal J s
  unique :
    ∀ ν : Measure F.Configuration,
      IsProjectiveLimit ν F.finiteMarginal →
        ν = euclideanYangMillsKolmogorovMeasure K

/-- Construct the certificate for the general Kolmogorov extension theorem. -/
def euclideanYangMillsKolmogorovExtensionCertificate
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    EuclideanYangMillsKolmogorovExtensionCertificate K :=
  { sigmaSubadditive :=
      euclidean_yang_mills_projective_cylinderContent_sigmaSubadditive K
    projectiveLimit :=
      euclidean_yang_mills_kolmogorovMeasure_isProjectiveLimit K
    probability :=
      euclidean_yang_mills_kolmogorovMeasure_probability K
    cylinderFormula := fun J _s hs =>
      euclidean_yang_mills_kolmogorovMeasure_cylinder K J hs
    unique := fun ν hν =>
      euclidean_yang_mills_kolmogorovMeasure_unique K ν hν }

end

end MathlibAnalytic
end MGAP4D

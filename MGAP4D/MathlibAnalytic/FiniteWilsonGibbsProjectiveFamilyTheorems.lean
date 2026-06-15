import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCoherentProjectiveMarginals
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCommonRefinementProjectiveMarginals
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveMarginals

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Direct Gibbs-preserving coarse graining proves the finite-dimensional
Wilson marginal restriction equation for every inclusion `J ⊆ I`. -/
theorem finite_wilson_gibbs_coherent_projective_restriction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (I J : Finset EuclideanFourSpace)
    (hJI : J ⊆ I) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J =
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal I).map
        (Finset.restrict₂ hJI) := by
  exact finite_wilson_gibbs_coherent_pushforwards_projective R I J hJI

/-- A common-refinement Wilson diagram proves the finite-dimensional marginal
restriction equation for every inclusion `J ⊆ I`. -/
theorem finite_wilson_gibbs_common_refinement_projective_restriction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    (I J : Finset EuclideanFourSpace)
    (hJI : J ⊆ I) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J =
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal I).map
        (Finset.restrict₂ hJI) := by
  exact finite_wilson_gibbs_common_refinement_projective R I J hJI

/-- Compatible observations of one fixed Wilson Gibbs measure prove the
finite-dimensional marginal restriction equation for every inclusion
`J ⊆ I`. -/
theorem finite_wilson_gibbs_single_source_projective_restriction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (I J : Finset EuclideanFourSpace)
    (hJI : J ⊆ I) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J =
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal I).map
        (Finset.restrict₂ hJI) := by
  exact finite_wilson_gibbs_single_source_projective R I J hJI

/-- The direct coarse-graining construction supplies a complete Mathlib
projective measure family. -/
theorem finite_wilson_gibbs_coherent_isProjectiveMeasureFamily
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W) :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal := by
  exact finite_wilson_gibbs_coherent_pushforwards_projective R

/-- The common-refinement construction supplies a complete Mathlib projective
measure family. -/
theorem finite_wilson_gibbs_common_refinement_isProjectiveMeasureFamily
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W) :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal := by
  exact finite_wilson_gibbs_common_refinement_projective R

/-- The single common Gibbs source construction supplies a complete Mathlib
projective measure family. -/
theorem finite_wilson_gibbs_single_source_isProjectiveMeasureFamily
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal := by
  exact finite_wilson_gibbs_single_source_projective R

/-- Audit-visible bundle collecting all three proved projective-family routes. -/
structure FiniteWilsonGibbsProjectiveFamilyTheoremBundle
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (coherent : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (commonRefinement : FiniteWilsonGibbsCommonRefinementRealization W)
    (singleSource : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  coherentProjective :
    IsProjectiveMeasureFamily
      coherent.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal
  commonRefinementProjective :
    IsProjectiveMeasureFamily
      commonRefinement.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal
  singleSourceProjective :
    IsProjectiveMeasureFamily
      singleSource.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal

/-- Construct the bundle of the three Wilson Gibbs projective-family proofs. -/
def finiteWilsonGibbsProjectiveFamilyTheoremBundle
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (coherent : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (commonRefinement : FiniteWilsonGibbsCommonRefinementRealization W)
    (singleSource : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    FiniteWilsonGibbsProjectiveFamilyTheoremBundle
      coherent commonRefinement singleSource :=
  { coherentProjective :=
      finite_wilson_gibbs_coherent_isProjectiveMeasureFamily coherent
    commonRefinementProjective :=
      finite_wilson_gibbs_common_refinement_isProjectiveMeasureFamily
        commonRefinement
    singleSourceProjective :=
      finite_wilson_gibbs_single_source_isProjectiveMeasureFamily singleSource }

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitThreeRoutes

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

section StandardBorel

variable (F : EuclideanYangMillsProjectiveCylinderFamily)
  [∀ x, StandardBorelSpace (F.fieldValue x)]

theorem standardBorel_route_compile_smoke :
    IsProjectiveLimit
      (euclideanYangMillsStandardBorelMeasure F) F.finiteMarginal :=
  euclidean_yang_mills_standardBorel_isProjectiveLimit F

end StandardBorel

section CompactTightness

variable (F : EuclideanYangMillsProjectiveCylinderFamily)
  [∀ x, TopologicalSpace (F.fieldValue x)]
  [∀ x, OpensMeasurableSpace (F.fieldValue x)]
  [∀ x, SecondCountableTopology (F.fieldValue x)]
  (T : EuclideanYangMillsCompactTightnessData F)

theorem compactTightness_route_compile_smoke :
    IsProjectiveLimit
      (euclideanYangMillsCompactTightMeasure F T) F.finiteMarginal :=
  euclidean_yang_mills_compactTight_isProjectiveLimit F T

end CompactTightness

section CountableSkeleton

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]
  (F : EuclideanYangMillsProjectiveCylinderFamily)
  (D : EuclideanYangMillsCountableSkeletonData F κ β)

theorem countableSkeleton_route_compile_smoke :
    IsProjectiveLimit D.continuumMeasure F.finiteMarginal :=
  D.isProjectiveLimit

noncomputable def countableSkeleton_projectiveLimit_compile_smoke :
    EuclideanYangMillsProjectiveLimitMeasure F :=
  D.projectiveLimitMeasure

end CountableSkeleton

end

end MathlibAnalytic
end MGAP4D

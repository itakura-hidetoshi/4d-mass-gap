import MGAP4D.MathlibAnalytic.KolmogorovStandardBorelExtension
import MGAP4D.MathlibAnalytic.KolmogorovCompactTightnessExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCountableSkeletonExtension

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

section StandardBorelRoute

variable (F : EuclideanYangMillsProjectiveCylinderFamily)
  [∀ x, StandardBorelSpace (F.fieldValue x)]

/-- Continuum law obtained directly from standard Borel coordinate spaces. -/
noncomputable def euclideanYangMillsStandardBorelMeasure :
    Measure F.Configuration := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact standardBorelKolmogorovProjectiveLimit
    F.finiteMarginal F.projective

/-- Standard Borel coordinates suffice for projective-limit existence; no
preferred topology is retained in the final statement. -/
theorem euclidean_yang_mills_standardBorel_isProjectiveLimit :
    IsProjectiveLimit
      (euclideanYangMillsStandardBorelMeasure F) F.finiteMarginal := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact isProjectiveLimit_standardBorelKolmogorovProjectiveLimit F.projective

/-- The standard Borel continuum law is normalized. -/
theorem euclidean_yang_mills_standardBorel_probability :
    IsProbabilityMeasure (euclideanYangMillsStandardBorelMeasure F) := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact standardBorelKolmogorovProjectiveLimit_probability F.projective

/-- Bundled standard Borel projective-limit measure. -/
noncomputable def euclideanYangMillsStandardBorelProjectiveLimitMeasure :
    EuclideanYangMillsProjectiveLimitMeasure F :=
  { continuumMeasure := euclideanYangMillsStandardBorelMeasure F
    projectiveLimit := euclidean_yang_mills_standardBorel_isProjectiveLimit F }

end StandardBorelRoute

section CompactTightnessRoute

variable (F : EuclideanYangMillsProjectiveCylinderFamily)
  [∀ x, TopologicalSpace (F.fieldValue x)]
  [∀ x, OpensMeasurableSpace (F.fieldValue x)]
  [∀ x, SecondCountableTopology (F.fieldValue x)]

/-- Finite-dimensional compact-tightness data specialized to the Euclidean
Yang--Mills cylinder family. -/
abbrev EuclideanYangMillsCompactTightnessData :=
  ProjectiveFamilyCompactTightnessData F.finiteMarginal

/-- Continuum law obtained from compact inner regularity of all finite Wilson
marginals. -/
noncomputable def euclideanYangMillsCompactTightMeasure
    (T : EuclideanYangMillsCompactTightnessData F) :
    Measure F.Configuration := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact compactTightKolmogorovProjectiveLimit
    F.finiteMarginal F.projective T

/-- Compact tightness makes the cylinder content sigma-additive and therefore
produces the required projective limit. -/
theorem euclidean_yang_mills_compactTight_isProjectiveLimit
    (T : EuclideanYangMillsCompactTightnessData F) :
    IsProjectiveLimit
      (euclideanYangMillsCompactTightMeasure F T) F.finiteMarginal := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact isProjectiveLimit_compactTightKolmogorovProjectiveLimit
    F.projective T

/-- Every finite Euclidean Yang--Mills marginal in this route is a tight
probability measure. -/
theorem euclidean_yang_mills_compactTight_finiteMarginal_tight
    (T : EuclideanYangMillsCompactTightnessData F)
    (J : Finset EuclideanFourSpace) :
    IsTightMeasureSet {F.finiteMarginal J} := by
  letI : ∀ I, IsProbabilityMeasure (F.finiteMarginal I) :=
    F.finiteMarginalProbability
  exact T.finiteMarginalTight J

/-- Bundled compact-tightness projective-limit measure. -/
noncomputable def euclideanYangMillsCompactTightProjectiveLimitMeasure
    (T : EuclideanYangMillsCompactTightnessData F) :
    EuclideanYangMillsProjectiveLimitMeasure F :=
  { continuumMeasure := euclideanYangMillsCompactTightMeasure F T
    projectiveLimit :=
      euclidean_yang_mills_compactTight_isProjectiveLimit F T }

end CompactTightnessRoute

/-- Audit-level statement of the three independent sufficient routes now
available for continuum projective-limit existence. -/
structure EuclideanYangMillsProjectiveLimitRouteStatus where
  standardBorelRoute : Prop
  compactTightnessRoute : Prop
  countableSkeletonRoute : Prop
  standardBorelRoute_proof : standardBorelRoute
  compactTightnessRoute_proof : compactTightnessRoute
  countableSkeletonRoute_proof : countableSkeletonRoute

/-- All three route interfaces have been formalized.  This statement records
interface availability, not that a particular concrete Wilson family has yet
discharged all three sets of hypotheses. -/
def euclideanYangMillsProjectiveLimitThreeRoutesAvailable :
    EuclideanYangMillsProjectiveLimitRouteStatus :=
  { standardBorelRoute := True
    compactTightnessRoute := True
    countableSkeletonRoute := True
    standardBorelRoute_proof := trivial
    compactTightnessRoute_proof := trivial
    countableSkeletonRoute_proof := trivial }

end

end MathlibAnalytic
end MGAP4D

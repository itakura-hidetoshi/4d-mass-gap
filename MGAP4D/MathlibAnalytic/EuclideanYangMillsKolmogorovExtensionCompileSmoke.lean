import MGAP4D.MathlibAnalytic.EuclideanYangMillsKolmogorovExtensionTheorem

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Compile gate: continuity from above makes the projective cylinder content
sigma-subadditive. -/
theorem euclidean_yang_mills_kolmogorov_sigmaSubadditive_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    F.cylinderContent.IsSigmaSubadditive :=
  euclidean_yang_mills_projective_cylinderContent_sigmaSubadditive K

/-- Compile gate: the Carathéodory extension is a projective-limit measure. -/
theorem euclidean_yang_mills_kolmogorov_isProjectiveLimit_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    IsProjectiveLimit (euclideanYangMillsKolmogorovMeasure K)
      F.finiteMarginal :=
  euclidean_yang_mills_kolmogorovMeasure_isProjectiveLimit K

/-- Compile gate: the general Kolmogorov extension route proves existence. -/
theorem euclidean_yang_mills_kolmogorov_exists_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    ∃ μ : Measure F.Configuration,
      IsProjectiveLimit μ F.finiteMarginal :=
  euclidean_yang_mills_kolmogorov_projective_limit_exists K

/-- Compile gate: the constructed Kolmogorov extension is a probability
measure. -/
theorem euclidean_yang_mills_kolmogorov_probability_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F) :
    IsProbabilityMeasure (euclideanYangMillsKolmogorovMeasure K) :=
  euclidean_yang_mills_kolmogorovMeasure_probability K

/-- Compile gate: every prescribed finite-dimensional law is recovered. -/
theorem euclidean_yang_mills_kolmogorov_marginal_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (K : EuclideanYangMillsKolmogorovExtensionCondition F)
    (J : Finset EuclideanFourSpace) :
    (euclideanYangMillsKolmogorovMeasure K).map J.restrict =
      F.finiteMarginal J :=
  euclidean_yang_mills_kolmogorovMeasure_isProjectiveLimit K J

end

end MathlibAnalytic
end MGAP4D

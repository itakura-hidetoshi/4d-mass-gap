import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonRandomScanHeatBathSweep

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Real total-variation distance between two probability mass functions on a
finite state space. -/
def finitePMFTotalVariationReal
    {α : Type*} [Fintype α]
    (p q : PMF α) : ℝ := by
  classical
  exact (2 : ℝ)⁻¹ *
    ∑ a : α, |(p a).toReal - (q a).toReal|

/-- Finite PMF total variation is nonnegative. -/
theorem finitePMFTotalVariationReal_nonneg
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    0 ≤ finitePMFTotalVariationReal p q := by
  classical
  unfold finitePMFTotalVariationReal
  positivity

/-- Two configurations agree away from one source link. -/
def FiniteLatticeWilsonSystem.AgreeAwayFrom
    (L : FiniteLatticeWilsonSystem)
    (source : L.Edge)
    (A B : L.Configuration) : Prop :=
  ∀ e : L.Edge, e ≠ source → A e = B e

/-- Total variation between the target-link conditional Wilson laws under two
boundary configurations. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge)
    (A B : L.Configuration) : ℝ :=
  finitePMFTotalVariationReal
    (L.singleLinkConditionalPMF A target)
    (L.singleLinkConditionalPMF B target)

/-- Conditional Wilson total variation is nonnegative. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_nonneg
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge)
    (A B : L.Configuration) :
    0 ≤ L.singleLinkConditionalTotalVariation target A B :=
  finitePMFTotalVariationReal_nonneg _ _

/-- A concrete Dobrushin influence certificate for a finite Wilson system.
`influence target source` bounds how much changing only `source` can change the
conditional law at `target`. -/
structure FiniteLatticeWilsonDobrushinInfluenceCertificate
    (L : FiniteLatticeWilsonSystem) where
  influence : L.Edge → L.Edge → ℝ
  influence_nonneg :
    ∀ target source : L.Edge, 0 ≤ influence target source
  conditional_tv_le_influence :
    ∀ (target source : L.Edge) (A B : L.Configuration),
      L.AgreeAwayFrom source A B →
        L.singleLinkConditionalTotalVariation target A B ≤
          influence target source
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  row_sum_le_rate :
    ∀ target : L.Edge,
      ∑ source : L.Edge, influence target source ≤ contractionRate
  exactGap_le_one_sub_rate :
    exactGapValueReal ≤ 1 - contractionRate

/-- The universal comparison step still needed after a Wilson influence matrix
has been bounded: its Dobrushin row sum contracts the concrete random-scan
heat-bath sweep in Gibbs variance. -/
def FiniteLatticeWilsonDobrushinVarianceComparisonPrinciple
    (L : FiniteLatticeWilsonSystem) : Prop :=
  ∀ C : FiniteLatticeWilsonDobrushinInfluenceCertificate L,
    ∀ f : L.Configuration → ℝ,
      L.gibbsVarianceReal (L.randomScanHeatBathSweep f) ≤
        C.contractionRate * L.gibbsVarianceReal f

/-- The variance-decomposition step for the concrete random-scan heat-bath
operator. This is separated from the Wilson-specific influence estimate. -/
def FiniteLatticeWilsonRandomScanVarianceDecompositionPrinciple
    (L : FiniteLatticeWilsonSystem) : Prop :=
  ∀ f : L.Configuration → ℝ,
    L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f +
        L.gibbsVarianceReal (L.randomScanHeatBathSweep f)

/-- A Dobrushin influence certificate, together with the two universal
random-scan comparison principles, generates the concrete contraction package. -/
noncomputable def
    finiteLatticeWilsonRandomScanContractionDataOfDobrushin
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinInfluenceCertificate L)
    (hDecomposition :
      FiniteLatticeWilsonRandomScanVarianceDecompositionPrinciple L)
    (hComparison :
      FiniteLatticeWilsonDobrushinVarianceComparisonPrinciple L) :
    FiniteLatticeWilsonRandomScanHeatBathContractionData L :=
  { contractionRate := C.contractionRate
    contractionRate_nonneg := C.contractionRate_nonneg
    contractionRate_lt_one := C.contractionRate_lt_one
    variance_decomposition := hDecomposition
    randomScan_variance_contraction := hComparison C
    exactGap_le_one_sub_rate := C.exactGap_le_one_sub_rate }

/-- A concrete Wilson Dobrushin certificate yields the exact-gap heat-bath
Poincare inequality once the universal comparison principles are supplied. -/
theorem finite_lattice_exactGap_heatBathPoincare_of_dobrushin
    (L : FiniteLatticeWilsonSystem)
    (C : FiniteLatticeWilsonDobrushinInfluenceCertificate L)
    (hDecomposition :
      FiniteLatticeWilsonRandomScanVarianceDecompositionPrinciple L)
    (hComparison :
      FiniteLatticeWilsonDobrushinVarianceComparisonPrinciple L) :
    L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_randomScanContraction
    L
    (finiteLatticeWilsonRandomScanContractionDataOfDobrushin
      L C hDecomposition hComparison)

end

end MathlibAnalytic
end MGAP4D

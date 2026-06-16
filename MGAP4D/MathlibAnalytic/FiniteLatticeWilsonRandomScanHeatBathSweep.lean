import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonHeatBathSweepContraction

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The exact one-link heat-bath operator acting on finite Wilson observables. -/
def FiniteLatticeWilsonSystem.singleLinkHeatBathOperator
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  fun A => L.singleLinkConditionalExpectation f A e

/-- The concrete random-scan heat-bath sweep: average the exact one-link
conditional-expectation operators over all lattice links. -/
def FiniteLatticeWilsonSystem.randomScanHeatBathSweep
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.Configuration → ℝ := by
  classical
  exact fun A =>
    (Fintype.card L.Edge : ℝ)⁻¹ *
      ∑ e : L.Edge, L.singleLinkHeatBathOperator e f A

/-- Pointwise expansion of the random-scan Wilson heat-bath sweep. -/
theorem finite_lattice_randomScanHeatBathSweep_apply
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) :
    L.randomScanHeatBathSweep f A =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge, L.singleLinkConditionalExpectation f A e := by
  rfl

/-- A contraction certificate specifically for the concrete random-scan
single-link Wilson heat-bath sweep. -/
structure FiniteLatticeWilsonRandomScanHeatBathContractionData
    (L : FiniteLatticeWilsonSystem) where
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  variance_decomposition :
    ∀ f : L.Configuration → ℝ,
      L.gibbsVarianceReal f ≤
        L.singleLinkHeatBathDirichletForm f +
          L.gibbsVarianceReal (L.randomScanHeatBathSweep f)
  randomScan_variance_contraction :
    ∀ f : L.Configuration → ℝ,
      L.gibbsVarianceReal (L.randomScanHeatBathSweep f) ≤
        contractionRate * L.gibbsVarianceReal f
  exactGap_le_one_sub_rate :
    exactGapValueReal ≤ 1 - contractionRate

/-- Forget that the sweep is the concrete random-scan Wilson operator and enter
the general sweep-contraction theorem. -/
noncomputable def
    FiniteLatticeWilsonRandomScanHeatBathContractionData.toSweepContractionData
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonRandomScanHeatBathContractionData L) :
    FiniteLatticeWilsonHeatBathSweepContractionData L :=
  { sweep := L.randomScanHeatBathSweep
    contractionRate := R.contractionRate
    contractionRate_nonneg := R.contractionRate_nonneg
    contractionRate_lt_one := R.contractionRate_lt_one
    variance_decomposition := R.variance_decomposition
    sweep_variance_contraction := R.randomScan_variance_contraction
    exactGap_le_one_sub_rate := R.exactGap_le_one_sub_rate }

/-- A variance contraction estimate for the actual random-scan Wilson
heat-bath sweep generates the finite exact-gap Poincare inequality. -/
theorem finite_lattice_exactGap_heatBathPoincare_of_randomScanContraction
    (L : FiniteLatticeWilsonSystem)
    (R : FiniteLatticeWilsonRandomScanHeatBathContractionData L) :
    L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_sweepContraction
    L R.toSweepContractionData

/-- Uniform random-scan contraction data for a finite Wilson approximation
family, using one common contraction rate. -/
structure FiniteLatticeWilsonApproximationFamily.UniformRandomScanHeatBathContractionData
    (F : FiniteLatticeWilsonApproximationFamily) where
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  variance_decomposition :
    ∀ (i : F.index) (f : (F.system i).Configuration → ℝ),
      (F.system i).gibbsVarianceReal f ≤
        (F.system i).singleLinkHeatBathDirichletForm f +
          (F.system i).gibbsVarianceReal
            ((F.system i).randomScanHeatBathSweep f)
  randomScan_variance_contraction :
    ∀ (i : F.index) (f : (F.system i).Configuration → ℝ),
      (F.system i).gibbsVarianceReal
          ((F.system i).randomScanHeatBathSweep f) ≤
        contractionRate * (F.system i).gibbsVarianceReal f
  exactGap_le_one_sub_rate :
    exactGapValueReal ≤ 1 - contractionRate

/-- Specialize uniform random-scan contraction data to one finite system. -/
noncomputable def
    FiniteLatticeWilsonApproximationFamily.UniformRandomScanHeatBathContractionData.toSystemData
    {F : FiniteLatticeWilsonApproximationFamily}
    (R : F.UniformRandomScanHeatBathContractionData)
    (i : F.index) :
    FiniteLatticeWilsonRandomScanHeatBathContractionData (F.system i) :=
  { contractionRate := R.contractionRate
    contractionRate_nonneg := R.contractionRate_nonneg
    contractionRate_lt_one := R.contractionRate_lt_one
    variance_decomposition := R.variance_decomposition i
    randomScan_variance_contraction := R.randomScan_variance_contraction i
    exactGap_le_one_sub_rate := R.exactGap_le_one_sub_rate }

/-- A uniform contraction rate for the concrete random-scan Wilson heat-bath
sweeps implies the family-wide exact-gap Poincare property. -/
theorem finite_lattice_uniform_exactGap_heatBathPoincare_of_randomScanContraction
    (F : FiniteLatticeWilsonApproximationFamily)
    (R : F.UniformRandomScanHeatBathContractionData) :
    F.UniformExactGapSingleLinkHeatBathPoincare := by
  intro i
  exact
    finite_lattice_exactGap_heatBathPoincare_of_randomScanContraction
      (F.system i) (R.toSystemData i)

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkApproximateTensorization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A one-sweep contraction certificate for the concrete finite Wilson Gibbs
law.  The sweep may later be instantiated by an ordered single-link heat-bath
sweep, a random scan, or a block update. -/
structure FiniteLatticeWilsonHeatBathSweepContractionData
    (L : FiniteLatticeWilsonSystem) where
  sweep : (L.Configuration → ℝ) → (L.Configuration → ℝ)
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  variance_decomposition :
    ∀ f : L.Configuration → ℝ,
      L.gibbsVarianceReal f ≤
        L.singleLinkHeatBathDirichletForm f +
          L.gibbsVarianceReal (sweep f)
  sweep_variance_contraction :
    ∀ f : L.Configuration → ℝ,
      L.gibbsVarianceReal (sweep f) ≤
        contractionRate * L.gibbsVarianceReal f
  exactGap_le_one_sub_rate :
    exactGapValueReal ≤ 1 - contractionRate

/-- Variance decomposition plus one-sweep contraction gives the quantitative
coercive estimate with coefficient `1 - contractionRate`. -/
theorem finite_lattice_one_sub_sweepRate_mul_variance_le_dirichlet
    (L : FiniteLatticeWilsonSystem)
    (S : FiniteLatticeWilsonHeatBathSweepContractionData L)
    (f : L.Configuration → ℝ) :
    (1 - S.contractionRate) * L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f := by
  have hDecomposition := S.variance_decomposition f
  have hContraction := S.sweep_variance_contraction f
  nlinarith

/-- A heat-bath sweep contracting variance at rate `ρ`, with
`exactGapValueReal ≤ 1 - ρ`, generates the concrete exact-gap Wilson Poincare
inequality. -/
theorem finite_lattice_exactGap_heatBathPoincare_of_sweepContraction
    (L : FiniteLatticeWilsonSystem)
    (S : FiniteLatticeWilsonHeatBathSweepContractionData L) :
    L.ExactGapSingleLinkHeatBathPoincare := by
  intro f
  calc
    exactGapValueReal * L.gibbsVarianceReal f ≤
        (1 - S.contractionRate) * L.gibbsVarianceReal f :=
      mul_le_mul_of_nonneg_right
        S.exactGap_le_one_sub_rate
        (finite_lattice_gibbsVarianceReal_nonneg L f)
    _ ≤ L.singleLinkHeatBathDirichletForm f :=
      finite_lattice_one_sub_sweepRate_mul_variance_le_dirichlet L S f

/-- Convert a sweep-contraction certificate into the approximate tensorization
package with constant `(1 - ρ)⁻¹`. -/
noncomputable def
    FiniteLatticeWilsonHeatBathSweepContractionData.toApproximateTensorizationData
    {L : FiniteLatticeWilsonSystem}
    (S : FiniteLatticeWilsonHeatBathSweepContractionData L) :
    FiniteLatticeWilsonSingleLinkApproximateTensorizationData L := by
  have hPositive : 0 < 1 - S.contractionRate :=
    sub_pos.mpr S.contractionRate_lt_one
  refine
    { tensorizationConstant := (1 - S.contractionRate)⁻¹
      tensorizationConstant_nonneg := inv_nonneg.mpr (le_of_lt hPositive)
      variance_le_constant_mul_dirichlet := ?_
      exactGap_mul_constant_le_one := ?_ }
  · intro f
    have hCoercive :=
      finite_lattice_one_sub_sweepRate_mul_variance_le_dirichlet L S f
    have hDiv :
        L.gibbsVarianceReal f ≤
          L.singleLinkHeatBathDirichletForm f /
            (1 - S.contractionRate) :=
      (le_div_iff₀ hPositive).2 hCoercive
    simpa [div_eq_mul_inv, mul_comm] using hDiv
  · have hDiv :
        exactGapValueReal / (1 - S.contractionRate) ≤ 1 := by
      apply (div_le_iff₀ hPositive).2
      simpa using S.exactGap_le_one_sub_rate
    simpa [div_eq_mul_inv] using hDiv

/-- Uniform sweep-contraction data for a whole finite Wilson approximation
family, with one common contraction rate. -/
structure FiniteLatticeWilsonApproximationFamily.UniformHeatBathSweepContractionData
    (F : FiniteLatticeWilsonApproximationFamily) where
  sweep :
    (i : F.index) →
      ((F.system i).Configuration → ℝ) →
        ((F.system i).Configuration → ℝ)
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  variance_decomposition :
    ∀ (i : F.index) (f : (F.system i).Configuration → ℝ),
      (F.system i).gibbsVarianceReal f ≤
        (F.system i).singleLinkHeatBathDirichletForm f +
          (F.system i).gibbsVarianceReal (sweep i f)
  sweep_variance_contraction :
    ∀ (i : F.index) (f : (F.system i).Configuration → ℝ),
      (F.system i).gibbsVarianceReal (sweep i f) ≤
        contractionRate * (F.system i).gibbsVarianceReal f
  exactGap_le_one_sub_rate :
    exactGapValueReal ≤ 1 - contractionRate

/-- Specialize a uniform sweep certificate to one finite Wilson system. -/
noncomputable def
    FiniteLatticeWilsonApproximationFamily.UniformHeatBathSweepContractionData.toSystemData
    {F : FiniteLatticeWilsonApproximationFamily}
    (S : F.UniformHeatBathSweepContractionData)
    (i : F.index) :
    FiniteLatticeWilsonHeatBathSweepContractionData (F.system i) :=
  { sweep := S.sweep i
    contractionRate := S.contractionRate
    contractionRate_nonneg := S.contractionRate_nonneg
    contractionRate_lt_one := S.contractionRate_lt_one
    variance_decomposition := S.variance_decomposition i
    sweep_variance_contraction := S.sweep_variance_contraction i
    exactGap_le_one_sub_rate := S.exactGap_le_one_sub_rate }

/-- A volume- and lattice-spacing-uniform one-sweep contraction certificate
implies the uniform exact-gap heat-bath Poincare property. -/
theorem finite_lattice_uniform_exactGap_heatBathPoincare_of_sweepContraction
    (F : FiniteLatticeWilsonApproximationFamily)
    (S : F.UniformHeatBathSweepContractionData) :
    F.UniformExactGapSingleLinkHeatBathPoincare := by
  intro i
  exact
    finite_lattice_exactGap_heatBathPoincare_of_sweepContraction
      (F.system i) (S.toSystemData i)

end

end MathlibAnalytic
end MGAP4D

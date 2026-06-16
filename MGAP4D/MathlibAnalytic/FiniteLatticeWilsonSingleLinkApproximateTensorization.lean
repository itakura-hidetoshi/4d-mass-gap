import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathDirichlet

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Quantitative approximate tensorization data for the concrete single-link
Wilson heat-bath Dirichlet form.  The tensorization constant is independent of
the observable; its eventual uniformity in volume and lattice spacing is the
remaining analytic target. -/
structure FiniteLatticeWilsonSingleLinkApproximateTensorizationData
    (L : FiniteLatticeWilsonSystem) where
  tensorizationConstant : ℝ
  tensorizationConstant_nonneg : 0 ≤ tensorizationConstant
  variance_le_constant_mul_dirichlet :
    ∀ f : L.Configuration → ℝ,
      L.gibbsVarianceReal f ≤
        tensorizationConstant * L.singleLinkHeatBathDirichletForm f
  exactGap_mul_constant_le_one :
    exactGapValueReal * tensorizationConstant ≤ 1

/-- An approximate tensorization estimate with a constant compatible with the
public exact gap generates the concrete Wilson heat-bath Poincare inequality. -/
theorem finite_lattice_exactGap_heatBathPoincare_of_approximateTensorization
    (L : FiniteLatticeWilsonSystem)
    (T : FiniteLatticeWilsonSingleLinkApproximateTensorizationData L) :
    L.ExactGapSingleLinkHeatBathPoincare := by
  intro f
  have hGapNonneg : 0 ≤ exactGapValueReal :=
    le_of_lt exactGapValueReal_pos
  have hDirichletNonneg :
      0 ≤ L.singleLinkHeatBathDirichletForm f :=
    finite_lattice_singleLinkHeatBathDirichletForm_nonneg L f
  calc
    exactGapValueReal * L.gibbsVarianceReal f ≤
        exactGapValueReal *
          (T.tensorizationConstant *
            L.singleLinkHeatBathDirichletForm f) :=
      mul_le_mul_of_nonneg_left
        (T.variance_le_constant_mul_dirichlet f)
        hGapNonneg
    _ = (exactGapValueReal * T.tensorizationConstant) *
        L.singleLinkHeatBathDirichletForm f := by
      rw [mul_assoc]
    _ ≤ 1 * L.singleLinkHeatBathDirichletForm f :=
      mul_le_mul_of_nonneg_right
        T.exactGap_mul_constant_le_one
        hDirichletNonneg
    _ = L.singleLinkHeatBathDirichletForm f := by
      rw [one_mul]

/-- A family-wide approximate tensorization estimate using one common constant
for every finite Wilson system. -/
structure FiniteLatticeWilsonApproximationFamily.UniformSingleLinkApproximateTensorizationData
    (F : FiniteLatticeWilsonApproximationFamily) where
  tensorizationConstant : ℝ
  tensorizationConstant_nonneg : 0 ≤ tensorizationConstant
  variance_le_constant_mul_dirichlet :
    ∀ (i : F.index) (f : (F.system i).Configuration → ℝ),
      (F.system i).gibbsVarianceReal f ≤
        tensorizationConstant *
          (F.system i).singleLinkHeatBathDirichletForm f
  exactGap_mul_constant_le_one :
    exactGapValueReal * tensorizationConstant ≤ 1

/-- Specialize uniform family data to one finite Wilson system. -/
noncomputable def
    FiniteLatticeWilsonApproximationFamily.UniformSingleLinkApproximateTensorizationData.toSystemData
    {F : FiniteLatticeWilsonApproximationFamily}
    (T : F.UniformSingleLinkApproximateTensorizationData)
    (i : F.index) :
    FiniteLatticeWilsonSingleLinkApproximateTensorizationData (F.system i) :=
  { tensorizationConstant := T.tensorizationConstant
    tensorizationConstant_nonneg := T.tensorizationConstant_nonneg
    variance_le_constant_mul_dirichlet :=
      T.variance_le_constant_mul_dirichlet i
    exactGap_mul_constant_le_one :=
      T.exactGap_mul_constant_le_one }

/-- A volume- and lattice-spacing-uniform approximate tensorization constant
implies the uniform exact-gap single-link Wilson Poincare property. -/
theorem finite_lattice_uniform_exactGap_heatBathPoincare_of_approximateTensorization
    (F : FiniteLatticeWilsonApproximationFamily)
    (T : F.UniformSingleLinkApproximateTensorizationData) :
    F.UniformExactGapSingleLinkHeatBathPoincare := by
  intro i
  exact
    finite_lattice_exactGap_heatBathPoincare_of_approximateTensorization
      (F.system i) (T.toSystemData i)

end

end MathlibAnalytic
end MGAP4D

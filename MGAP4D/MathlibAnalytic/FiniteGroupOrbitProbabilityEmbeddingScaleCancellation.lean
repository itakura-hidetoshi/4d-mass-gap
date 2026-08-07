import MGAP4D.MathlibAnalytic.FiniteGroupOrbitProbabilityL2Realization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The square-root-density pointwise scale obtained by comparing two finite
uniform configuration spaces through their orbit-probability coordinates. -/
noncomputable def finiteGroupOrbitProbabilityEmbeddingScale
    (Gf αf Gc αc : Type)
    [Group Gf]
    [Fintype αf]
    [Nonempty αf]
    [MulAction Gf αf]
    [Group Gc]
    [Fintype αc]
    [Nonempty αc]
    [MulAction Gc αc]
    (qf : FiniteGroupOrbitQuotient Gf αf)
    (qc : FiniteGroupOrbitQuotient Gc αc) : ℝ :=
  (Real.sqrt ((finiteGroupOrbitProbabilityL2Data Gf αf).weight qf) *
      (Real.sqrt (finiteGroupOrbitMass Gc αc qc) /
        Real.sqrt ((finiteGroupOrbitProbabilityL2Data Gc αc).weight qc))) /
    Real.sqrt (finiteGroupOrbitMass Gf αf qf)

/-- The corresponding configuration-cardinality scale. -/
noncomputable def finiteGroupConfigurationCardinalityEmbeddingScale
    (αf αc : Type)
    [Fintype αf]
    [Nonempty αf]
    [Fintype αc]
    [Nonempty αc] : ℝ :=
  Real.sqrt (Fintype.card αc : ℝ) /
    Real.sqrt (Fintype.card αf : ℝ)

/-- Orbit masses cancel exactly: for uniform finite configuration probability,
the pointwise scale depends only on the total fine/coarse configuration
cardinalities and not on the selected orbit classes. -/
theorem finiteGroupOrbitProbabilityEmbeddingScale_eq_cardinality
    (Gf αf Gc αc : Type)
    [Group Gf]
    [Fintype αf]
    [Nonempty αf]
    [MulAction Gf αf]
    [Group Gc]
    [Fintype αc]
    [Nonempty αc]
    [MulAction Gc αc]
    (qf : FiniteGroupOrbitQuotient Gf αf)
    (qc : FiniteGroupOrbitQuotient Gc αc) :
    finiteGroupOrbitProbabilityEmbeddingScale Gf αf Gc αc qf qc =
      finiteGroupConfigurationCardinalityEmbeddingScale αf αc := by
  let mf := finiteGroupOrbitMass Gf αf qf
  let mc := finiteGroupOrbitMass Gc αc qc
  let nf : ℝ := Fintype.card αf
  let nc : ℝ := Fintype.card αc
  have hmf : 0 < mf := finiteGroupOrbitMass_pos Gf αf qf
  have hmc : 0 < mc := finiteGroupOrbitMass_pos Gc αc qc
  have hnf : 0 < nf := by
    dsimp [nf]
    exact_mod_cast Fintype.card_pos
  have hnc : 0 < nc := by
    dsimp [nc]
    exact_mod_cast Fintype.card_pos
  have hwf : 0 < mf * nf⁻¹ := mul_pos hmf (inv_pos.mpr hnf)
  have hwc : 0 < mc * nc⁻¹ := mul_pos hmc (inv_pos.mpr hnc)
  have hScalePos :
      0 < finiteGroupOrbitProbabilityEmbeddingScale Gf αf Gc αc qf qc := by
    unfold finiteGroupOrbitProbabilityEmbeddingScale
    change 0 <
      (Real.sqrt (mf * nf⁻¹) *
        (Real.sqrt mc / Real.sqrt (mc * nc⁻¹))) /
        Real.sqrt mf
    exact div_pos
      (mul_pos (Real.sqrt_pos.2 hwf)
        (div_pos (Real.sqrt_pos.2 hmc) (Real.sqrt_pos.2 hwc)))
      (Real.sqrt_pos.2 hmf)
  have hCardScalePos :
      0 < finiteGroupConfigurationCardinalityEmbeddingScale αf αc := by
    unfold finiteGroupConfigurationCardinalityEmbeddingScale
    change 0 < Real.sqrt nc / Real.sqrt nf
    exact div_pos (Real.sqrt_pos.2 hnc) (Real.sqrt_pos.2 hnf)
  apply (sq_eq_sq₀ (le_of_lt hScalePos) (le_of_lt hCardScalePos)).mp
  unfold finiteGroupOrbitProbabilityEmbeddingScale
    finiteGroupConfigurationCardinalityEmbeddingScale
  change
    ((Real.sqrt (mf * nf⁻¹) *
        (Real.sqrt mc / Real.sqrt (mc * nc⁻¹))) /
        Real.sqrt mf) ^ 2 =
      (Real.sqrt nc / Real.sqrt nf) ^ 2
  rw [div_pow, mul_pow, div_pow, div_pow]
  rw [Real.sq_sqrt (le_of_lt hwf), Real.sq_sqrt (le_of_lt hmc),
    Real.sq_sqrt (le_of_lt hwc), Real.sq_sqrt (le_of_lt hmf),
    Real.sq_sqrt (le_of_lt hnc), Real.sq_sqrt (le_of_lt hnf)]
  field_simp [ne_of_gt hmf, ne_of_gt hmc, ne_of_gt hnf, ne_of_gt hnc]
  ring

/-- The generic cardinality scale is strictly positive. -/
theorem finiteGroupConfigurationCardinalityEmbeddingScale_pos
    (αf αc : Type)
    [Fintype αf]
    [Nonempty αf]
    [Fintype αc]
    [Nonempty αc] :
    0 < finiteGroupConfigurationCardinalityEmbeddingScale αf αc := by
  unfold finiteGroupConfigurationCardinalityEmbeddingScale
  exact div_pos
    (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos (α := αc)))
    (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos (α := αf)))

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRealPolarizationAdditivity
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic

/-!
# P4-Q2-BQ: full real bilinearity of ORIGINAL Wilson Haar reference polarization

BP established real-valued ADDITIVITY of the literal original Wilson
mass-weighted twelve-color reference polarization on the genuine bounded,
strongly measurable physical joint-observable core.

This file derives arbitrary real scalar homogeneity without assuming it:
the reference Q is nonnegative and satisfies the actual BN parallelogram
and BI scaling laws. The polarization is therefore bounded by Q(F)+Q(G).
For fixed F,G the additive function a ↦ B(a F,G) is bounded on a
neighborhood of 0 using Q(aF)=a² Q(F).

The pinned mathlib theorems AddMonoidHom.continuous_of_isBounded_nhds_zero
and map_real_smul upgrade this additive scalar function to a continuous
real-linear function. Symmetry upgrades linearity to the right variable.
The full real bilinear map is then constructed on the same original
physical Wilson bounded core.

No surrogate law, Dobrushin bound, reverse Haar-reference Poincare
inequality, or continuum spacing-scaled mass gap is inferred. Descent
from this concrete original core to physical joint L² remains separate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 1600000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Core" => p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "Q" => p4Q2BP_originalCoreReference H N hN beta hbeta
local notation "B" => p4Q2BP_originalCorePolarization H N hN beta hbeta

/-- The actual original real Haar reference is nonnegative even before
restricting to the bounded physical core. -/
theorem p4Q2BQ_originalCoreReference_nonneg (F : Core) :
    0 ≤ Q F := by
  change 0 ≤ p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
    H N hN beta hbeta F.1
  unfold p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
  exact ENNReal.toReal_nonneg

/-- Original Wilson reference quadratic scaling by ARBITRARY real numbers,
transported from BI to the actual bounded core. -/
theorem p4Q2BQ_originalCoreReference_smul (a : ℝ) (F : Core) :
    Q (a • F) = a ^ 2 * Q F := by
  change
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta (fun z => a * F.1 z) =
    a ^ 2 *
      p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H N hN beta hbeta F.1
  exact p4Q2BI_originalWilsonTwelveColorHaarReferenceReal_mul
    H N hN beta hbeta a F.1

/-- Real polarization is dominated in absolute value by the positive
reference energies of its arguments. No scalar linearity is assumed. -/
theorem p4Q2BQ_originalCorePolarization_abs_le
    (F G : Core) :
    |B F G| ≤ Q F + Q G := by
  have hp :=
    p4Q2BP_originalCoreReference_parallelogram
      H N hN beta hbeta F G
  have hplus : 0 ≤ Q (F + G) :=
    p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta (F + G)
  have hminus : 0 ≤ Q (F - G) :=
    p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta (F - G)
  change |(Q (F + G) - Q (F - G)) / 4| ≤ Q F + Q G
  apply abs_le.mpr
  constructor <;> linarith

/-- For fixed original Wilson core F,G, the scalar slice of its
already proved additive polarization is an additive ℝ → ℝ homomorphism. -/
noncomputable def p4Q2BQ_originalPolarization_scalarAddHom
    (F G : Core) : ℝ →+ ℝ where
  toFun := fun a => B (a • F) G
  map_zero' := by
    have h := p4Q2BP_originalCorePolarization_add_left
      H N hN beta hbeta (0 : Core) 0 G
    simp only [zero_add] at h
    have hz : B (0 : Core) G = 0 := by linarith
    simpa only [zero_smul] using hz
  map_add' := by
    intro a b
    change B ((a + b) • F) G = B (a • F) G + B (b • F) G
    rw [add_smul]
    exact p4Q2BP_originalCorePolarization_add_left
      H N hN beta hbeta (a • F) (b • F) G

/-- Local boundedness on the real scalar unit ball follows entirely from
original reference positivity and exact quadratic scaling, not an
unsupported pointwise original fiber mass floor. -/
theorem p4Q2BQ_originalPolarization_scalarAddHom_bounded_unitBall
    (F G : Core) :
    Bornology.IsBounded
      ((p4Q2BQ_originalPolarization_scalarAddHom
        H N hN beta hbeta F G) '' Metric.ball (0 : ℝ) 1) := by
  let ell := p4Q2BQ_originalPolarization_scalarAddHom
    H N hN beta hbeta F G
  have hF : 0 ≤ Q F :=
    p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta F
  refine (isBounded_iff_forall_norm_le (s := ell '' Metric.ball (0 : ℝ) 1)).2
    ⟨Q F + Q G, ?_⟩
  rintro t ⟨a, ha, rfl⟩
  have habs : |a| < 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ha
  have hsq : a ^ 2 ≤ 1 := by
    have hm : 0 ≤ (1 - |a|) * (1 + |a|) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [sq_abs a]
  have hb := p4Q2BQ_originalCorePolarization_abs_le
    H N hN beta hbeta (a • F) G
  rw [p4Q2BQ_originalCoreReference_smul H N hN beta hbeta a F] at hb
  have hmul : a ^ 2 * Q F ≤ Q F := by
    calc
      a ^ 2 * Q F ≤ 1 * Q F :=
        mul_le_mul_of_nonneg_right hsq hF
      _ = Q F := one_mul _
  change ‖B (a • F) G‖ ≤ Q F + Q G
  rw [Real.norm_eq_abs]
  exact hb.trans (by linarith)

/-- The additive scalar slice is continuous. Boundedness near 0 is
proved rather than assumed, so no pathological discontinuous additive
function can appear in the genuine Wilson polarization. -/
theorem p4Q2BQ_originalPolarization_scalarAddHom_continuous
    (F G : Core) :
    Continuous
      (p4Q2BQ_originalPolarization_scalarAddHom
        H N hN beta hbeta F G) := by
  let ell := p4Q2BQ_originalPolarization_scalarAddHom
    H N hN beta hbeta F G
  exact ell.continuous_of_isBounded_nhds_zero
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
    (p4Q2BQ_originalPolarization_scalarAddHom_bounded_unitBall
      H N hN beta hbeta F G)

/-- FIRST FULL REAL SCALAR HOMOGENEITY of the LITERAL original Wilson
polarization on the bounded strongly measurable physical joint core. -/
theorem p4Q2BQ_originalCorePolarization_smul_left
    (a : ℝ) (F G : Core) :
    B (a • F) G = a * B F G := by
  let ell := p4Q2BQ_originalPolarization_scalarAddHom
    H N hN beta hbeta F G
  have hc : Continuous ell :=
    p4Q2BQ_originalPolarization_scalarAddHom_continuous
      H N hN beta hbeta F G
  have hs := map_real_smul ell hc a (1 : ℝ)
  change B ((a • (1 : ℝ)) • F) G =
    a • B ((1 : ℝ) • F) G at hs
  simpa only [smul_eq_mul, mul_one, one_smul] using hs

/-- Real homogeneity in the second variable follows from the
already-formalized original reference polarization symmetry. -/
theorem p4Q2BQ_originalCorePolarization_smul_right
    (a : ℝ) (F G : Core) :
    B F (a • G) = a * B F G := by
  calc
    B F (a • G) = B (a • G) F :=
      p4Q2BP_originalCorePolarization_symm
        H N hN beta hbeta F (a • G)
    _ = a * B G F :=
      p4Q2BQ_originalCorePolarization_smul_left
        H N hN beta hbeta a G F
    _ = a * B F G := by
      rw [p4Q2BP_originalCorePolarization_symm
        H N hN beta hbeta G F]

/-- Genuine real bilinear map produced by polarizing the SAME original
Wilson mass-weighted twelve-color Haar reference on its bounded core.
Its diagonal is the original reference, not the physical E12 Dirichlet form. -/
noncomputable def p4Q2BQ_originalWilsonPolarBilin :
    LinearMap.BilinMap ℝ Core ℝ :=
  LinearMap.mk₂ ℝ
    (p4Q2BP_originalCorePolarization H N hN beta hbeta)
    (p4Q2BP_originalCorePolarization_add_left H N hN beta hbeta)
    (p4Q2BQ_originalCorePolarization_smul_left H N hN beta hbeta)
    (p4Q2BP_originalCorePolarization_add_right H N hN beta hbeta)
    (p4Q2BQ_originalCorePolarization_smul_right H N hN beta hbeta)

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D

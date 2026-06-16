import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonRandomScanHeatBathSweep
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite total-variation distance between two exact single-link Wilson
conditional laws. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge) : ℝ := by
  classical
  exact (2 : ℝ)⁻¹ *
    ∑ g : L.Gauge,
      |(L.singleLinkConditionalPMF A e g).toReal -
        (L.singleLinkConditionalPMF B e g).toReal|

/-- Conditional total variation is nonnegative. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_nonneg
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge) :
    0 ≤ L.singleLinkConditionalTotalVariation A B e := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun g _hg => abs_nonneg _)

/-- The conditional total variation vanishes when the two configurations agree
outside the link being resampled. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalTotalVariation A B e = 0 := by
  classical
  have hPMF :
      L.singleLinkConditionalPMF A e =
        L.singleLinkConditionalPMF B e :=
    finite_lattice_singleLinkConditionalPMF_eq_of_agreeOffLink
      L A B e hAgree
  simp [FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation, hPMF]

/-- A concrete Dobrushin influence matrix for one finite Wilson system.
`influence target source` bounds how much the conditional law at `target` can
change when only the `source` link is changed. -/
structure FiniteLatticeWilsonDobrushinInfluenceData
    (L : FiniteLatticeWilsonSystem) where
  influence : L.Edge → L.Edge → ℝ
  influence_nonneg :
    ∀ target source : L.Edge, 0 ≤ influence target source
  influence_diagonal_zero :
    ∀ e : L.Edge, influence e e = 0
  conditionalTotalVariation_le :
    ∀ (target source : L.Edge) (A B : L.Configuration),
      L.AgreeOffLink A B source →
        L.singleLinkConditionalTotalVariation A B target ≤
          influence target source
  dobrushinCoefficient : ℝ
  dobrushinCoefficient_nonneg : 0 ≤ dobrushinCoefficient
  rowSum_le_coefficient :
    ∀ target : L.Edge,
      ∑ source : L.Edge, influence target source ≤
        dobrushinCoefficient
  dobrushinCoefficient_lt_one : dobrushinCoefficient < 1

/-- The diagonal influence estimate is automatically compatible with exact
fiber invariance of the Wilson conditional law. -/
theorem finite_lattice_dobrushin_diagonal_totalVariation_zero
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinInfluenceData L)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalTotalVariation A B e =
      D.influence e e := by
  rw [finite_lattice_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
      L A B e hAgree,
    D.influence_diagonal_zero e]

/-- The Dobrushin row-sum criterion specialized to one finite Wilson system. -/
def FiniteLatticeWilsonSystem.HasDobrushinUniqueness
    (L : FiniteLatticeWilsonSystem) : Prop :=
  Nonempty (FiniteLatticeWilsonDobrushinInfluenceData L)

/-- A volume- and lattice-spacing-uniform Dobrushin influence package for a
finite Wilson approximation family. -/
structure FiniteLatticeWilsonApproximationFamily.UniformDobrushinInfluenceData
    (F : FiniteLatticeWilsonApproximationFamily) where
  influence :
    (i : F.index) →
      (F.system i).Edge → (F.system i).Edge → ℝ
  influence_nonneg :
    ∀ (i : F.index) (target source : (F.system i).Edge),
      0 ≤ influence i target source
  influence_diagonal_zero :
    ∀ (i : F.index) (e : (F.system i).Edge),
      influence i e e = 0
  conditionalTotalVariation_le :
    ∀ (i : F.index)
      (target source : (F.system i).Edge)
      (A B : (F.system i).Configuration),
      (F.system i).AgreeOffLink A B source →
        (F.system i).singleLinkConditionalTotalVariation A B target ≤
          influence i target source
  dobrushinCoefficient : ℝ
  dobrushinCoefficient_nonneg : 0 ≤ dobrushinCoefficient
  rowSum_le_coefficient :
    ∀ (i : F.index) (target : (F.system i).Edge),
      ∑ source : (F.system i).Edge,
          influence i target source ≤ dobrushinCoefficient
  dobrushinCoefficient_lt_one : dobrushinCoefficient < 1

/-- Restrict a uniform Dobrushin package to one finite Wilson system. -/
noncomputable def
    FiniteLatticeWilsonApproximationFamily.UniformDobrushinInfluenceData.toSystemData
    {F : FiniteLatticeWilsonApproximationFamily}
    (D : F.UniformDobrushinInfluenceData)
    (i : F.index) :
    FiniteLatticeWilsonDobrushinInfluenceData (F.system i) :=
  { influence := D.influence i
    influence_nonneg := D.influence_nonneg i
    influence_diagonal_zero := D.influence_diagonal_zero i
    conditionalTotalVariation_le := D.conditionalTotalVariation_le i
    dobrushinCoefficient := D.dobrushinCoefficient
    dobrushinCoefficient_nonneg := D.dobrushinCoefficient_nonneg
    rowSum_le_coefficient := D.rowSum_le_coefficient i
    dobrushinCoefficient_lt_one := D.dobrushinCoefficient_lt_one }

/-- A uniform package yields Dobrushin uniqueness data at every finite scale. -/
theorem finite_lattice_uniform_dobrushin_has_system_data
    (F : FiniteLatticeWilsonApproximationFamily)
    (D : F.UniformDobrushinInfluenceData)
    (i : F.index) :
    (F.system i).HasDobrushinUniqueness :=
  ⟨D.toSystemData i⟩

end

end MathlibAnalytic
end MGAP4D

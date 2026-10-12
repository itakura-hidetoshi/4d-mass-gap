import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszOrthogonalSpectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

/-!
# P4-Q2-DX: ORIGINAL Wilson Haar Riesz restricted invertibility and spectral BAND

DW constructs the literal original mass-weighted Wilson Haar Riesz operator
A_W on the true physical Wilson ground-state joint L² and proves finite-
volume coercivity, annihilation of the original Wilson constant line,
continuous self-adjoint restriction to the constant-orthogonal space, and
a positive LOWER bound for its real Banach spectrum.

This file closes two further genuine original-operator consequences:
(1) the ACTUAL restricted Riesz endomorphism is a unit of the Banach algebra
    of bounded real-linear endomorphisms of the physical orthogonal sector;
(2) its WHOLE REAL spectrum lies in a finite band [κ_R(H,N,beta),12], not
    merely a positive half-line. The upper edge 12 is the original
    UNNORMALIZED twelve-color Haar sum coefficient from the verified BY
    quadratic estimate, not the normalized physical D12.

The proof uses the pinned mathlib coercive-unit lemma for real Hilbert
operators. No spectral compactness, pure-point assertion, synthetic
measure, interacting-conditionals commutation, or volume-uniform gap is
introduced. The positivity constant may depend on finite H,N,beta.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace NNReal

noncomputable section

set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

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

local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "V" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "A" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
local notation "R" =>
  p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta

/-- The original Wilson Riesz quadratic has the original literal
unnormalized 12-color upper coefficient on the genuine orthogonal sector.
No physical D12 conditional-expectation operator occurs here. -/
theorem p4Q2DX_restrictedOriginalWilsonRiesz_quadratic_le_twelve
    (x : Vᗮ) :
    inner ℝ (R x) x ≤ (12 : ℝ) * ‖x‖ ^ 2 := by
  change inner ℝ (A (x : J)) (x : J) ≤ (12 : ℝ) * ‖(x : J)‖ ^ 2
  exact p4Q2BY_originalFullJointRieszOperator_inner_le
    H N hN beta hbeta (x : J)

/-- Entire physical Wilson constant-orthogonal Riesz operator is a UNIT,
not merely injective: true bounded invertibility on the closed Hilbert
subspace, derived from the SAME positive DV/DW finite-volume estimate. -/
theorem p4Q2DX_restrictedOriginalWilsonRiesz_isUnit :
    IsUnit (R : (Vᗮ) →L[ℝ] (Vᗮ)) := by
  let W : Submodule ℝ J :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta)ᗮ
  let T : W →L[ℝ] W :=
    p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta
  obtain ⟨κ, hκ, hRay⟩ :=
    p4Q2DW_restrictedOriginalWilsonRiesz_positiveRayleigh H N hN beta hbeta
  let c : ℝ≥0 := ⟨κ, hκ.le⟩
  have hc : 0 < c := by
    change (0 : ℝ) < κ
    exact hκ
  change IsUnit T
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map T hc
  intro x
  have hbound : κ * ‖x‖ ^ 2 ≤ inner ℝ (T x) x := hRay x
  have hcoercive :
      ‖x‖ ^ 2 * (c : ℝ) ≤ inner ℝ (T x) x := by
    change ‖x‖ ^ 2 * κ ≤ inner ℝ (T x) x
    nlinarith [hbound]
  exact hcoercive.trans (by
    rw [Real.norm_eq_abs]
    exact le_abs_self _)

/-- The physical Wilson constant-orthogonal Riesz spectrum has BOTH edges:
the strictly positive lower spectral bound is DW, and t>12 is excluded
by quantitative invertibility of t·id - A_W using BY's original reference
12-coefficient. No density-of-eigenvectors assumption is made. -/
theorem p4Q2DX_restrictedOriginalWilsonRiesz_spectrum_subset_Icc :
    ∃ κ : ℝ, 0 < κ ∧
      spectrum ℝ R ⊆ Set.Icc κ (12 : ℝ) := by
  let W : Submodule ℝ J :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta)ᗮ
  let T : W →L[ℝ] W :=
    p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta
  obtain ⟨κ, hκ, hLowerSpec⟩ :=
    p4Q2DW_restrictedOriginalWilsonRiesz_spectrum_subset_Ici
      H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  intro t ht
  change κ ≤ t ∧ t ≤ (12 : ℝ)
  refine ⟨hLowerSpec ht, ?_⟩
  by_contra hnot
  have hlt : (12 : ℝ) < t := lt_of_not_ge hnot
  let c : ℝ≥0 := ⟨t - (12 : ℝ), le_of_lt (sub_pos.mpr hlt)⟩
  have hc : 0 < c := by
    change (0 : ℝ) < t - (12 : ℝ)
    exact sub_pos.mpr hlt
  have hunit : IsUnit ((algebraMap ℝ (W →L[ℝ] W)) t - T) := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
      ((algebraMap ℝ (W →L[ℝ] W)) t - T) hc
    intro x
    have hupper : inner ℝ (T x) x ≤ (12 : ℝ) * ‖x‖ ^ 2 :=
      p4Q2DX_restrictedOriginalWilsonRiesz_quadratic_le_twelve
        H N hN beta hbeta x
    have hshift :
        inner ℝ (((algebraMap ℝ (W →L[ℝ] W)) t - T) x) x =
          t * ‖x‖ ^ 2 - inner ℝ (T x) x := by
      simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, inner_sub_left, real_inner_smul_left]
    have hpositive :
        ‖x‖ ^ 2 * (c : ℝ) ≤
          inner ℝ (((algebraMap ℝ (W →L[ℝ] W)) t - T) x) x := by
      rw [hshift]
      change ‖x‖ ^ 2 * (t - (12 : ℝ)) ≤
        t * ‖x‖ ^ 2 - inner ℝ (T x) x
      nlinarith [hupper]
    exact hpositive.trans (by
      rw [Real.norm_eq_abs]
      exact le_abs_self _)
  have hnotmem :
      t ∉ spectrum ℝ (p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta) :=
    (spectrum.notMem_iff).2 hunit
  exact (hnotmem ht).elim

/-- Zero is explicitly in the real resolvent of the TRUE original
Wilson Riesz orthogonal restriction, with no compactness assumptions. -/
theorem p4Q2DX_restrictedOriginalWilsonRiesz_zero_notMem_spectrum :
    (0 : ℝ) ∉ spectrum ℝ R := by
  obtain ⟨κ, hκ, hband⟩ :=
    p4Q2DX_restrictedOriginalWilsonRiesz_spectrum_subset_Icc
      H N hN beta hbeta
  intro hz
  have hmem : (0 : ℝ) ∈ Set.Icc κ (12 : ℝ) := hband hz
  have hge : κ ≤ (0 : ℝ) := hmem.1
  linarith

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2DX_restrictedOriginalWilsonRiesz_isUnit
#print axioms MGAP4D.MathlibAnalytic.p4Q2DX_restrictedOriginalWilsonRiesz_spectrum_subset_Icc
#print axioms MGAP4D.MathlibAnalytic.p4Q2DX_restrictedOriginalWilsonRiesz_zero_notMem_spectrum

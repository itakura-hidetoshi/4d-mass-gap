import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMinimalFourCenterSU2WilsonV5_PZ37Q
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalKrylovFinrankThreeV5_PZ37O
import Mathlib.Tactic

/-!
# PZ37Q — from physical SU(2) center to all finite periods rank three

The original minimal spatial Wilson energy 32 center boundary is connected
to the genuine identity boundary by the original SU(2) rotation path,
applied simultaneously on four actual selected spatial links. IVT provides
a middle physical boundary with original spatial half-action exactly 4.
Together with 0 and 16 this meets PZ37P's *loop-corrected* coefficient
nonzero criterion, without discarding any H=0 exceptional Haar term.

Transport the resulting original literal Wilson minor through the already
kernel-checked D2/D3 posterior–Gram–physical synthesis equivalences.
The H=0 and nonminimal H≥1 cases then combine into an all-FINITE-volume
small-positive fine original SU(2) physical three-mode rank theorem.

Every small-fine radius is allowed to depend on H and the physical
contexts; there is NO U0 volume-uniform estimate, arbitrary-depth fine,
endpoint, strong-limit, spectral gap or continuum mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic
open scoped Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

local notation "SU" => SpecialUnitaryMatrixGroup 2
local notation "Cfg₀" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2
local notation "w₀" => p4Q2PS_originalHalfSpatialAction 0
local notation "B₁₆" => p4Q2PZ37Q_originalMinimalFourCenterBoundary

private theorem p4Q2PZ37Q_rotation_continuous :
    Continuous (specialUnitaryTwoRotation : ℝ → SU) := by
  refine Continuous.subtype_mk ?_ (fun t => (specialUnitaryTwoRotation t).property)
  change Continuous (fun t : ℝ => specialUnitaryTwoRotationMatrix t)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [specialUnitaryTwoRotationMatrix] <;>
    fun_prop

private theorem p4Q2PZ37Q_rotation_zero :
    specialUnitaryTwoRotation 0 = (1 : SU) := by
  apply Subtype.ext
  change specialUnitaryTwoRotationMatrix 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [specialUnitaryTwoRotationMatrix, Matrix.one_apply]

private theorem p4Q2PZ37Q_rotation_pi_center :
    specialUnitaryTwoRotation Real.pi = specialUnitaryTwoNegativeIdentity := by
  apply Subtype.ext
  change specialUnitaryTwoRotationMatrix Real.pi =
    -(1 : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [specialUnitaryTwoRotationMatrix, Matrix.one_apply,
      Real.cos_pi, Real.sin_pi]

/-- Original SU(2) continuous four-link rotation family, no independently
parameterized or artificial scalar spatial Wilson energy. -/
noncomputable def p4Q2PZ37Q_rotatedFourLinkBoundary (t : ℝ) : Cfg₀ :=
  fun e =>
    if p4Q2PZ37Q_originalMinimalSelected e = true then
      specialUnitaryTwoRotation t else 1

private theorem p4Q2PZ37Q_rotatedFourLinkBoundary_continuous :
    Continuous p4Q2PZ37Q_rotatedFourLinkBoundary := by
  apply continuous_pi
  intro e
  change Continuous (fun t : ℝ =>
    if p4Q2PZ37Q_originalMinimalSelected e = true then
      specialUnitaryTwoRotation t else (1 : SU))
  by_cases h : p4Q2PZ37Q_originalMinimalSelected e = true
  · simpa only [h, if_true] using p4Q2PZ37Q_rotation_continuous
  · simpa only [h, if_false] using
      (continuous_const : Continuous (fun _ : ℝ => (1 : SU)))

private theorem p4Q2PZ37Q_rotatedFourLinkBoundary_zero :
    p4Q2PZ37Q_rotatedFourLinkBoundary 0 =
      (fun _ => (1 : SU)) := by
  funext e
  cases h : p4Q2PZ37Q_originalMinimalSelected e <;>
    simp [p4Q2PZ37Q_rotatedFourLinkBoundary, h,
      p4Q2PZ37Q_rotation_zero]

private theorem p4Q2PZ37Q_rotatedFourLinkBoundary_pi :
    p4Q2PZ37Q_rotatedFourLinkBoundary Real.pi = B₁₆ := by
  funext e
  cases h : p4Q2PZ37Q_originalMinimalSelected e <;>
    simp [p4Q2PZ37Q_rotatedFourLinkBoundary,
      p4Q2PZ37Q_originalMinimalFourCenterBoundary,
      p4Q2PZ37Q_originalSU2CenterSign, h,
      p4Q2PZ37Q_rotation_pi_center]

/-- Three ACTUAL original minimal H=0 physical SU(2) boundaries whose
half-spatial Wilson action values are exactly 0,4,16. The middle
state is produced by continuous genuine SU(2) rotation and IVT. -/
theorem p4Q2PZ37Q_originalMinimalThreePhysicalBoundaryActions :
    ∃ A B C : Cfg₀, w₀ A = 0 ∧ w₀ B = 4 ∧ w₀ C = 16 := by
  let W := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction 0 2
  let f : ℝ → ℝ := fun t => W (p4Q2PZ37Q_rotatedFourLinkBoundary t)
  have hf : Continuous f :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous 0 2).comp
      p4Q2PZ37Q_rotatedFourLinkBoundary_continuous
  have hzero : f 0 = 0 := by
    change W (p4Q2PZ37Q_rotatedFourLinkBoundary 0) = 0
    rw [p4Q2PZ37Q_rotatedFourLinkBoundary_zero]
    exact p4Q2IY_allOneSpatialWilsonAction_zero 0
  have hpi : f Real.pi = 32 := by
    change W (p4Q2PZ37Q_rotatedFourLinkBoundary Real.pi) = 32
    rw [p4Q2PZ37Q_rotatedFourLinkBoundary_pi]
    exact p4Q2PZ37Q_originalMinimalFourCenterBoundary_spatialWilsonAction
  have hEightIcc : (8 : ℝ) ∈ Set.Icc (f 0) (f Real.pi) := by
    rw [hzero, hpi]
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨t, _ht, hft⟩ :=
    (intermediate_value_Icc (le_of_lt Real.pi_pos) hf.continuousOn) hEightIcc
  refine ⟨(fun _ => (1 : SU)), p4Q2PZ37Q_rotatedFourLinkBoundary t, B₁₆,
    ?_, ?_, ?_⟩
  · change (1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction 0 2
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink 0 => (1 : SU)) = 0
    rw [p4Q2IY_allOneSpatialWilsonAction_zero]
    norm_num
  · change (1 / 2 : ℝ) * f t = 4
    rw [hft]
    norm_num
  · exact p4Q2PZ37Q_originalMinimalFourCenterBoundary_halfAction

/-- Missing PZ37P geometric input is now a proved existence theorem on
the original H=0 SU(2) spatial boundary (including loop correction). -/
theorem p4Q2PZ37Q_originalMinimalCorrectedSeventhCoefficient_exists_nonzero :
    ∃ A B C : Cfg₀,
      p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient A B C ≠ 0 := by
  obtain ⟨A, B, C, hA, hB, hC⟩ :=
    p4Q2PZ37Q_originalMinimalThreePhysicalBoundaryActions
  exact ⟨A, B, C,
    p4Q2PZ37P_originalMinimalCorrectedCoefficient_nonzero_of_spread
      A B C hA hB hC⟩

section AllFinitePhysicalRanks

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))
local notation "Krylov" =>
  (fun j : Fin (2 + 1) => ((Fine ^ (j : ℕ)) U : Phys))
local notation "D3" =>
  p4Q2PD_originalWilsonThirdMomentGap
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "S" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "a" =>
  p4Q2PE_actualThirdMomentCoefficient
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- UNCONDITIONAL across every finite even spatial volume H≥0:
sufficiently small positive fine coupling gives the actual original
normalized Wilson Gauss-law physical three-mode Krylov finrank THREE. -/
theorem p4Q2PZ37Q_allFiniteSmallFine_originalPhysicalKrylov_finrank_three
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        Module.finrank ℝ (p4Q2AD_realFiniteSynthesis Krylov).range = 3) := by
  by_cases hZero : Hn = 0
  · exact p4Q2PZ37P_minimalSmallFine_originalPhysicalKrylov_finrank_three
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hZero hFrozen
      p4Q2PZ37Q_originalMinimalCorrectedSeventhCoefficient_exists_nonzero
      e e' left₀ right₀
  · have hH : 1 ≤ Hn := by omega
    exact p4Q2PZ37O_actualSmallFine_originalPhysicalKrylov_finrank_three
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hH hFrozen e e' left₀ right₀

/-- Physical Schur source, true posterior-fiber positive mass, and
nonzero signed GI receiver for every finite H≥0. The finite-volume
radius remains non-uniform and fine coupling remains small/positive. -/
theorem p4Q2PZ37Q_allFiniteSmallFine_originalThirdSource_mass_and_signedGI
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < D3 ∧
        0 < Mass (S 2 a) (Finset.univ : Finset Link) ∧
        ∃ z : Pair, Modal 2 e z a ≠ 0) := by
  by_cases hZero : Hn = 0
  · exact p4Q2PZ37P_minimalSmallFine_originalThirdSource_mass_and_signedGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hZero hFrozen
      p4Q2PZ37Q_originalMinimalCorrectedSeventhCoefficient_exists_nonzero
      e e' left₀ right₀
  · have hH : 1 ≤ Hn := by omega
    exact p4Q2PZ37O_actualSmallFine_originalThirdSource_mass_and_signedGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hH hFrozen e e' left₀ right₀

end AllFinitePhysicalRanks
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_originalMinimalThreePhysicalBoundaryActions
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_originalMinimalCorrectedSeventhCoefficient_exists_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_allFiniteSmallFine_originalPhysicalKrylov_finrank_three
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_allFiniteSmallFine_originalThirdSource_mass_and_signedGI

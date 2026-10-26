import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalKrylovFinrankThreeV5_PZ37O
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralSeventhCoefficientV5_PZ37M
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# P4-Q2-PZ37P — minimal physical period and the exact boundary-loop correction

At half-extent H=0 the true SU(2) Wilson seventh coefficient is NOT just the
Vandermonde: the actual 48-pair boundary loop polynomial contributes its
proven, explicitly evaluated wedge. Keep that correction in the exact
coefficient and control the eighth-order Taylor remainder.

A nonzero corrected seventh coefficient for one genuine minimal-period
boundary triple gives nonzero literal original double-Haar minor for ALL
sufficiently small positive fine couplings. Transfer through the unchanged
PJ, PE, PB and AF theorems to actual D2/D3, physical Gauss-law Krylov
rank three, positive original posterior-fiber Schur mass and nonzero
signed GI response. The remaining H=0 task is to construct a certified
SU(2) boundary triple with nonzero corrected coefficient. This module
does not assume the loop correction vanishes or assert the witness exists.

There are no volume-uniform, endpoint, arbitrary-depth or continuum claims.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

section MinimalCorrectedLiteralMinor

local notation "Cfg₀" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2
local notation "w₀" => p4Q2PS_originalHalfSpatialAction 0
local notation "Loop₀" => p4Q2PZ37L_originalMinimalBoundaryLoopSum
local notation "Budget₀" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget 0

/-- The *evaluated* original H=0 seventh coefficient, retaining the
physical 48-pair boundary-loop correction rather than dropping it. -/
noncomputable def p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient
    (A B C : Cfg₀) : ℝ :=
  -(PZ37VandermondeAlgebra.vandermonde (w₀ A) (w₀ B) (w₀ C))/512 -
    (3/8192 : ℝ) *
      p4Q2PZ37B_originalBoundaryWedge 0 w₀ Loop₀ A B C

/-- A genuinely nonzero corrected seventh coefficient forces the
actual unmodified double-Haar minor to be nonzero for every small
positive fine coupling. The correction is never assumed to vanish. -/
theorem p4Q2PZ37P_originalMinimalLiteralMinor_nonzero_smallPositive
    (A B C : Cfg₀)
    (hCoeff : p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient A B C ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t : ℝ, 0 < t → t < epsilon →
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor 0 t A B C ≠ 0 := by
  let c : ℝ := p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient A B C
  let M : ℝ := Budget₀
  have hc : c ≠ 0 := hCoeff
  have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨K, hK, hTaylor⟩ :=
    p4Q2PZ37M_originalLiteralWilsonMinor_minimal_loopCorrection A B C
  have hKp : 0 < K + 1 := by linarith
  have hMp : 0 < 1 + ‖2 * M‖ := by positivity
  let epsilon : ℝ :=
    min 1 (min (1 / (1 + ‖2 * M‖)) (‖c‖ / (K + 1)))
  have heps : 0 < epsilon := by
    dsimp only [epsilon]
    exact lt_min (by norm_num)
      (lt_min (div_pos (by norm_num) hMp) (div_pos hcNorm hKp))
  have hepsOne : epsilon ≤ 1 := by
    dsimp only [epsilon]
    exact min_le_left _ _
  have hepsM : epsilon ≤ 1 / (1 + ‖2 * M‖) := by
    dsimp only [epsilon]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hepsC : epsilon ≤ ‖c‖ / (K + 1) := by
    dsimp only [epsilon]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨epsilon, heps, ?_⟩
  intro t ht0 htEps
  have hBeta : ‖t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos ht0]
    exact (lt_of_lt_of_le htEps hepsOne).le
  have htM : t * (1 + ‖2 * M‖) < 1 :=
    (lt_div_iff₀ hMp).mp (lt_of_lt_of_le htEps hepsM)
  have hSmall : ‖t * (2 * M)‖ ≤ 1 := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos ht0]
    nlinarith
  have hUpper : t * (K + 1) < ‖c‖ :=
    (lt_div_iff₀ hKp).mp (lt_of_lt_of_le htEps hepsC)
  have hKsmall : K * t < ‖c‖ := by
    nlinarith
  have hHigher : K * ‖t‖ ^ 8 < ‖t ^ 7 * c‖ := by
    calc
      K * ‖t‖ ^ 8 = t ^ 7 * (K * t) := by
        rw [Real.norm_eq_abs, abs_of_pos ht0]
        ring
      _ < t ^ 7 * ‖c‖ :=
        mul_lt_mul_of_pos_left hKsmall (pow_pos ht0 7)
      _ = ‖t ^ 7 * c‖ := by
        simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos ht0]
  have hApprox :
      ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor 0 t A B C -
        t ^ 7 * c‖ ≤ K * ‖t‖ ^ 8 := by
    simpa only [c, p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient, M]
      using hTaylor t hBeta hSmall
  intro hzero
  rw [hzero, zero_sub, norm_neg] at hApprox
  exact (not_lt_of_ge hApprox) hHigher

end MinimalCorrectedLiteralMinor

section MinimalPhysicalSchurAndKrylov

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Cfg₀" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2
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
local notation "D2" =>
  p4Q2PD_originalWilsonTwoMomentDet
    Hn (beta (n + 1)) (hbeta (n + 1))
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

/-- The only missing input to the H=0 original-Wilson D3 gate is a
nonzero explicitly loop-corrected coefficient at one genuine triple. -/
theorem p4Q2PZ37P_minimalSmallFine_twoAndThreeMoments_pos
    (hZero : Hn = 0) (hFrozen : 0 < beta n)
    (hWitness : ∃ A B C : Cfg₀,
      p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient A B C ≠ 0)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < D2 ∧ 0 < D3) := by
  obtain ⟨delta₂, hdelta₂, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  obtain ⟨A, B, C, hCoeff⟩ := hWitness
  obtain ⟨delta₃, hdelta₃, hMinor⟩ :=
    p4Q2PZ37P_originalMinimalLiteralMinor_nonzero_smallPositive A B C hCoeff
  refine ⟨min delta₂ delta₃, lt_min hdelta₂ hdelta₃, ?_⟩
  intro ht hsmall
  have hSmallTwo : beta (n + 1) < delta₂ :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have hSmallMinor : beta (n + 1) < delta₃ :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hD2 : 0 < D2 := hTwo ht hSmallTwo
  have hLiteral :
      ∃ X Y Z : Cfg,
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor
          Hn (beta (n + 1)) X Y Z ≠ 0 := by
    rw [hZero]
    exact ⟨A, B, C, hMinor (beta (n + 1)) ht hSmallMinor⟩
  have hD3 : 0 < D3 :=
    (p4Q2PJ_originalThirdMoment_pos_iff_exists_literalWilsonKernelMinor
      Hn (beta (n + 1)) (hbeta (n + 1)) hD2).mpr hLiteral
  exact ⟨hD2, hD3⟩

/-- H=0 original normalized Gauss-law three-mode Gram has full rank
under the *explicit* minimal-period seventh-coefficient witness. -/
theorem p4Q2PZ37P_minimalSmallFine_originalPhysicalKrylov_finrank_three
    (hZero : Hn = 0) (hFrozen : 0 < beta n)
    (hWitness : ∃ A B C : Cfg₀,
      p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient A B C ≠ 0)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        Module.finrank ℝ (p4Q2AD_realFiniteSynthesis Krylov).range = 3) := by
  obtain ⟨delta, hdelta, hMoments⟩ :=
    p4Q2PZ37P_minimalSmallFine_twoAndThreeMoments_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hZero hFrozen hWitness e e' left₀ right₀
  have hGram :
      Matrix.gram ℝ Krylov =
        p4Q2PD_originalWilsonThreeHankel
          Hn (beta (n + 1)) (hbeta (n + 1)) := by
    simpa only [p4Q2PD_originalWilsonThreeHankel] using
      (p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel
        Hn (beta (n + 1)) (hbeta (n + 1)) 2)
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  have hDet :
      0 < (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1))).det := by
    rw [p4Q2PD_originalWilsonThreeHankel_det_eq_gap]
    exact (hMoments ht hsmall).2
  have hUnitDet :
      IsUnit (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1))).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hDet)
  have hRank :=
    Matrix.rank_mul_eq_left_of_isUnit_det
      (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1)))
      (1 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ)
      hUnitDet
  have hThree :
      (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1))).rank = 3 := by
    simpa only [one_mul, Matrix.rank_one, Fintype.card_fin] using hRank
  calc
    Module.finrank ℝ (p4Q2AD_realFiniteSynthesis Krylov).range =
        (Matrix.gram ℝ Krylov).rank :=
          (p4Q2AF_realFiniteGram_rank_eq_physical_finrank Krylov).symm
    _ = (p4Q2PD_originalWilsonThreeHankel
          Hn (beta (n + 1)) (hbeta (n + 1))).rank := by
          rw [hGram]
    _ = 3 := hThree

/-- Same authentic original Schur source and positive frozen posterior:
the corrected H=0 seventh-coefficient witness implies both strictly
positive physical posterior-fiber mass and a nonzero signed GI receiver. -/
theorem p4Q2PZ37P_minimalSmallFine_originalThirdSource_mass_and_signedGI
    (hZero : Hn = 0) (hFrozen : 0 < beta n)
    (hWitness : ∃ A B C : Cfg₀,
      p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient A B C ≠ 0)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < D3 ∧
        0 < Mass (S 2 a) (Finset.univ : Finset Link) ∧
        ∃ z : Pair, Modal 2 e z a ≠ 0) := by
  obtain ⟨delta, hdelta, hMoments⟩ :=
    p4Q2PZ37P_minimalSmallFine_twoAndThreeMoments_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hZero hFrozen hWitness e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  obtain ⟨hD2, hD3⟩ := hMoments ht hsmall
  have hMass : 0 < Mass (S 2 a) (Finset.univ : Finset Link) :=
    (p4Q2PE_actualThirdMoment_postMass_pos_iff_thirdGap_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ hD2).mpr hD3
  have hGI : ∃ z : Pair, Modal 2 e z a ≠ 0 :=
    (p4Q2PE_actualThirdMoment_trueSignedGI_exists_iff_thirdGap_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ hD2).mpr hD3
  exact ⟨hD3, hMass, hGI⟩

end MinimalPhysicalSchurAndKrylov

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37P_originalMinimalLiteralMinor_nonzero_smallPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37P_minimalSmallFine_twoAndThreeMoments_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37P_minimalSmallFine_originalPhysicalKrylov_finrank_three
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37P_minimalSmallFine_originalThirdSource_mass_and_signedGI

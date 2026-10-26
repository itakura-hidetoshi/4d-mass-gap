import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralMinorThirdGapV5_PZ37O
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonThirdMomentPosteriorMassCriterionV5_PE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37O — the true Gauss-law and posterior-fiber third rank

At each NONMINIMAL spatial period, join two independently proved strict
small-positive original-Wilson intervals:

* PE/PC: the true normalized physical first two moment pivot D2 is positive
  at a frozen-positive / fine-positive coupling pair.
* PZ37N and PJ: the literal interacting SU(2) one-/two-slab Wilson minor is
  nonzero, so the actual third Hankel-Schur gap D3 is positive under D2 > 0.

This yields an unconditional (on the common small-positive fine interval)
positive physical three-by-three Wilson Hankel determinant, a strictly
positive true signed posterior GL mass of the genuine Gauss-law Krylov-Schur
source, and a nonzero original two-interacting-posterior signed GI receiver.

The spatial volume and frozen coupling remain fixed, and the fine radius
depends on the volume and auxiliary chosen contexts; this is NOT U0,
uniform fine-by-all-depth, an endpoint statement, or a continuum gap.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

section PhysicalSmallPositiveThirdRank

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "D2" => p4Q2PD_originalWilsonTwoMomentDet
  Hn (beta (n + 1)) (hbeta (n + 1))
local notation "D3" => p4Q2PD_originalWilsonThirdMomentGap
  Hn (beta (n + 1)) (hbeta (n + 1))
local notation "Src" => p4Q2PE_actualThirdMomentCoefficient
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Mass" => p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  Hn (beta n) (hbeta n)

/-- For every nonminimal even volume and any genuine positive frozen
coupling, there exists a common small-positive fine interval where the
original Gauss-law Wilson rank-three Hankel determinant is positive,
and the SAME true physical Schur source is detected by the unchanged
two-posterior GL mass and the signed GI expectation receiver.

The existential epsilon depends on H and the input physical contexts.
No third-rank premise or artificial posterior is inserted. -/
theorem p4Q2PZ37O_actualNonminimal_smallFine_hankel_postMass_trueGI
    (hH : 1 ≤ Hn) (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < D2 ∧
        0 < D3 ∧
        0 < (p4Q2PD_originalWilsonThreeHankel
          Hn (beta (n + 1)) (hbeta (n + 1))).det ∧
        0 < Mass (S 2 Src) (Finset.univ : Finset Link) ∧
        ∃ z : Cfg × Cfg, M 2 e z Src ≠ 0) := by
  obtain ⟨delta₂, hdelta₂, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  obtain ⟨delta₃, hdelta₃, hThird⟩ :=
    p4Q2PZ37O_originalNonminimal_smallPositive_thirdGap_of_twoPivot Hn hH
  refine ⟨min delta₂ delta₃, lt_min hdelta₂ hdelta₃, ?_⟩
  intro hFine hSmall
  have hSmall₂ : beta (n + 1) < delta₂ :=
    lt_of_lt_of_le hSmall (min_le_left _ _)
  have hSmall₃ : beta (n + 1) < delta₃ :=
    lt_of_lt_of_le hSmall (min_le_right _ _)
  have hD2 : 0 < D2 := hTwo hFine hSmall₂
  have hD3 : 0 < D3 :=
    hThird (beta (n + 1)) (hbeta (n + 1)) hFine hSmall₃ hD2
  have hDet :
      0 < (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1))).det := by
    rw [p4Q2PD_originalWilsonThreeHankel_det_eq_gap]
    exact hD3
  have hMass :
      0 < Mass (S 2 Src) (Finset.univ : Finset Link) :=
    (p4Q2PE_actualThirdMoment_postMass_pos_iff_thirdGap_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ hD2).mpr hD3
  have hGI : ∃ z : Cfg × Cfg, M 2 e z Src ≠ 0 :=
    (p4Q2PE_actualThirdMoment_trueSignedGI_exists_iff_thirdGap_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ hD2).mpr hD3
  exact ⟨hD2, hD3, hDet, hMass, hGI⟩

end PhysicalSmallPositiveThirdRank
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_actualNonminimal_smallFine_hankel_postMass_trueGI

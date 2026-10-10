import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorAllTimeExcitedRate
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# P4-Q2-AJ1: actual finite-volume Wilson spectral deficit and a physical mass rate

P4-Q2-AI proved all-power contraction of the genuine centered SU(2)
Wilson physical source, and isolated the missing spacing-rate estimate.

The ACTUAL excited norm q(H,beta) = ‖S(H,beta)-P(H,beta)‖ has
  0 ≤ q < 1
at each fixed finite physical Wilson volume. At any positive spacing a,
this produces a **positive finite-volume** mass certificate
  m(H,beta,a) = (1-q)/a > 0,
  q ≤ exp(-m*a).
There is NO asserted lower bound on m uniform in H or spacing.

We also show the exact sufficient physical frontier:
an estimate on the genuine Wilson spectral DEFICIT
  m*a_n ≤ 1 - ‖S_n-P_n‖
implies the uniform-in-n exponential bound on every actual centered
Krylov physical source. This is NOT a claim that the deficit hypothesis
has been established by the finite Wilson interaction.

We never replace the original transfer, top projection, frozen
posterior or pair-Haar law; no Dobrushin, proxy Gram, sorry/admit/axioms,
or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 850000

/-- Any nonnegative strict one-step contraction q<1 yields the explicit
positive finite-spacing mass rate (1-q)/a. This also covers q=0. -/
theorem p4Q2AJ_strictFactor_finiteDeficitMassCertificate
    (q spacing : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hspacing : 0 < spacing) :
    0 < (1-q)/spacing ∧
      q ≤ Real.exp (-((1-q)/spacing)*spacing) := by
  have hmass : 0 < (1-q)/spacing :=
    div_pos (sub_pos.mpr hq1) hspacing
  have hquot : -((1-q)/spacing)*spacing = -(1-q) := by
    field_simp [ne_of_gt hspacing]
    ring
  have hExp : 1-(1-q) ≤ Real.exp (-(1-q)) := by
    have h := Real.add_one_le_exp (-(1-q))
    linarith
  refine ⟨hmass, ?_⟩
  calc
    q = 1-(1-q) := by ring
    _ ≤ Real.exp (-(1-q)) := hExp
    _ = Real.exp (-((1-q)/spacing)*spacing) := by rw [hquot]

/-- A *linear-in-spacing* lower bound for the actual spectral deficit
is sufficient to certify the spacing-exponential one-step bound.
No positivity of q is necessary; hence the q=0 sector is included. -/
theorem p4Q2AJ_deficit_lower_implies_exp_upper
    (q spacing mass : ℝ)
    (hdeficit : mass*spacing ≤ 1-q) :
    q ≤ Real.exp (-mass*spacing) := by
  have hLinear : q ≤ 1 - mass*spacing := by linarith
  have hExp := Real.add_one_le_exp (-mass*spacing)
  linarith

local instance p4AJGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AJCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AJSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AJMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AJBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AJLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AJComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Finite-H positivity of the REAL Wilson normalized excited mass rate,
obtained only from the genuine centered-transfer norm q(H,beta)<1.
The same physical spacing may depend on H; uniformity is not assumed. -/
theorem physicalOriginalNormalizedFineTransfer_exists_finiteDeficitMass
    (H : ℕ) (fine : ℝ) (hFine : 0 ≤ fine)
    (spacing : ℝ) (hspacing : 0 < spacing) :
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
    ∃ m : ℝ, 0 < m ∧ ‖S-P‖ ≤ Real.exp (-m*spacing) := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  have hq : ‖S-P‖ < 1 :=
    physicalOriginalNormalizedFineTransfer_sub_topSpectralProjection_norm_lt_one
      H fine hFine
  obtain ⟨hpos, hexp⟩ :=
    p4Q2AJ_strictFactor_finiteDeficitMassCertificate
      ‖S-P‖ spacing (norm_nonneg (S-P)) hq hspacing
  exact ⟨(1-‖S-P‖)/spacing, hpos, hexp⟩

/-- Genuine centered Wilson source: every individual finite volume and
positive lattice spacing has SOME positive decay mass, depending on
the actual finite-H spectral deficit. No shared mass over n is obtained. -/
theorem fineRightKrylov_originalWilson_centeredSource_exists_finiteMassRate
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ)
    (hCenter : (∑ j : Fin (r+1), a j) = 0)
    (spacing : ℝ) (hspacing : 0 < spacing) :
    let H := halfExtent (n+1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    ∃ m : ℝ, 0 < m ∧ ∀ k : ℕ,
      ‖(S^k) F‖ ≤ Real.exp ((k : ℝ)*(-m*spacing))*‖F‖ := by
  let H := halfExtent (n+1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  obtain ⟨m, hm, hstep⟩ :=
    physicalOriginalNormalizedFineTransfer_exists_finiteDeficitMass
      H (beta (n+1)) (hbeta (n+1)) spacing hspacing
  refine ⟨m, hm, ?_⟩
  intro k
  exact fineRightKrylov_originalWilson_centeredSource_spacingRate_of_certifiedStep
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a hCenter spacing m hstep k

/-- Precise physical frontier: a COMMON mass m and the actual Wilson
one-step deficit bound m*a_n ≤ 1-q_n yield all-time exponential
contraction for every centered original Krylov physical source.
This theorem does NOT establish its missing physical hypothesis. -/
theorem fineRightKrylov_originalWilson_uniformDeficit_implies_allTimeMass
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (spacing : ℕ → ℝ) (mass : ℝ)
    (hPhysicalDeficit : ∀ n : ℕ,
      let H := halfExtent (n+1)
      let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
      let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
      mass*spacing n ≤ 1-‖S-P‖)
    (n r : ℕ) (a : Fin (r+1) → ℝ)
    (hCenter : (∑ j : Fin (r+1), a j) = 0)
    (k : ℕ) :
    let H := halfExtent (n+1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    ‖(S^k) F‖ ≤ Real.exp ((k : ℝ)*(-mass*spacing n))*‖F‖ := by
  let H := halfExtent (n+1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  have hdef : mass*spacing n ≤ 1-‖S-P‖ := hPhysicalDeficit n
  have hStep : ‖S-P‖ ≤ Real.exp (-mass*spacing n) :=
    p4Q2AJ_deficit_lower_implies_exp_upper
      ‖S-P‖ (spacing n) mass hdef
  exact fineRightKrylov_originalWilson_centeredSource_spacingRate_of_certifiedStep
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a hCenter (spacing n) mass hStep k

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

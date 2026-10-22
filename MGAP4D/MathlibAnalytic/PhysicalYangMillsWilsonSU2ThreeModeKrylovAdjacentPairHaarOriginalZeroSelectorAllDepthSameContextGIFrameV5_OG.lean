import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalKrylovZeroSelectorSignedDensityFloorV5_OF
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIModalLinearityAnyFineBetaV5_HF
import Mathlib.Tactic

/-!
# P4-Q2-OG — true original-Wilson SAME physical contexts for ALL finite Krylov depths

OF/GX prove the original fine-right Krylov zero-selector source
equals the SAME Gauss-law constant physical unit U for all finite r
at fixed scale n, with any original nonnegative fine beta(n+1).
OE proves true original two-posterior signed GI receiver Q_GI/N_H
positive square-floor for that very U at genuine physical contexts.

OG proves the quantifier strengthening:
  one pair of original Wilson contexts exists at fixed n and works
  for ALL finite depths r with the SAME Q_GI/N_H positive coefficient.
The contexts are independent of r because U and the original
frozen-beta interacting posterior density laws do not depend on r.

OG additionally proves the actual HF modal GI detector evaluated at
each TRUE zero-selector coefficient equals OD's exact signed
posterior functional on the unchanged original FF physical receiver
of U; these modal evaluations are identical across all depths.

No claim about arbitrary coefficient-source injectivity, positive-fine
arbitrary-r full detector, cross-scale endpoint identity, volume
uniform U0, continuum strong limit or 4D Yang-Mills mass gap.
Original Gauss-law source, two interacting Wilson posterior laws,
Perron joint half-density and both true Wilson actions unchanged.
No artificial rank/source assumption, independent-Haar model,
Dobrushin, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section RealOriginalAllDepth
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Unit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "N" => (p4Q2LP_originalSpatialPlaquetteCount Hn : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale (beta n)
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy
  Hn (beta n) (hbeta n)
local notation "Signed" => p4Q2OD_originalTwoPosteriorContrastCLM
  Hn (beta n) (hbeta n)
local notation "Fiber" => p4Q2OD_originalPhysicalSignedReceiverFiber
  Hn (beta n) (hbeta n)
local notation "Source" => p4Q2OF_actualRightZeroSelectorSource
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Modal" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- All true finite-depth Krylov zero-selector coefficient sources
at fixed n are literally the same original Gauss-law U. -/
theorem p4Q2OG_originalZeroSelector_physicalSource_depth_independent
    (r s : ℕ) : Source r = Source s := by
  rw [p4Q2OF_actualRightZeroSelectorSource_eq_unit,
    p4Q2OF_actualRightZeroSelectorSource_eq_unit]

/-- HF actual right Krylov GI modal detector at the zero selector
equals the original OD signed two-interacting-posterior functional
applied to the SAME original physical FF receiver fiber of U. -/
theorem p4Q2OG_originalZeroSelector_modal_eq_trueSignedUnit
    (r : ℕ) (e : Link) (z : Cfg × Cfg) :
    Modal r e z (p4Q2GX_rightZeroCoefficient r) =
      Signed z.2 e (Fiber Unit e z) := by
  have hHF :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (Source r) e z =
          Modal r e z (p4Q2GX_rightZeroCoefficient r) :=
    p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (p4Q2GX_rightZeroCoefficient r) e z
  calc
    Modal r e z (p4Q2GX_rightZeroCoefficient r) =
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (Source r) e z := hHF.symm
    _ = Signed z.2 e (Fiber (Source r) e z) :=
      p4Q2OD_originalPhysicalGI_eq_truePosteriorSignedFunctional
        Hn (beta n) (hbeta n) (Source r) e z
    _ = Signed z.2 e (Fiber Unit e z) :=
      p4Q2OF_actualRightZeroSelector_signedReceiver_eq_unit
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z

/-- Every fixed original link/context has the SAME real original
modal response on the true zero-selector coefficient at ALL r. -/
theorem p4Q2OG_originalZeroSelector_modal_depth_independent
    (r s : ℕ) (e : Link) (z : Cfg × Cfg) :
    Modal r e z (p4Q2GX_rightZeroCoefficient r) =
      Modal s e z (p4Q2GX_rightZeroCoefficient s) := by
  calc
    Modal r e z (p4Q2GX_rightZeroCoefficient r) =
        Signed z.2 e (Fiber Unit e z) :=
      p4Q2OG_originalZeroSelector_modal_eq_trueSignedUnit
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z
    _ = Modal s e z (p4Q2GX_rightZeroCoefficient s) :=
      (p4Q2OG_originalZeroSelector_modal_eq_trueSignedUnit
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n s e z).symm

/-- Stronger than OF's forall-depth / exists-context ordering:
ONE context pair at fixed n and one exact original Q_GI/N_H
positive GI coefficient works for ALL finite physical Krylov depths
of the canonical actual zero selector simultaneously. -/
theorem p4Q2OG_actualZeroSelector_exists_allDepth_sameContext_modalFloor
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < N ∧
      0 < Q e e' z z' / N ∧
      ∀ r : ℕ,
        (Q e e' z z' / N) / (10 * E^2) ≤
          (Modal r e z (p4Q2GX_rightZeroCoefficient r))^2 +
          (Modal r e' z' (p4Q2GX_rightZeroCoefficient r))^2 := by
  obtain ⟨z, z', hN, hQ, hBound⟩ :=
    p4Q2OE_originalPhysicalUnitReceiver_exists_meanEnergyDensityFloor
      Hn (beta n) (hbeta n) hFrozen e e' left₀ right₀
  refine ⟨z, z', hN, hQ, ?_⟩
  intro r
  rw [p4Q2OG_originalZeroSelector_modal_eq_trueSignedUnit
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z,
      p4Q2OG_originalZeroSelector_modal_eq_trueSignedUnit
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e' z']
  exact hBound

/-- At these same genuine contexts the original HF zero-selector
modal response cannot vanish in both rows for any finite depth.
All-coefficient source injectivity remains a different open claim. -/
theorem p4Q2OG_actualZeroSelector_exists_allDepth_sameContext_detected
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < Q e e' z z' / N ∧
      ∀ r : ℕ,
        Modal r e z (p4Q2GX_rightZeroCoefficient r) ≠ 0 ∨
        Modal r e' z' (p4Q2GX_rightZeroCoefficient r) ≠ 0 := by
  obtain ⟨z, z', hN, hQ, hFloor⟩ :=
    p4Q2OG_actualZeroSelector_exists_allDepth_sameContext_modalFloor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  have hE : 0 < E :=
    p4Q2LW_originalHarnackContrastScale_pos (beta n) hFrozen
  have hk : 0 < (Q e e' z z' / N) / (10 * E^2) :=
    div_pos hQ
      (mul_pos (by norm_num) (sq_pos_of_pos hE))
  refine ⟨z, z', hQ, ?_⟩
  intro r
  by_contra hBoth
  obtain ⟨hOne, hTwo⟩ := not_or.mp hBoth
  have hOne' : Modal r e z (p4Q2GX_rightZeroCoefficient r) = 0 :=
    of_not_not hOne
  have hTwo' : Modal r e' z' (p4Q2GX_rightZeroCoefficient r) = 0 :=
    of_not_not hTwo
  have hZero : (Q e e' z z' / N) / (10 * E^2) ≤ 0 := by
    simpa [hOne', hTwo'] using hFloor r
  exact (not_lt_of_ge hZero) hk

end RealOriginalAllDepth
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OG_originalZeroSelector_physicalSource_depth_independent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OG_originalZeroSelector_modal_eq_trueSignedUnit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OG_originalZeroSelector_modal_depth_independent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OG_actualZeroSelector_exists_allDepth_sameContext_modalFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OG_actualZeroSelector_exists_allDepth_sameContext_detected

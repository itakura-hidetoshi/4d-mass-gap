import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFineDepthOneGIPhysicalSourceInjectiveV5_ON
import Mathlib.Tactic

/-!
# P4-Q2-OO — original depth-two Krylov Schur residual, first-two actual GI rows

At true depth two the candidate original physical Wilson sources are
U, T_fine U, T_fine^2 U. ON proves independence of ONLY the first two
in a finite-volume small-positive-fine window. This module does not
assume a third independent source or a third separating GI detector.

Instead, it constructs the explicit coefficient Schur residual in
the real THREE-mode right-Krylov coefficient space and proves:
* its two selected genuine original Wilson GI rows vanish EXACTLY;
* its coefficient is NONZERO whenever OM's actual first-two minor
  is nonzero; this nonzero coefficient is NOT asserted to have
  nonzero synthesized physical source;
* the first-two determinant at genuine depth two is IDENTICAL to
  OM's proved actual depth-one two-context minor;
* the synthesized Schur residual is EXACTLY a genuine physical Hilbert
  combination of T_fine^2 U, U and T_fine U;
* every further modal GI row on this physical source is the
  UNMODIFIED original two-interacting-posterior signed receiver.

The new obstruction is the genuinely nonzero THIRD-row response or
equivalently third-mode physical nondegeneracy. No rank, third response,
new physical law, independent Haar posterior or volume-uniform bound
is postulated. In particular, this is NOT a 3-mode injectivity proof.
No sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The ACTUAL depth-two right-Krylov first selector (Fin 3). -/
def p4Q2OO_depthTwoFirstCoefficient : Fin (2 + 1) → ℝ :=
  fun j => if j = 1 then 1 else 0

/-- The ACTUAL depth-two right-Krylov second selector (Fin 3). -/
def p4Q2OO_depthTwoSecondCoefficient : Fin (2 + 1) → ℝ :=
  fun j => if j = 2 then 1 else 0

/-- All three real right-Krylov coefficients decompose in their literal
zero, first and second selectors. No source independence is assumed. -/
theorem p4Q2OO_depthTwo_coeff_decompose (a : Fin (2 + 1) → ℝ) :
    a = a 0 • p4Q2GX_rightZeroCoefficient 2 +
        a 1 • p4Q2OO_depthTwoFirstCoefficient +
        a 2 • p4Q2OO_depthTwoSecondCoefficient := by
  funext j
  fin_cases j <;>
    simp [p4Q2GX_rightZeroCoefficient,
      p4Q2OO_depthTwoFirstCoefficient,
      p4Q2OO_depthTwoSecondCoefficient,
      Pi.add_apply, Pi.smul_apply]

/-- The actual first-two modal receiver minor in the three-dimensional
coefficient space: the third column is deliberately NOT assumed
independent. -/
def p4Q2OO_depthTwoLeadingMinor
    (D D' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ) : ℝ :=
  D (p4Q2GX_rightZeroCoefficient 2) *
      D' p4Q2OO_depthTwoFirstCoefficient -
    D p4Q2OO_depthTwoFirstCoefficient *
      D' (p4Q2GX_rightZeroCoefficient 2)

/-- The exact Schur elimination of the third actual Krylov coefficient
against the first TWO original Wilson modal GI rows.
This definition depends only on their literal values at the three
genuine source selectors; no arbitrary third receiver is introduced. -/
noncomputable def p4Q2OO_depthTwoSchurResidual
    (D D' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ) :
    Fin (2 + 1) → ℝ :=
  p4Q2OO_depthTwoLeadingMinor D D' •
      p4Q2OO_depthTwoSecondCoefficient -
    (D p4Q2OO_depthTwoSecondCoefficient *
        D' p4Q2OO_depthTwoFirstCoefficient -
      D p4Q2OO_depthTwoFirstCoefficient *
        D' p4Q2OO_depthTwoSecondCoefficient) •
          p4Q2GX_rightZeroCoefficient 2 -
    (D (p4Q2GX_rightZeroCoefficient 2) *
        D' p4Q2OO_depthTwoSecondCoefficient -
      D p4Q2OO_depthTwoSecondCoefficient *
        D' (p4Q2GX_rightZeroCoefficient 2)) •
          p4Q2OO_depthTwoFirstCoefficient

/-- First original two-posterior GI receiver cancels exactly. -/
theorem p4Q2OO_depthTwoSchurResidual_firstRow_null
    (D D' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ) :
    D (p4Q2OO_depthTwoSchurResidual D D') = 0 := by
  simp only [p4Q2OO_depthTwoSchurResidual,
    p4Q2OO_depthTwoLeadingMinor, map_sub, map_smul, smul_eq_mul]
  ring

/-- Second original two-posterior GI receiver cancels exactly. -/
theorem p4Q2OO_depthTwoSchurResidual_secondRow_null
    (D D' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ) :
    D' (p4Q2OO_depthTwoSchurResidual D D') = 0 := by
  simp only [p4Q2OO_depthTwoSchurResidual,
    p4Q2OO_depthTwoLeadingMinor, map_sub, map_smul, smul_eq_mul]
  ring

/-- The second coefficient of the Schur residual is precisely the
proved first-two GI determinant. -/
theorem p4Q2OO_depthTwoSchurResidual_secondCoefficient
    (D D' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ) :
    p4Q2OO_depthTwoSchurResidual D D' 2 =
      p4Q2OO_depthTwoLeadingMinor D D' := by
  simp [p4Q2OO_depthTwoSchurResidual,
    p4Q2OO_depthTwoFirstCoefficient,
    p4Q2OO_depthTwoSecondCoefficient,
    p4Q2GX_rightZeroCoefficient, Pi.sub_apply, Pi.smul_apply]

/-- First-two original GI separation proves a NONZERO three-mode
coefficient residual; it does NOT prove the physical synthesized
residual is nonzero. -/
theorem p4Q2OO_depthTwoSchurResidual_ne_zero_of_leadingMinor
    (D D' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ)
    (hMinor : p4Q2OO_depthTwoLeadingMinor D D' ≠ 0) :
    p4Q2OO_depthTwoSchurResidual D D' ≠ 0 := by
  intro hZero
  have hTwo := congrArg
    (fun a : Fin (2 + 1) → ℝ => a 2) hZero
  have hMinorZero : p4Q2OO_depthTwoLeadingMinor D D' = 0 := by
    simpa only [p4Q2OO_depthTwoSchurResidual_secondCoefficient,
      Pi.zero_apply] using hTwo
  exact hMinor hMinorZero

/-- An ACTUAL third Wilson GI receiver evaluates the residual by a
literal three-column Schur expansion. Whether this is nonzero for
some actual third context is a genuinely new, unproved physical
input, not a postulated rank axiom. -/
theorem p4Q2OO_depthTwoSchurResidual_thirdRow_formula
    (D D' D'' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ) :
    D'' (p4Q2OO_depthTwoSchurResidual D D') =
      p4Q2OO_depthTwoLeadingMinor D D' *
        D'' p4Q2OO_depthTwoSecondCoefficient -
      (D p4Q2OO_depthTwoSecondCoefficient *
          D' p4Q2OO_depthTwoFirstCoefficient -
        D p4Q2OO_depthTwoFirstCoefficient *
          D' p4Q2OO_depthTwoSecondCoefficient) *
        D'' (p4Q2GX_rightZeroCoefficient 2) -
      (D (p4Q2GX_rightZeroCoefficient 2) *
          D' p4Q2OO_depthTwoSecondCoefficient -
        D p4Q2OO_depthTwoSecondCoefficient *
          D' (p4Q2GX_rightZeroCoefficient 2)) *
        D'' p4Q2OO_depthTwoFirstCoefficient := by
  simp only [p4Q2OO_depthTwoSchurResidual,
    map_sub, map_smul, smul_eq_mul]

section ActualOriginalWilsonDepthTwo

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Zero" => p4Q2GX_rightZeroCoefficient
local notation "First" => p4Q2OO_depthTwoFirstCoefficient
local notation "Second" => p4Q2OO_depthTwoSecondCoefficient
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "Right" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- No substitute operator: the zero, first and second coefficient
selectors synthesize EXACTLY U, T_fine U, T_fine^2 U in the actual
Gauss-law physical Hilbert carrier. -/
theorem p4Q2OO_actualDepthTwo_selectorPhysicalSources :
    S 2 (Zero 2) = U ∧
      S 2 First = Fine U ∧
      S 2 Second = (Fine ^ 2) U := by
  refine ⟨
    p4Q2GX_actualRightCoefficientSource_eq_physicalUnit
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2,
    ?_, ?_⟩
  · have h : S 2 First = Right 1 := by
      change (∑ j : Fin (2 + 1), First j • Right (j : ℕ)) = Right 1
      calc
        (∑ j : Fin (2 + 1), First j • Right (j : ℕ)) =
            First (1 : Fin (2 + 1)) • Right 1 := by
              apply Finset.sum_eq_single (1 : Fin (2 + 1))
              · intro j _hj hj
                simp [p4Q2OO_depthTwoFirstCoefficient, hj]
              · intro hnot
                exact False.elim (hnot (Finset.mem_univ _))
        _ = Right 1 := by simp [p4Q2OO_depthTwoFirstCoefficient]
    calc
      S 2 First = Right 1 := h
      _ = Fine U :=
        p4Q2IU_actualFirstRightSource_eq_normalizedFineWilsonUnit
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  · have h : S 2 Second = Right 2 := by
      change (∑ j : Fin (2 + 1), Second j • Right (j : ℕ)) = Right 2
      calc
        (∑ j : Fin (2 + 1), Second j • Right (j : ℕ)) =
            Second (2 : Fin (2 + 1)) • Right 2 := by
              apply Finset.sum_eq_single (2 : Fin (2 + 1))
              · intro j _hj hj
                simp [p4Q2OO_depthTwoSecondCoefficient, hj]
              · intro hnot
                exact False.elim (hnot (Finset.mem_univ _))
        _ = Right 2 := by simp [p4Q2OO_depthTwoSecondCoefficient]
    calc
      S 2 Second = Right 2 := h
      _ = (Fine ^ 2) U := rfl

/-- Every selector's genuine HF modal GI value is the ORIGINAL
two-interacting-Wilson-posterior signed response on its actual
physical source; this includes the previously untreated T_fine^2 U. -/
theorem p4Q2OO_actualDepthTwo_selectorModal_eq_originalPhysicalGI
    (e : Link) (z : Pair) :
    M 2 e z (Zero 2) =
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) U e z ∧
    M 2 e z First =
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (Fine U) e z ∧
    M 2 e z Second =
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) ((Fine ^ 2) U) e z := by
  have hSelector (a : Fin (2 + 1) → ℝ) (f : Phys)
      (ha : S 2 a = f) :
      M 2 e z a =
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) f e z := by
    have hHF :=
      p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2 a e z
    change p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) (S 2 a) e z = M 2 e z a at hHF
    rw [ha] at hHF
    exact hHF.symm
  obtain ⟨h0, h1, h2⟩ :=
    p4Q2OO_actualDepthTwo_selectorPhysicalSources
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  exact ⟨hSelector (Zero 2) U h0,
    hSelector First (Fine U) h1,
    hSelector Second ((Fine ^ 2) U) h2⟩

/-- The first TWO columns of true depth-two Wilson GI modes
are LITERALLY the same physical minor proved nonzero by OM at
depth one, even though the independent third column is OPEN. -/
theorem p4Q2OO_actualDepthTwo_leadingMinor_eq_originalDepthOneMinor
    (e e' : Link) (z z' : Pair) :
    p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') =
      p4Q2OJ_originalCrossContextModalMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 1 e e' z z' p4Q2IS_depthOneCoefficient := by
  obtain ⟨h0, h1, _h2⟩ :=
    p4Q2OO_actualDepthTwo_selectorModal_eq_originalPhysicalGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z
  obtain ⟨h0', h1', _h2'⟩ :=
    p4Q2OO_actualDepthTwo_selectorModal_eq_originalPhysicalGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z'
  unfold p4Q2OO_depthTwoLeadingMinor p4Q2OJ_originalCrossContextModalMinor
  rw [h0, h1, h0', h1',
    p4Q2OM_actualDepthOne_zeroModal_eq_originalPhysicalUnitGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z,
    p4Q2OM_actualDepthOne_firstModal_eq_originalFinePhysicalGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z,
    p4Q2OM_actualDepthOne_zeroModal_eq_originalPhysicalUnitGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z',
    p4Q2OM_actualDepthOne_firstModal_eq_originalFinePhysicalGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z']

/-- UNCONDITIONAL finite-volume original Wilson result inherited
from OM, now transported to the actual depth-two coefficient frame.
Two authentic contexts can be chosen before the fine coupling value. -/
theorem p4Q2OO_actualDepthTwo_exists_nonzeroLeadingMinor_smallFine
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Pair, ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0) := by
  obtain ⟨z, z', delta, hdelta, hMinor⟩ :=
    p4Q2OM_actualDepthOne_exists_fixedContexts_smallPositiveFine_minor_ne
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨z, z', delta, hdelta, ?_⟩
  intro ht hSmall
  rw [p4Q2OO_actualDepthTwo_leadingMinor_eq_originalDepthOneMinor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e e' z z']
  exact hMinor ht hSmall

/-- In the genuine positive-fine two-context witness, there is a
NONZERO signed three-mode coefficient annihilated by BOTH selected
original Wilson GI rows. The physical image may still be zero. -/
theorem p4Q2OO_actualDepthTwo_SchurResidual_twoGI_null_coefficient_ne
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor
      (M 2 e z) (M 2 e' z') ≠ 0) :
    M 2 e z
        (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0 ∧
    M 2 e' z'
        (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0 ∧
    p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z') ≠ 0 := by
  exact ⟨p4Q2OO_depthTwoSchurResidual_firstRow_null _ _,
    p4Q2OO_depthTwoSchurResidual_secondRow_null _ _,
    p4Q2OO_depthTwoSchurResidual_ne_zero_of_leadingMinor _ _ hMinor⟩

/-- Exact physical meaning of the SCHUR residual:
a true depth-two right-Krylov physical source, not an independent
synthetic detector or surrogate physical model. -/
theorem p4Q2OO_actualDepthTwo_SchurResidual_physicalSource
    (e e' : Link) (z z' : Pair) :
    S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) =
      p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') •
        ((Fine ^ 2) U) -
      ((M 2 e z) Second * (M 2 e' z') First -
        (M 2 e z) First * (M 2 e' z') Second) • U -
      ((M 2 e z) (Zero 2) * (M 2 e' z') Second -
        (M 2 e z) Second * (M 2 e' z') (Zero 2)) • (Fine U) := by
  obtain ⟨h0, h1, h2⟩ :=
    p4Q2OO_actualDepthTwo_selectorPhysicalSources
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  simp only [p4Q2OO_depthTwoSchurResidual, map_sub, map_smul]
  rw [h0, h1, h2]

/-- The response of ANY actual third original two-posterior GI row
to the SAME depth-two Schur residual is EXACTLY the original physical
signed response of its genuine Gauss-law Hilbert source.
A nonzero value remains to be proved, not assumed here. -/
theorem p4Q2OO_actualDepthTwo_SchurResidual_trueThirdGI_response
    (e e' e'' : Link) (z z' z'' : Pair) :
    M 2 e'' z'' (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (S 2 (p4Q2OO_depthTwoSchurResidual
          (M 2 e z) (M 2 e' z'))) e'' z'' := by
  have hHF :=
    p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z'))
      e'' z''
  change p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    Hn (beta n) (hbeta n)
    (S 2 (p4Q2OO_depthTwoSchurResidual
      (M 2 e z) (M 2 e' z'))) e'' z'' =
    M 2 e'' z'' (p4Q2OO_depthTwoSchurResidual
      (M 2 e z) (M 2 e' z')) at hHF
  exact hHF.symm

end ActualOriginalWilsonDepthTwo
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_depthTwo_coeff_decompose
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_depthTwoSchurResidual_firstRow_null
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_depthTwoSchurResidual_secondRow_null
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_depthTwoSchurResidual_secondCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_depthTwoSchurResidual_ne_zero_of_leadingMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_depthTwoSchurResidual_thirdRow_formula
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_actualDepthTwo_selectorPhysicalSources
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_actualDepthTwo_selectorModal_eq_originalPhysicalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_actualDepthTwo_leadingMinor_eq_originalDepthOneMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_actualDepthTwo_exists_nonzeroLeadingMinor_smallFine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_actualDepthTwo_SchurResidual_twoGI_null_coefficient_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_actualDepthTwo_SchurResidual_physicalSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OO_actualDepthTwo_SchurResidual_trueThirdGI_response

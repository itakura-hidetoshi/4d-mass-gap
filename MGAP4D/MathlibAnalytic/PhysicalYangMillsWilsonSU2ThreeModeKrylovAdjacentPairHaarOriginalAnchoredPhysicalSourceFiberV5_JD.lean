import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAnchoredHaarMomentRatioV5_JC
import Mathlib.Tactic

/-!
# P4-Q2-JD: the original anchored Haar residual is the Wilson response to a REAL physical source

JC reduces original two-interacting-Wilson-posterior GI separation to
nonzero residual of the genuine frozen transfer/Haar fiber moments.
JD identifies its integrand with ONE real signed physical Haar-L² source:
the actual fine Wilson first Krylov vector minus the anchored physical
constant unit with the verified original GI zero-mode moment ratio.

The source is nonzero throughout a sufficiently small positive fine-Wilson
coupling window, by the true spatial plaquette witness of IZ.
Its original GI response is exactly the nonzero frozen Wilson factor
times the anchored Haar-moment residual. This bridges the finite
moment algebra back to the true physical Hilbert carrier; it does not
assume original GI visibility of that nonzero source.

No surrogate independent-Haar posterior, new frame, new axioms or
continuum mass-gap claim is introduced. The nonzero second-context
response remains the next essential physical obstruction.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The true two-mode anchored signed coefficient has original zero-mode
weight -t and first-mode weight one; this lemma does not encode an
independent physical source or a second posterior. -/
private theorem p4Q2JD_abstract_anchored_twoModeMoment
    (t : ℝ) (w : Fin (1 + 1) → ℝ) :
    (∑ j : Fin (1 + 1),
      (p4Q2IS_depthOneCoefficient -
        t • p4Q2GX_rightZeroCoefficient 1) j * w j) =
      w 1 - t * w 0 := by
  simp [Fin.sum_univ_two, p4Q2IS_depthOneCoefficient,
    p4Q2GX_rightZeroCoefficient, Pi.sub_apply, Pi.smul_apply]
  ring

section ActualRightDepthOne

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
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "J" =>
  p4Q2JB_originalWilsonTrueFiberMoment
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "P" =>
  p4Q2JB_originalWilsonFrozenPrefactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "FineTransfer" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "Unit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2

/-- The actual signed coefficient selected by one genuine original
two-posterior GI anchor: the ratio is taken from its LITERAL
frozen-Wilson Haar transfer moments, not an arbitrary modal frame. -/
noncomputable def p4Q2JD_originalWilsonAnchoredCoefficient
    (e : Link) (z : Pair) : Fin (1 + 1) → ℝ :=
  p4Q2IS_depthOneCoefficient -
    (J e z 1 / J e z 0) • p4Q2GX_rightZeroCoefficient 1

/-- The ACTUAL Haar-L² physical synthesis of this anchored coefficient. -/
noncomputable def p4Q2JD_originalWilsonAnchoredPhysicalSource
    (e : Link) (z : Pair) : Phys :=
  PhysicalSource
    (p4Q2JD_originalWilsonAnchoredCoefficient
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z)

/-- The actual signed physical vector is literally the genuine first
fine Wilson Krylov source minus the original-Haar-moment normalized
constant physical unit. It is not merely nonzero as coefficients. -/
theorem p4Q2JD_originalWilsonAnchoredPhysicalSource_eq_trueFinePivot
    (e : Link) (z : Pair) :
    p4Q2JD_originalWilsonAnchoredPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z =
      RightFactor n 1 - (J e z 1 / J e z 0) • RightFactor n 0 := by
  have h1 :
      PhysicalSource p4Q2IS_depthOneCoefficient = RightFactor n 1 :=
    p4Q2IU_firstSelector_synthesizes_actualFineRightSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  have h0 :
      PhysicalSource (p4Q2GX_rightZeroCoefficient 1) = RightFactor n 0 :=
    p4Q2GX_actualRightCoefficientSource_eq_zeroMode
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
  unfold p4Q2JD_originalWilsonAnchoredPhysicalSource
    p4Q2JD_originalWilsonAnchoredCoefficient
  rw [map_sub, map_smul, h1, h0]

/-- THE physically essential integral identity:
JC's second-context residual is the original frozen Wilson
transfer/Haar fiber pairing of the one true signed PHYSICAL source
against the difference of the two interacting posterior densities.
It is not a four-scalar surrogate or a replacement conditional law. -/
theorem p4Q2JD_originalFrozenFiberIntegral_of_signedPhysicalSource_eq_secondResidual
    (e : Link) (z : Pair) (e' : Link) (z' : Pair) :
    p4Q2GN_originalTransferFiberContrastMoment
      Hn (beta n) (hbeta n)
        (p4Q2JD_originalWilsonAnchoredPhysicalSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z)
        e' z' =
    p4Q2JC_originalWilsonAnchoredSecondMomentResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z e' z' := by
  let t : ℝ := J e z 1 / J e z 0
  let a : Fin (1 + 1) → ℝ :=
    p4Q2JD_originalWilsonAnchoredCoefficient
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z
  let w : Fin (1 + 1) → ℝ := fun j =>
    p4Q2GN_originalTransferFiberContrastMoment
      Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e' z'
  have hSum :=
    p4Q2HF_actualRightOriginalTransferFiberMoment_finite_sum
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 a e' z'
  have ha :
      a = p4Q2IS_depthOneCoefficient -
        t • p4Q2GX_rightZeroCoefficient 1 := rfl
  have hSample :
      (∑ j : Fin (1 + 1), a j * w j) = w 1 - t * w 0 := by
    rw [ha]
    exact p4Q2JD_abstract_anchored_twoModeMoment t w
  change p4Q2GN_originalTransferFiberContrastMoment Hn (beta n) (hbeta n)
      (∑ j : Fin (1 + 1), a j • RightFactor n (j : ℕ)) e' z' =
    w 1 - t * w 0
  rw [hSum]
  exact hSample

/-- The genuine original two-interacting-Wilson-posterior GI expectation
difference of ONE signed physical source equals the nonzero frozen
prefactor multiplied by JC's anchored second-context Haar residual. -/
theorem p4Q2JD_originalGIResponse_of_signedPhysicalSource_eq_prefactor_mul_residual
    (e : Link) (z : Pair) (e' : Link) (z' : Pair) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
        (p4Q2JD_originalWilsonAnchoredPhysicalSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z)
        e' z' =
      P z' *
        p4Q2JC_originalWilsonAnchoredSecondMomentResidual
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n e z e' z' := by
  have hGN :=
    p4Q2GN_originalExpectationGap_eq_transferFiberMoment
      Hn (beta n) (hbeta n)
      (p4Q2JD_originalWilsonAnchoredPhysicalSource
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z)
      e' z'
  rw [hGN, p4Q2JD_originalFrozenFiberIntegral_of_signedPhysicalSource_eq_secondResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z e' z']
  rfl

/-- At a genuine nonzero original Wilson anchor, a nonzero original
interacting GI response of the physical signed source at the second
context is equivalent to the exact physical Haar-moment residual
being nonzero. Both posterior laws remain the original ones. -/
theorem p4Q2JD_originalGIResponse_of_signedPhysicalSource_ne_iff_residual_ne
    (e : Link) (z : Pair) (e' : Link) (z' : Pair) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
        (p4Q2JD_originalWilsonAnchoredPhysicalSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z)
        e' z' ≠ 0 ↔
      p4Q2JC_originalWilsonAnchoredSecondMomentResidual
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z e' z' ≠ 0 := by
  rw [p4Q2JD_originalGIResponse_of_signedPhysicalSource_eq_prefactor_mul_residual
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e z e' z']
  have hp : P z' ≠ 0 :=
    p4Q2JB_originalWilsonFrozenPrefactor_ne_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n z'
  constructor
  · intro h hZero
    exact h (by rw [hZero, mul_zero])
  · intro hResidual
    exact mul_ne_zero hp hResidual

/-- Although the physical GI detector may still miss it, the actual
anchored signed source is provably NONZERO throughout some strictly
positive fine beta interval. This uses IZ's genuine SU(2) spatial
Wilson plaquette witness, not a coefficient-space rank assumption. -/
theorem p4Q2JD_smallPositiveFine_anchoredSignedPhysicalSource_ne_zero
    (e : Link) (z : Pair) :
    ∃ ε : ℝ, 0 < ε ∧
      (0 < beta (n + 1) → beta (n + 1) < ε →
        p4Q2JD_originalWilsonAnchoredPhysicalSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n e z ≠ 0) := by
  obtain ⟨ε, hε, hNE⟩ :=
    p4Q2IZ_actualFineUnit_notEigenline_for_small_positive_beta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  refine ⟨ε, hε, ?_⟩
  intro hPos hSmall hZero
  have hEq := p4Q2JD_originalWilsonAnchoredPhysicalSource_eq_trueFinePivot
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e z
  rw [hEq] at hZero
  have hParallel :
      RightFactor n 1 = (J e z 1 / J e z 0) • RightFactor n 0 :=
    sub_eq_zero.mp hZero
  have hFirst :
      RightFactor n 1 = FineTransfer Unit :=
    p4Q2IU_actualFirstRightSource_eq_normalizedFineWilsonUnit
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  have hUnit : RightFactor n 0 = Unit :=
    fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  rw [hFirst, hUnit] at hParallel
  exact (hNE hPos hSmall) ⟨J e z 1 / J e z 0, hParallel⟩

end ActualRightDepthOne
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JD_originalWilsonAnchoredPhysicalSource_eq_trueFinePivot
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JD_originalFrozenFiberIntegral_of_signedPhysicalSource_eq_secondResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JD_originalGIResponse_of_signedPhysicalSource_eq_prefactor_mul_residual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JD_originalGIResponse_of_signedPhysicalSource_ne_iff_residual_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JD_smallPositiveFine_anchoredSignedPhysicalSource_ne_zero

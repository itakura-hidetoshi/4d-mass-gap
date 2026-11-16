import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPrimaryPlaquetteFundamentalCharacterCoefficientV5_PZ37AMD
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteTranslationAdjacency
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsSectorFactorization
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHaarGibbsL2Isometry
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AME — genuine SU(2) Wilson Gibbs pair with one shared physical link

AMD concerns ONE physical primary plaquette under product-Haar reference measure.
Here we construct a SECOND, DISTINCT plaquette sharing an actual oriented physical
link with that primary plaquette. The two observables are evaluated against the
SAME actual interacting finite-volume SU(2) Wilson Gibbs probability law.

The exact density integration identity preserves the FULL Wilson exponent,
including the other plaquettes sharing links. It does not erase interactions,
postulate a product Gibbs law, or deduce clustering from the single-plaquette
ABN/AMD coefficient. In particular no volume-uniform decay or mass gap follows.

Only append-only definitions and equality proofs; original Wilson model, fixed
beta0, Haar, Gauss/AJA and Lean/mathlib pins are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "GK" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "chiK" => p4Q2PZ35C_originalOneLinkCharacter

local instance ameSideLengthNonzero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance ameSU2Topological : IsTopologicalGroup GK :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance ameSU2Compact : CompactSpace GK :=
  specialUnitaryGroupCompactSpace 2
local instance ameSU2SecondCountable : SecondCountableTopology GK :=
  specialUnitaryGroupSecondCountableTopology 2
local instance ameSU2Measurable : MeasurableSpace GK :=
  specialUnitaryGroupMeasurableSpace 2
local instance ameSU2Borel : BorelSpace GK :=
  specialUnitaryGroupBorelSpace 2
local instance ameSU2Nontrivial : Nontrivial GK := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : GK => (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace GroundStatePosteriorJoint

/-- An actual second primary-plane plaquette at a positive unit spatial
translation. The original four-link plaquette is left unchanged. -/
noncomputable def p4Q2PZ37AME_originalPrimarySharedLinkNeighbor
    (H : ℕ) : PeriodicHypercubicEvenPlaquette H :=
  let p := periodicHypercubicEvenPrimarySpatialPlaquette H
  (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) p.1
    (periodicHypercubicPlaquetteFirstAxis p), p.2)

/-- This is geometric shared-PHYSICAL-link adjacency (and distinctness),
not independence or a statement about covariance. -/
theorem p4Q2PZ37AME_originalPrimarySharedLinkNeighbor_adjacent
    (H : ℕ) :
    periodicHypercubicPlaquetteAdjacent
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenPrimarySpatialPlaquette H)
      (p4Q2PZ37AME_originalPrimarySharedLinkNeighbor H) := by
  have hn : 2 ≤ PeriodicHypercubicEvenSideLength H := by
    change 2 ≤ 2 * (H + 1)
    omega
  simpa only [p4Q2PZ37AME_originalPrimarySharedLinkNeighbor] using
    (periodicHypercubicPlaquetteAdjacent_shift_first
      (PeriodicHypercubicEvenSideLength H) hn
      (periodicHypercubicEvenPrimarySpatialPlaquette H))

/-- Explicit existence of a physical SU(2) lattice edge touched by both
distinct plaquettes; this witness is inherited from proven incidence geometry. -/
theorem p4Q2PZ37AME_originalPrimarySharedLinkNeighbor_physicalEdge
    (H : ℕ) :
    ∃ e : PeriodicHypercubicEvenEdge H,
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenPrimarySpatialPlaquette H) e ∧
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H)
        (p4Q2PZ37AME_originalPrimarySharedLinkNeighbor H) e :=
  (p4Q2PZ37AME_originalPrimarySharedLinkNeighbor_adjacent H).2

/-- Real connected character covariance of two ACTUAL SU(2) plaquettes
sharing a physical link, under the FULL interacting finite-volume Wilson Gibbs
law, not under free product-Haar measure. This definition claims no decay. -/
noncomputable def p4Q2PZ37AME_originalPrimaryNeighborGibbsConnected
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta
  let p := periodicHypercubicEvenPrimarySpatialPlaquette H
  let q := p4Q2PZ37AME_originalPrimarySharedLinkNeighbor H
  exact
    (∫ A : PeriodicHypercubicEvenEdge H → GK,
      chiK (periodicHypercubicPlaquetteHolonomy A p) *
        chiK (periodicHypercubicPlaquetteHolonomy A q) ∂C.gibbsMeasure) -
    (∫ A : PeriodicHypercubicEvenEdge H → GK,
      chiK (periodicHypercubicPlaquetteHolonomy A p) ∂C.gibbsMeasure) *
    (∫ A : PeriodicHypercubicEvenEdge H → GK,
      chiK (periodicHypercubicPlaquetteHolonomy A q) ∂C.gibbsMeasure)

/-- Exact real moment conversion for the ORIGINAL compact oriented Wilson
Gibbs tilt. The denominator is the genuine full-volume partition function;
there is no replacement by a one-plaquette normalization. -/
theorem p4Q2PZ37AME_actualWilsonGibbsIntegral_eq_fullHaarDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ) :
    (∫ A, f A ∂C.gibbsMeasure) =
      (∫ A,
        (Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) * f A
        ∂C.base.configurationHaarMeasure) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  unfold CompactOrientedGaugeWilsonSystem.gibbsMeasure
  rw [integral_tilted]
  simp only [smul_eq_mul, CompactOrientedGaugeWilsonSystem.partitionFunction]

/-- The exact two-observable connected correlation identity is under the
full interacting Wilson law, and retains the common Gibbs weight in ALL
three moments. It does NOT factor their joint distribution. -/
theorem p4Q2PZ37AME_actualWilsonGibbsConnected_eq_fullHaarDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : C.base.Configuration → ℝ) :
    (∫ A, f A * g A ∂C.gibbsMeasure) -
      (∫ A, f A ∂C.gibbsMeasure) *
      (∫ A, g A ∂C.gibbsMeasure) =
    (∫ A,
      (Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) *
        (f A * g A) ∂C.base.configurationHaarMeasure) -
      (∫ A,
        (Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) * f A
          ∂C.base.configurationHaarMeasure) *
      (∫ A,
        (Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) * g A
          ∂C.base.configurationHaarMeasure) := by
  rw [p4Q2PZ37AME_actualWilsonGibbsIntegral_eq_fullHaarDensity
        C (fun A => f A * g A),
      p4Q2PZ37AME_actualWilsonGibbsIntegral_eq_fullHaarDensity C f,
      p4Q2PZ37AME_actualWilsonGibbsIntegral_eq_fullHaarDensity C g]

/-- Every actual Wilson finite-volume partition function in this same-root
SU(2) family is strictly positive. No uniform H-independent lower bound
is inferred from this finite-H positivity. -/
theorem p4Q2PZ37AME_originalFiniteWilsonPartition_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 <
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2
        (by norm_num) beta hbeta).base.partitionFunction := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta
  exact compact_oriented_partitionFunction_pos C.base
    (continuous_compact_oriented_boltzmannIntegrable C)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AME_originalPrimarySharedLinkNeighbor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AME_originalPrimarySharedLinkNeighbor_adjacent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AME_originalPrimarySharedLinkNeighbor_physicalEdge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AME_originalPrimaryNeighborGibbsConnected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AME_actualWilsonGibbsIntegral_eq_fullHaarDensity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AME_actualWilsonGibbsConnected_eq_fullHaarDensity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AME_originalFiniteWilsonPartition_pos

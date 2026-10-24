import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOffDiagonalPeriodTwoV5_PY9B
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOffDiagonalNonminimalHaarV5_PY9C
import Mathlib.Tactic

/-!
# P4-Q2-PY9D — original fifth Wilson Ward coefficient vanishes at ALL even periods

PY9B provides a genuine center-odd spatial link outside any two
true temporal crossing links for EVERY distinct spatial plaquette
pair, including the exceptional period-two torus. The odd link may
belong to p alone OR to q alone. Using PY8D in the corresponding
orientation, with the exact commuting real Haar integrand when
necessary, all original off-diagonal two-crossing terms vanish.

PY9C expands the COMPLETE crossing action square, so J_pq(B)=0
for every genuine distinct original pair. PY8C proves diagonal
boundary invariance, hence PY7's exact finite pair expansion makes
the true centered squared-Wilson two-crossing Haar profile constant
at EVERY finite even lattice period H.

Thus the true PX4 fourth-jet fifth coefficient is EXACTLY ZERO for
all original spatial SU(2) triples. PX4's literal interacting Wilson
minor with both Haar integrations and ALL intermediate spatial Wilson
contributions is consequently O(beta^6), under its original physical
small-action budget.

No new axioms, sorry/admit, independent/posterior factorization,
Dobrushin model, fictitious spectral measure or nonzero minor claim.
In particular this is not a claim of Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY9D_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY9D_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY9D_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY9D_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY9D_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PY9D_plaquetteFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalUniversalFifthWardZero
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "s" => p4Q2PY9_originalPlaquettePhysicalEdges H
local notation "J" => p4Q2PY7_originalPlaquettePairTwoCrossingHaar H
local notation "G" => p4Q2PY7_originalCenteredSquareTwoCrossingHaar H
local notation "C5" => p4Q2PX_originalFifthFourthJetCoefficient H
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H

/-- Every original off-diagonal plaquette-character pair against two
true temporal Wilson energies integrates to zero under spatial Haar.
The period-two symmetric-difference case is included, and neither
of the two original crossing links is removed. -/
theorem p4Q2PY9_originalOffDiagonal_twoCrossingHaar_zero_allPeriods
    (p q : Plaq) (hpq : p ≠ q) (e f : Link) (B : Cfg) :
    (∫ A : Cfg, (χ p A * χ q A) *
      (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) = 0 := by
  obtain ⟨target, hside, he, hf⟩ :=
    p4Q2PY9_originalDistinctPlaquettes_oddFreeLink_for_twoCrossings
      H p q hpq e f
  have hWard (u v : Plaq) (hu : target ∈ s u)
      (hv : target ∉ s v) :
      (∫ A : Cfg, (χ u A * χ v A) *
        (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) = 0 := by
    apply p4Q2PY8_originalPlaquettePair_twoCrossingHaar_zero_of_freeEdge
      H u v e f target
    · exact (p4Q2PY9_originalPlaquettePhysicalEdges_mem H u target).mp hu
    · intro h
      exact hv ((p4Q2PY9_originalPlaquettePhysicalEdges_mem H v target).mpr h)
    · exact he
    · exact hf
  rcases hside with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · exact hWard p q hp hq
  · calc
      (∫ A : Cfg, (χ p A * χ q A) *
        (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) =
        (∫ A : Cfg, (χ q A * χ p A) *
          (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) := by
            apply integral_congr_ae
            filter_upwards with A
            ring
      _ = 0 := hWard q p hq hp

/-- Entire original double-crossing-square Haar matrix is zero
off-diagonal, in ALL finite even spatial volumes including H=0. -/
theorem p4Q2PY9_originalOffDiagonalPlaquettePairHaar_zero_allPeriods
    (p q : Plaq) (hpq : p ≠ q) (B : Cfg) :
    J p q B = 0 := by
  rw [p4Q2PY9_originalPlaquettePair_fullCrossingSquare_expand H p q B]
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  exact p4Q2PY9_originalOffDiagonal_twoCrossingHaar_zero_allPeriods
    H p q hpq e f B

/-- Each TRUE spatial-plaquette pair Haar moment is right-boundary
invariant for arbitrary even period: diagonal by original gauge
invariance, and off-diagonal by exact center-odd Haar vanishing. -/
theorem p4Q2PY9_originalPlaquettePairHaar_invariant_allPeriods
    (p q : Plaq) (B : Cfg) :
    J p q B = J p q (fun _ => 1) := by
  by_cases hpq : p = q
  · subst q
    exact p4Q2PY8_originalDiagonalPlaquettePairHaar_invariant H p B
  · calc
      J p q B = 0 :=
        p4Q2PY9_originalOffDiagonalPlaquettePairHaar_zero_allPeriods
          H p q hpq B
      _ = J p q (fun _ => 1) :=
        (p4Q2PY9_originalOffDiagonalPlaquettePairHaar_zero_allPeriods
          H p q hpq (fun _ => 1)).symm

/-- Exact centered genuine spatial Wilson-square Haar two-crossing
profile is a constant function of the original SU(2) boundary,
for ALL finite even H, including the minimal period-two torus. -/
theorem p4Q2PY9_originalCenteredSquare_constant_allPeriods
    (B : Cfg) :
    G B = G (fun _ => 1) := by
  classical
  calc
    G B = (1 / 4 : ℝ) * (∑ p : Plaq, ∑ q : Plaq, J p q B) :=
      p4Q2PY7_originalCenteredSquare_eq_plaquettePairSum H B
    _ = (1 / 4 : ℝ) *
        (∑ p : Plaq, ∑ q : Plaq, J p q (fun _ => 1)) := by
      apply congrArg (fun x : ℝ => (1 / 4 : ℝ) * x)
      apply Finset.sum_congr rfl
      intro p _hp
      apply Finset.sum_congr rfl
      intro q _hq
      exact p4Q2PY9_originalPlaquettePairHaar_invariant_allPeriods
        H p q B
    _ = G (fun _ => 1) :=
      (p4Q2PY7_originalCenteredSquare_eq_plaquettePairSum
        H (fun _ => 1)).symm

/-- Genuine ORIGINAL full fourth-moment fifth Wilson minor
coefficient vanishes without any additional finite-volume,
boundary, posterior, rank, or witness assumption. -/
theorem p4Q2PY9_originalFifthFourthJetCoefficient_zero_allPeriods
    (A B C : Cfg) :
    C5 A B C = 0 := by
  rw [p4Q2PY7_originalFifthCoefficient_eq_centeredSquareMinor H A B C,
    p4Q2PY9_originalCenteredSquare_constant_allPeriods H A,
    p4Q2PY9_originalCenteredSquare_constant_allPeriods H B,
    p4Q2PY9_originalCenteredSquare_constant_allPeriods H C]
  ring

/-- Genuine original fully interacting three-boundary Wilson minor
is O(beta^6), with its EXACT PX4 action-budget small-coupling range.
No positivity, three-mode independence or mass-gap conclusion. -/
theorem p4Q2PY9_originalLiteralThreeSpatialMinor_sixthOrder_allPeriods
    (A B C : Cfg) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
          ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C‖ ≤
            K * ‖beta‖ ^ 6 := by
  obtain ⟨K, hK, hRem⟩ :=
    p4Q2PX4_originalLiteralWilsonMinor_fifthCoefficient H A B C
  refine ⟨K, hK, ?_⟩
  intro beta hBeta hSmall
  have h := hRem beta hBeta hSmall
  rw [p4Q2PY9_originalFifthFourthJetCoefficient_zero_allPeriods H A B C] at h
  simpa using h

end OriginalUniversalFifthWardZero
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalOffDiagonal_twoCrossingHaar_zero_allPeriods
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalOffDiagonalPlaquettePairHaar_zero_allPeriods
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalPlaquettePairHaar_invariant_allPeriods
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalCenteredSquare_constant_allPeriods
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalFifthFourthJetCoefficient_zero_allPeriods
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalLiteralThreeSpatialMinor_sixthOrder_allPeriods

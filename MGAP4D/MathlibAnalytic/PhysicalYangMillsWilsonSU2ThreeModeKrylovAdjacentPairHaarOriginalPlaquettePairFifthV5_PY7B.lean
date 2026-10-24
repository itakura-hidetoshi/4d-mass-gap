import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCenteredPlaquetteSquareFifthV5_PY7
import Mathlib.Tactic

/-!
# P4-Q2-PY7B — exact double-plaquette Haar presentation of the fifth Ward obstruction

PY7 reduces the true original finite-volume SU(2) Wilson fifth
coefficient to the genuine centered spatial-Wilson-square Haar
moment G(B). The centered Wilson moment is exactly one half of
the finite spatial plaquette character sum, so G is precisely
one quarter of the finite DOUBLE sum of genuine original
plaquette-character PAIRS integrated with the COMPLETE squared
temporal crossing action.

This is exact with all diagonal p=q, off-diagonal p≠q, and
all crossing e=f and e≠f terms retained; no cancellations
between distinct plaquettes are assumed. Symmetry of the
original pair moments is proved by real commutativity.

The next analytic question is which of these genuine pair
moments have a right-boundary-dependent component, not an
invented rank or nonzero physical third Hankel coefficient.
No sorry/admit/new axioms, posterior replacement, Dobrushin
or spectral surrogate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY7B_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY7B_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY7B_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY7B_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY7B_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PY7B_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section TrueOriginalPlaquettePairFifth
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "G" => p4Q2PY7_originalCenteredSquareTwoCrossingHaar H

/-- A single genuinely coupled pair of original spatial Wilson
plaquette real characters paired against the full temporal
two-crossing square under the true spatial SU(2) reference Haar. -/
noncomputable def p4Q2PY7_originalPlaquettePairTwoCrossingHaar
    (p q : Plaq) (B : Cfg) : ℝ :=
  ∫ A : Cfg, (χ p A * χ q A) * (Cross A B)^2 ∂haar

local notation "J" => p4Q2PY7_originalPlaquettePairTwoCrossingHaar H

/-- The original pair Haar integrals are symmetric in the
TWO ACTUAL oriented spatial plaquettes. -/
theorem p4Q2PY7_originalPlaquettePairTwoCrossing_symm
    (p q : Plaq) (B : Cfg) :
    J p q B = J q p B := by
  unfold p4Q2PY7_originalPlaquettePairTwoCrossingHaar
  apply integral_congr_ae
  filter_upwards with A
  ring

/-- Exact integral expansion of the genuine squared complete
spatial plaquette trace sum into ALL ordered spatial plaquette
pair Haar moments, including diagonal and off-diagonal pairs. -/
theorem p4Q2PY7_originalPlaquetteTraceSquare_crossingHaar_pairSum
    (B : Cfg) :
    (∫ A : Cfg, (Φ A)^2 * (Cross A B)^2 ∂haar) =
      ∑ p : Plaq, ∑ q : Plaq, J p q B := by
  classical
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hChi (p : Plaq) : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hEach (p q : Plaq) :
      Integrable (fun A : Cfg =>
        (χ p A * χ q A) * (Cross A B)^2) haar :=
    (((hChi p).mul (hChi q)).mul (hCross.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (p : Plaq) : Continuous (fun A : Cfg =>
        ∑ q : Plaq, (χ p A * χ q A) * (Cross A B)^2) := by
    apply continuous_finset_sum
    intro q _hq
    exact ((hChi p).mul (hChi q)).mul (hCross.pow 2)
  have hSums :
      (∫ A : Cfg,
        ∑ p : Plaq, ∑ q : Plaq,
          (χ p A * χ q A) * (Cross A B)^2 ∂haar) =
        ∑ p : Plaq, ∑ q : Plaq,
          (∫ A : Cfg,
            (χ p A * χ q A) * (Cross A B)^2 ∂haar) := by
    rw [integral_finset_sum _ (fun p _ =>
      (hInner p).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [integral_finset_sum _ (fun q _ => hEach p q)]
  have hPoint (A : Cfg) :
      (Φ A)^2 * (Cross A B)^2 =
        ∑ p : Plaq, ∑ q : Plaq,
          (χ p A * χ q A) * (Cross A B)^2 := by
    have hSquare :
        (∑ p : Plaq, χ p A) * (∑ q : Plaq, χ q A) =
        ∑ p : Plaq, ∑ q : Plaq, χ p A * χ q A := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
    calc
      (Φ A)^2 * (Cross A B)^2 =
          ((∑ p : Plaq, χ p A) *
            (∑ q : Plaq, χ q A)) * (Cross A B)^2 := by
        unfold p4Q2PW2_originalAllPlaquetteRealTrace
        ring
      _ = (∑ p : Plaq, ∑ q : Plaq, χ p A * χ q A) *
          (Cross A B)^2 := by rw [hSquare]
      _ = ∑ p : Plaq, ∑ q : Plaq,
          (χ p A * χ q A) * (Cross A B)^2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.sum_mul]
  calc
    (∫ A : Cfg, (Φ A)^2 * (Cross A B)^2 ∂haar) =
      ∫ A : Cfg,
        ∑ p : Plaq, ∑ q : Plaq,
          (χ p A * χ q A) * (Cross A B)^2 ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact hPoint A
    _ = ∑ p : Plaq, ∑ q : Plaq, J p q B := by
      rw [hSums]
      rfl

/-- Explicit true SU(2) centered fifth obstruction as the finite
double sum of all actual original plaquette-character PAIR Haar
moments with the complete original crossing action. -/
theorem p4Q2PY7_originalCenteredSquare_eq_plaquettePairSum
    (B : Cfg) :
    G B = (1 / 4 : ℝ) *
      (∑ p : Plaq, ∑ q : Plaq, J p q B) := by
  rw [p4Q2PY7_originalCenteredSquare_eq_plaquetteTraceSquare H B,
    p4Q2PY7_originalPlaquetteTraceSquare_crossingHaar_pairSum H B]

end TrueOriginalPlaquettePairFifth
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalPlaquettePairTwoCrossing_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalPlaquetteTraceSquare_crossingHaar_pairSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalCenteredSquare_eq_plaquettePairSum

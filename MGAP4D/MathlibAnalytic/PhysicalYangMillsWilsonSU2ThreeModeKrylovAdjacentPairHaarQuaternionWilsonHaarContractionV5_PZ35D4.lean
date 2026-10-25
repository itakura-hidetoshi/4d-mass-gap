import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionOrbitComplexV5_PZ35D3
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D4 — actual SU(2) real Wilson orbit and one-link Haar contraction

The unconditional complex SU(2) quaternion trace orbit PZ35D3 and
the exact ORIGINAL real Wilson character embedding PZ35D2 give
the unconditional four-point REAL character orbit identity.

Four genuine normalized-SU(2)-Haar left translations then yield
the exact one-link real Schur correlation 1/4. A genuine central
SU(2) element J^2=-I gives zero mean fundamental character, and hence
the one-link mixed character/Wilson energy integral is -1/4.

This is not a finite-subgroup Haar measure. The four *distinct spatial
lattice link* Fubini transport and original J_p=chi_p/256 are separate,
not yet asserted here. No new axiom/sorry/admit/native_decide.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "μ" => normalizedCompactHaar G

local instance p4Q2PZ35D4_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance p4Q2PZ35D4_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2

local instance p4Q2PZ35D4_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2

local instance p4Q2PZ35D4_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2

local instance p4Q2PZ35D4_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ35D4_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Genuine SU(2) quaternion orbit, now in the ORIGINAL normalized
REAL fundamental Wilson character. No hypothesis and no surrogate Haar. -/
theorem p4Q2PZ35D4_originalRealCharacterOrbit (b u : G) :
    (∑ j : Fin 4, χ (q j * u) * χ ((q j * u)⁻¹ * b)) = χ b := by
  have hComplex :
      (∑ j : Fin 4,
        (χ (q j * u) : ℂ) * (χ ((q j * u)⁻¹ * b) : ℂ)) =
        (χ b : ℂ) := by
    simp_rw [p4Q2PZ35D2_originalCharacter_complex_coe]
    calc
      (∑ j : Fin 4,
          (Matrix.trace ((q j * u : G) : Mat) / 2) *
            (Matrix.trace (((q j * u)⁻¹ * b : G) : Mat) / 2)) =
          (1 / 4 : ℂ) * (∑ j : Fin 4,
            Matrix.trace ((q j * u : G) : Mat) *
              Matrix.trace (((q j * u)⁻¹ * b : G) : Mat)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = (1 / 4 : ℂ) * (2 * Matrix.trace (b : Mat)) := by
        rw [p4Q2PZ35D3_SU2_complexOrbitTrace b u]
      _ = Matrix.trace (b : Mat) / 2 := by ring
  exact_mod_cast hComplex

/-- Genuine original normalized SU(2) Haar: a one-link real Wilson
character correlation is exactly one quarter the original character. -/
theorem p4Q2PZ35D4_originalOneLinkHaar_characterQuarter (b : G) :
    (∫ u : G, χ u * χ (u⁻¹ * b) ∂μ) = (1 / 4 : ℝ) * χ b := by
  simpa only [p4Q2PZ35C_originalOneLinkCharacterPair] using
    (p4Q2PZ35C_originalOneLinkHaar_quarter_of_quaternionOrbit b
      (p4Q2PZ35D4_originalRealCharacterOrbit b))

/-- Genuine SU(2) central element J², whose underlying matrix is -I. -/
def p4Q2PZ35D4_centralMinusOne : G :=
  p4Q2PZ35B_quaternionJ * p4Q2PZ35B_quaternionJ

theorem p4Q2PZ35D4_centralMinusOne_coe :
    ((p4Q2PZ35D4_centralMinusOne : G) : Mat) = -(1 : Mat) := by
  change p4Q2PZ35A_pauliQ1 * p4Q2PZ35A_pauliQ1 = -(1 : Mat)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p4Q2PZ35A_pauliQ1]

/-- The fundamental real Wilson character is odd under multiplication
by the true central SU(2) element -I. -/
theorem p4Q2PZ35D4_originalCharacter_centralFlip (u : G) :
    χ (p4Q2PZ35D4_centralMinusOne * u) = -χ u := by
  have hTrace :
      Matrix.trace (((p4Q2PZ35D4_centralMinusOne * u : G) : Mat)) =
        -Matrix.trace (u : Mat) := by
    change
      Matrix.trace (((p4Q2PZ35D4_centralMinusOne : G) : Mat) * (u : Mat)) =
        -Matrix.trace (u : Mat)
    rw [p4Q2PZ35D4_centralMinusOne_coe]
    simp
  have hComplex :
      ((χ (p4Q2PZ35D4_centralMinusOne * u) : ℝ) : ℂ) =
        -((χ u : ℝ) : ℂ) := by
    rw [p4Q2PZ35D2_originalCharacter_complex_coe,
      p4Q2PZ35D2_originalCharacter_complex_coe, hTrace]
    ring
  exact_mod_cast hComplex

private theorem p4Q2PZ35D4_originalCharacter_continuous :
    Continuous χ :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

/-- The genuine normalized SU(2) Haar integral of the original
fundamental Wilson character is ZERO by left invariance and center flip. -/
theorem p4Q2PZ35D4_originalOneLinkHaar_characterZero :
    (∫ u : G, χ u ∂μ) = 0 := by
  have h := p4Q2PZ35C_originalSU2Haar_integral_left_translate
    χ p4Q2PZ35D4_originalCharacter_continuous
    p4Q2PZ35D4_centralMinusOne
  simp_rw [p4Q2PZ35D4_originalCharacter_centralFlip] at h
  rw [integral_neg] at h
  linarith

/-- The original SU(2) one-link Wilson-character × relative Wilson
energy moment: the exact REAL Schur coefficient -1/4, with no premise. -/
theorem p4Q2PZ35D4_originalOneLinkHaar_characterEnergy (b : G) :
    (∫ u : G, χ u * E (u⁻¹ * b) ∂μ) =
      -(1 / 4 : ℝ) * χ b := by
  have hChiInt : Integrable χ μ := by
    exact p4Q2PZ35D4_originalCharacter_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace χ)
  have hPairInt : Integrable (fun u : G => χ u * χ (u⁻¹ * b)) μ := by
    exact (p4Q2PZ35C_originalOneLinkCharacterPair_continuous b).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (u : G) :
      χ u * E (u⁻¹ * b) = χ u - χ u * χ (u⁻¹ * b) := by
    unfold p4Q2PZ35C_originalOneLinkCharacter
    ring
  calc
    (∫ u : G, χ u * E (u⁻¹ * b) ∂μ) =
        ∫ u : G, (χ u - χ u * χ (u⁻¹ * b)) ∂μ := by
          apply integral_congr_ae
          filter_upwards with u
          exact hPoint u
    _ = (∫ u : G, χ u ∂μ) -
        (∫ u : G, χ u * χ (u⁻¹ * b) ∂μ) := by
          exact integral_sub hChiInt hPairInt
    _ = -(1 / 4 : ℝ) * χ b := by
      rw [p4Q2PZ35D4_originalOneLinkHaar_characterZero,
        p4Q2PZ35D4_originalOneLinkHaar_characterQuarter b]
      ring

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D4_originalRealCharacterOrbit
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D4_originalOneLinkHaar_characterQuarter
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D4_centralMinusOne_coe
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D4_originalCharacter_centralFlip
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D4_originalOneLinkHaar_characterZero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D4_originalOneLinkHaar_characterEnergy

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionOriginalSpatialHaarTranslationV5_PZ35D6
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D7 — eight TRUE SU(2) translates: pointwise Wilson contraction

Use four quaternion elements from PZ35B and the central -I from PZ35D4,
all INSIDE the original continuous compact SU(2) group. The eight-term
orbit identity is a pointwise identity, NOT averaging over a finite-group
Haar measure. On the true original spatial product Haar, eight link
translations preserve exactly the same measure by PZ35D6.

This module supplies unconditional pointwise mixed Wilson contractions
for an arbitrary right factor, including both link orientations.
The actual original four-link integral is NOT yet asserted.

No new axiom, sorry, admit, native_decide, or alternate model.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "z" => p4Q2PZ35D4_centralMinusOne
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

/-- True fundamental SU(2) character is invariant under conjugation:
this is derived from the existing literal trace character. -/
theorem p4Q2PZ35D7_originalCharacter_conjugate (c x : G) :
    χ (c⁻¹ * x * c) = χ x := by
  have h := p4Q2PZ35D5_originalEnergy_conjugate c x
  unfold p4Q2PZ35C_originalOneLinkCharacter
  rw [h]

/-- Quaternion 4-point mixed-character orbit with a TRUE arbitrary
right factor (not just the identity), pointwise in the original SU(2). -/
theorem p4Q2PZ35D7_originalForwardCharacterPairOrbit (b c u : G) :
    (∑ j : Fin 4,
      χ ((q j * u) * c) * χ ((q j * u)⁻¹ * b)) = χ (b * c) := by
  calc
    (∑ j : Fin 4,
      χ ((q j * u) * c) * χ ((q j * u)⁻¹ * b)) =
      (∑ j : Fin 4,
        χ (q j * (u * c)) * χ ((q j * (u * c))⁻¹ * (b * c))) := by
      apply Finset.sum_congr rfl
      intro j _hj
      have hg :
          (q j * (u * c))⁻¹ * (b * c) =
            c⁻¹ * ((q j * u)⁻¹ * b) * c := by group
      rw [hg, p4Q2PZ35D7_originalCharacter_conjugate]
      simp only [mul_assoc]
    _ = χ (b * c) :=
      p4Q2PZ35D4_originalRealCharacterOrbit (b * c) (u * c)

/-- Central -I reverses the character of the INVERSE link in an
arbitrary two-factor Wilson pair as well (not only a forward trace). -/
theorem p4Q2PZ35D7_originalInverseCharacter_centralFlip (v b : G) :
    χ ((z * v)⁻¹ * b) = -χ (v⁻¹ * b) := by
  calc
    χ ((z * v)⁻¹ * b) = χ (((z * v)⁻¹ * b)⁻¹) :=
      (p4Q2PZ35D5_originalCharacter_inv ((z * v)⁻¹ * b)).symm
    _ = χ (b⁻¹ * (z * v)) := by
      rw [mul_inv_rev, inv_inv]
    _ = χ ((z * v) * b⁻¹) :=
      p4Q2PZ35D5_originalCharacter_mul_comm b⁻¹ (z * v)
    _ = χ (z * (v * b⁻¹)) := by rw [mul_assoc]
    _ = -χ (v * b⁻¹) := p4Q2PZ35D4_originalCharacter_centralFlip (v * b⁻¹)
    _ = -χ (v⁻¹ * b) := by
      congr 1
      calc
        χ (v * b⁻¹) = χ (b⁻¹ * v) :=
          p4Q2PZ35D5_originalCharacter_mul_comm v b⁻¹
        _ = χ ((v⁻¹ * b)⁻¹) := by
          rw [mul_inv_rev, inv_inv]
        _ = χ (v⁻¹ * b) := p4Q2PZ35D5_originalCharacter_inv (v⁻¹ * b)

/-- The ORIGINAL Wilson plaquette energy is complemented by -I:
the two genuine SU(2) translates have energies adding to 2. -/
theorem p4Q2PZ35D7_originalEnergy_centralInverseComplement (v b : G) :
    E ((z * v)⁻¹ * b) = 2 - E (v⁻¹ * b) := by
  have h := p4Q2PZ35D7_originalInverseCharacter_centralFlip v b
  change 1 - E ((z * v)⁻¹ * b) =
    -(1 - E (v⁻¹ * b)) at h
  linarith

/-- Character with arbitrary right factor changes sign under
the genuine central SU(2) -I left translation. -/
theorem p4Q2PZ35D7_originalForwardCharacter_centralFlip (v c : G) :
    χ ((z * v) * c) = -χ (v * c) := by
  rw [mul_assoc]
  exact p4Q2PZ35D4_originalCharacter_centralFlip (v * c)

/-- Eight genuine SU(2) translates, pointwise and exact: this
is the mixed original Wilson one-link Schur projector in the
forward plaquette orientation, not a finite-group Haar integral. -/
theorem p4Q2PZ35D7_originalEightOrbit_forward (b c u : G) :
    (∑ j : Fin 4,
      (χ ((q j * u) * c) * E ((q j * u)⁻¹ * b) +
       χ ((z * (q j * u)) * c) *
         E ((z * (q j * u))⁻¹ * b))) =
      -2 * χ (b * c) := by
  have hTerm (j : Fin 4) :
      (χ ((q j * u) * c) * E ((q j * u)⁻¹ * b) +
       χ ((z * (q j * u)) * c) *
         E ((z * (q j * u))⁻¹ * b)) =
      -2 * (χ ((q j * u) * c) * χ ((q j * u)⁻¹ * b)) := by
    rw [p4Q2PZ35D7_originalForwardCharacter_centralFlip,
      p4Q2PZ35D7_originalEnergy_centralInverseComplement]
    have ht : E ((q j * u)⁻¹ * b) =
        1 - χ ((q j * u)⁻¹ * b) := by
      unfold p4Q2PZ35C_originalOneLinkCharacter
      ring
    rw [ht]
    ring
  calc
    (∑ j : Fin 4,
      (χ ((q j * u) * c) * E ((q j * u)⁻¹ * b) +
       χ ((z * (q j * u)) * c) *
         E ((z * (q j * u))⁻¹ * b))) =
      ∑ j : Fin 4, -2 * (χ ((q j * u) * c) * χ ((q j * u)⁻¹ * b)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact hTerm j
    _ = -2 * ∑ j : Fin 4,
      χ ((q j * u) * c) * χ ((q j * u)⁻¹ * b) := by
        rw [Finset.mul_sum]
    _ = -2 * χ (b * c) := by
      rw [p4Q2PZ35D7_originalForwardCharacterPairOrbit b c u]

/-- An inverse-oriented link character can be written as a
forward-oriented character without changing any SU(2) variable. -/
theorem p4Q2PZ35D7_originalInverseCharacter_as_forward
    (v c : G) : χ (v⁻¹ * c) = χ (v * c⁻¹) := by
  calc
    χ (v⁻¹ * c) = χ ((v⁻¹ * c)⁻¹) :=
      (p4Q2PZ35D5_originalCharacter_inv (v⁻¹ * c)).symm
    _ = χ (c⁻¹ * v) := by rw [mul_inv_rev, inv_inv]
    _ = χ (v * c⁻¹) :=
      p4Q2PZ35D5_originalCharacter_mul_comm c⁻¹ v

/-- Eight genuine SU(2) translates with the plaquette's
inverse-oriented link, with exact sign and target argument. -/
theorem p4Q2PZ35D7_originalEightOrbit_inverse (b c u : G) :
    (∑ j : Fin 4,
      (χ ((q j * u)⁻¹ * c) * E ((q j * u)⁻¹ * b) +
       χ ((z * (q j * u))⁻¹ * c) *
         E ((z * (q j * u))⁻¹ * b))) =
      -2 * χ (b⁻¹ * c) := by
  calc
    (∑ j : Fin 4,
      (χ ((q j * u)⁻¹ * c) * E ((q j * u)⁻¹ * b) +
       χ ((z * (q j * u))⁻¹ * c) *
         E ((z * (q j * u))⁻¹ * b))) =
      (∑ j : Fin 4,
        (χ ((q j * u) * c⁻¹) * E ((q j * u)⁻¹ * b) +
         χ ((z * (q j * u)) * c⁻¹) *
           E ((z * (q j * u))⁻¹ * b))) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [p4Q2PZ35D7_originalInverseCharacter_as_forward,
        p4Q2PZ35D7_originalInverseCharacter_as_forward]
    _ = -2 * χ (b * c⁻¹) :=
      p4Q2PZ35D7_originalEightOrbit_forward b c⁻¹ u
    _ = -2 * χ (b⁻¹ * c) := by
      congr 1
      calc
        χ (b * c⁻¹) = χ ((b * c⁻¹)⁻¹) :=
          (p4Q2PZ35D5_originalCharacter_inv (b * c⁻¹)).symm
        _ = χ (c * b⁻¹) := by rw [mul_inv_rev, inv_inv]
        _ = χ (b⁻¹ * c) :=
          p4Q2PZ35D5_originalCharacter_mul_comm c b⁻¹

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D7_originalCharacter_conjugate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D7_originalForwardCharacterPairOrbit
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D7_originalInverseCharacter_centralFlip
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D7_originalEnergy_centralInverseComplement
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D7_originalForwardCharacter_centralFlip
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D7_originalEightOrbit_forward
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D7_originalInverseCharacter_as_forward
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D7_originalEightOrbit_inverse

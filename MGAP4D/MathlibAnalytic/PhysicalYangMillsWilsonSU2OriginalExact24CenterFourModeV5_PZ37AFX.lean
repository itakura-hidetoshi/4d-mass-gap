import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAutoFourModeIntervalsV5_PZ37AFW
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFX — exact original SU(2) 24-center four-mode rational values

The actual SU(2) quaternion matrix has first-column real coordinates
x_0, x_1, x_2, x_3 from ADR and actual four real Wilson
character translates from the pre-existing genuine quaternion Q_j.

Direct original 2x2 matrix traces identify these four ORIGINAL functions:
   (phi_0, phi_1, phi_2, phi_3) = (x_0, -x_2, -x_1, -x_3).

AFQ's original 24 SU(2) centers are the actual ADS inverse maps of the
8 signed S³ coordinate axes and 16 half-diagonals. Every coordinate of
every such center belongs to Q. Hence every phi_j(center_i) is equal to
a fixed literal rational sample: 0 or ±1 on axes; ±1/2 on diagonals.

This module replaces AFW's conservative character [-1,1] intervals by
EXACT singleton rational intervals at the UNCHANGED original centers.
Only independently proved receiver/Perron/transfer rational intervals
remain external. Nothing is asserted about actual numerical receiver
samples, two-sign shell existence, coercivity or any 4D mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ComplexConjugate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "V" => p4Q2PZ37ADR_originalFourCoordinates
local notation "Psi" => p4Q2PZ37ADS_originalSphereToSU2
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters

local instance p4Q2PZ37AFX_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFX_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFX_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFX_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFX_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFX_probability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Original Wilson real fundamental character is half the real matrix
trace. This is the same definition used by the proved PZ35D2 theorem. -/
theorem p4Q2PZ37AFX_originalFourMode_realTrace
    (j : Fin 4) (g : G) :
    phi j g =
      (Matrix.trace (((q j * g : G) : Mat))).re / 2 := by
  change 1 - (1 - (Matrix.trace (((q j * g : G) : Mat))).re / (2 : ℝ)) =
    (Matrix.trace (((q j * g : G) : Mat))).re / 2
  ring

/-- Literal quaternion trace extraction for every original SU(2) matrix.
The output coordinate order/sign reflects the ACTUAL Pauli Q1/Q2/Q3,
rather than an arbitrarily chosen sign convention. -/
theorem p4Q2PZ37AFX_originalFourMode_firstColumn
    (g : G) (j : Fin 4) :
    phi j g =
      (![(((g : Mat) 0 0).re),
          -(((g : Mat) 1 0).re),
          -(((g : Mat) 0 0).im),
          -(((g : Mat) 1 0).im)] : Fin 4 → ℝ) j := by
  rw [p4Q2PZ37AFX_originalFourMode_realTrace]
  have hMat : (((q j * g : G) : Mat)) =
      (![p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
         p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3] : Fin 4 → Mat) j *
        !![((g : Mat) 0 0), -conj ((g : Mat) 1 0);
           ((g : Mat) 1 0), conj ((g : Mat) 0 0)] := by
    calc
      (((q j * g : G) : Mat)) = (((q j : G) : Mat) * (g : Mat)) := rfl
      _ = (![p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
             p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3] : Fin 4 → Mat) j *
            (g : Mat) := by rw [p4Q2PZ35B_quaternionFamily_coe]
      _ = _ := congrArg
        (fun M : Mat =>
          (![p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
             p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3] : Fin 4 → Mat) j * M)
        (p4Q2PZ37ADR_originalMatrix_fromFirstColumn g)
  rw [hMat]
  fin_cases j <;>
    simp [p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
      p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3,
      Matrix.trace_fin_two, Complex.mul_re, Complex.add_re, Complex.neg_re,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im] <;>
    ring

/-- Actual four characters are signed/permuted ADR real first-column
coordinates, not a proxy S³ test function. -/
def p4Q2PZ37AFX_coordinateIndex : Fin 4 → Fin 4 :=
  ![0, 2, 1, 3]

def p4Q2PZ37AFX_coordinateSign : Fin 4 → ℚ :=
  ![1, -1, -1, -1]

theorem p4Q2PZ37AFX_originalFourMode_coordinate
    (g : G) (j : Fin 4) :
    phi j g =
      (p4Q2PZ37AFX_coordinateSign j : ℝ) *
        (V g) (p4Q2PZ37AFX_coordinateIndex j) := by
  rw [p4Q2PZ37AFX_originalFourMode_firstColumn]
  fin_cases j <;>
    simp [p4Q2PZ37AFX_coordinateIndex, p4Q2PZ37AFX_coordinateSign,
      p4Q2PZ37ADR_originalFourCoordinates]

/-- Actual 24 AFQ centers retain the original signed unit-sphere
coordinates exactly under the proved ADS SU(2)-sphere inverse. -/
theorem p4Q2PZ37AFX_originalCenter_coordinates
    (i : Fin (Fintype.card Grid)) :
    V (gridCenter i) =
      (p4Q2PZ37AFQ_sphereCenters i : E4) := by
  change V (Psi (p4Q2PZ37AFQ_sphereCenters i)) =
    (p4Q2PZ37AFQ_sphereCenters i : E4)
  simpa only [p4Q2PZ37ADR_originalSU2ToSphere] using
    (congrArg Subtype.val
      (p4Q2PZ37ADS_sphere_roundtrip (p4Q2PZ37AFQ_sphereCenters i)))

/-- Completely literal rational coordinates of the 8 axis and
16 half-diagonal centers, independent of choice of Fin 24 numbering. -/
def p4Q2PZ37AFX_gridCoordinate
    (k : Grid) (idx : Fin 4) : ℚ :=
  match k with
  | Sum.inl (axis, sign) =>
      if idx = axis then (if sign then -1 else 1) else 0
  | Sum.inr signs =>
      if signs idx then -(1 / 2) else (1 / 2)

/-- Direct evaluation of the original AFQ S³ grid, at each of its
four coordinates; every value is a fixed rational. -/
theorem p4Q2PZ37AFX_gridCoordinate_exact
    (k : Grid) (idx : Fin 4) :
    (p4Q2PZ37AFQ_sphereGridCenter k : E4) idx =
      (p4Q2PZ37AFX_gridCoordinate k idx : ℝ) := by
  cases k with
  | inl axisSign =>
      rcases axisSign with ⟨axis, sign⟩
      by_cases h : idx = axis
      · subst idx
        cases sign <;>
          norm_num [p4Q2PZ37AFQ_sphereGridCenter,
            p4Q2PZ37AFQ_axisSphere, p4Q2PZ37AFQ_axisVector,
            p4Q2PZ37AFX_gridCoordinate]
      · cases sign <;>
          simp [p4Q2PZ37AFQ_sphereGridCenter,
            p4Q2PZ37AFQ_axisSphere, p4Q2PZ37AFQ_axisVector,
            p4Q2PZ37AFX_gridCoordinate, h]
  | inr signs =>
      by_cases h : signs idx = true
      · simp [p4Q2PZ37AFQ_sphereGridCenter,
          p4Q2PZ37AFQ_diagSphere, p4Q2PZ37AFQ_diagVector,
          p4Q2PZ37AFX_gridCoordinate, h] <;> norm_num
      · simp [p4Q2PZ37AFQ_sphereGridCenter,
          p4Q2PZ37AFQ_diagSphere, p4Q2PZ37AFQ_diagVector,
          p4Q2PZ37AFX_gridCoordinate, h] <;> norm_num

/-- Explicit fixed rational sample table for all four characters at all
24 original SU(2) centers; no floating-point or unknown Haar moments. -/
def p4Q2PZ37AFX_exactRationalCharacter
    (j : Fin 4) (i : Fin (Fintype.card Grid)) : ℚ :=
  let k : Grid := (Fintype.equivFin Grid).symm i
  p4Q2PZ37AFX_coordinateSign j *
    p4Q2PZ37AFX_gridCoordinate k (p4Q2PZ37AFX_coordinateIndex j)

theorem p4Q2PZ37AFX_originalCenter_character_exact
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    phi j (gridCenter i) =
      (p4Q2PZ37AFX_exactRationalCharacter j i : ℝ) := by
  rw [p4Q2PZ37AFX_originalFourMode_coordinate,
    p4Q2PZ37AFX_originalCenter_coordinates]
  change
    (p4Q2PZ37AFX_coordinateSign j : ℝ) *
      (p4Q2PZ37AFQ_sphereGridCenter
        ((Fintype.equivFin Grid).symm i) : E4)
          (p4Q2PZ37AFX_coordinateIndex j) =
      (p4Q2PZ37AFX_exactRationalCharacter j i : ℝ)
  rw [p4Q2PZ37AFX_gridCoordinate_exact]
  simp [p4Q2PZ37AFX_exactRationalCharacter]

/-- Exact singleton interval for each ORIGINAL four-mode character at
the true 24 centers: its half-width is zero, not AFW's coarse one. -/
def p4Q2PZ37AFX_originalCharacterSingleton
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AFV_verifiedInterval (phi j (gridCenter i)) where
  lower := p4Q2PZ37AFX_exactRationalCharacter j i
  upper := p4Q2PZ37AFX_exactRationalCharacter j i
  hLower := by
    rw [p4Q2PZ37AFX_originalCenter_character_exact]
  hUpper := by
    rw [p4Q2PZ37AFX_originalCenter_character_exact]

theorem p4Q2PZ37AFX_originalCharacterSingleton_zeroError
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    (p4Q2PZ37AFV_intervalToBall
      (p4Q2PZ37AFX_originalCharacterSingleton j i)).error = 0 := by
  simp [p4Q2PZ37AFV_intervalToBall,
    p4Q2PZ37AFX_originalCharacterSingleton]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H b0 hb0 f0

local instance p4Q2PZ37AFX_links : Fintype Link := Fintype.ofFinite _

/-- AFW's reduced input requires ONLY independently verified original
physical receiver intervals. AFX now supplies exact rational character
singletons instead of its universal [-1,1] character intervals. -/
def p4Q2PZ37AFX_toAFVOriginalIntervals
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c) :
    p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c where
  receiver := d.receiver
  character := fun j i => p4Q2PZ37AFX_originalCharacterSingleton j i

noncomputable def p4Q2PZ37AFX_toOriginalVerifiedSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c) :
    p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c :=
  p4Q2PZ37AFV_toOriginalVerifiedSamples H e c
    (p4Q2PZ37AFX_toAFVOriginalIntervals H e c d)

noncomputable def p4Q2PZ37AFX_toOriginalReceiverQuadrature
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c) :
    p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c :=
  p4Q2PZ37AFV_toOriginalReceiverQuadrature H e c hlo
    (p4Q2PZ37AFX_toAFVOriginalIntervals H e c d)

noncomputable def p4Q2PZ37AFX_toOriginalCoefficientVariance
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFV_toOriginalCoefficientVariance H e c hlo
    (p4Q2PZ37AFX_toAFVOriginalIntervals H e c d)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFX_originalFourMode_realTrace
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFX_originalFourMode_firstColumn
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFX_originalFourMode_coordinate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFX_originalCenter_coordinates
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFX_gridCoordinate_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFX_originalCenter_character_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFX_originalCharacterSingleton_zeroError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFX_toAFVOriginalIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFX_toOriginalVerifiedSamples
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFX_toOriginalReceiverQuadrature
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFX_toOriginalCoefficientVariance

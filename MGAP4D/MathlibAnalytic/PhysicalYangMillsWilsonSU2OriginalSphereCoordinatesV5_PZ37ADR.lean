import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereHaarBridgeV5_PZ37ADQ
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADR — original SU(2) in four genuine real sphere coordinates

After ADQ, begin the actual missing SU(2) → S³ geometry.
Every point is the SAME original special-unitary 2×2 matrix; the
first complex matrix column carries four real coordinates.

We prove from its actual special-unitary certificate:
* the original first column has squared complex norm one;
* the explicit four-real-coordinate vector lies on the unit 3-sphere;
* the determinant-one and unitarity axioms force a canonical
  quaternionic matrix representative, with no replacement group;
* therefore the genuine original SU(2) to S³ coordinate map is
  injective.

These are UNCONDITIONAL structural facts about the original SU(2).
Surjectivity, distance calibration, normalized-Haar pushforward
and the unconditional radial mass formula are NOT claimed here.
The ADQ radius-bound transfer therefore retains its explicit
measure-transport and ball-compatibility obligations.

No alteration to original Wilson FF source, transfer, interacting
posteriors, pair Haar, physical configuration, theorem root or pins.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators ComplexConjugate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1

/-- Original SU(2) first complex column, without any surrogate gauge group. -/
def p4Q2PZ37ADR_originalFirstColumn (g : G) : ℂ × ℂ :=
  (((g : Mat) 0 0), ((g : Mat) 1 0))

/-- Unit length of the first complex column, derived from ACTUAL unitarity
of the same original special-unitary group, not an S³ assumption. -/
theorem p4Q2PZ37ADR_originalFirstColumn_normSq_one (g : G) :
    Complex.normSq ((g : Mat) 0 0) +
      Complex.normSq ((g : Mat) 1 0) = 1 := by
  have hU : (g : Mat).conjTranspose * (g : Mat) = (1 : Mat) := by
    simpa only [Matrix.star_eq_conjTranspose] using g.property.1.1
  have h00 := congrArg (fun A : Mat => A 0 0) hU
  have hC :
      conj ((g : Mat) 0 0) * ((g : Mat) 0 0) +
        conj ((g : Mat) 1 0) * ((g : Mat) 1 0) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using h00
  have hRe := congrArg Complex.re hC
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
    conj_re, conj_im] at hRe
  simp only [Complex.normSq_apply]
  nlinarith only [hRe]

/-- Four REAL coordinates, extracted from the FIRST column of the
actual original SU(2) matrix. -/
noncomputable def p4Q2PZ37ADR_originalFourCoordinates (g : G) : E4 :=
  WithLp.toLp 2
    ![((g : Mat) 0 0).re, ((g : Mat) 0 0).im,
      ((g : Mat) 1 0).re, ((g : Mat) 1 0).im]

/-- The four original matrix coordinates have exactly unit Euclidean
squared norm. This is a 4D, not the old 8D, assertion. -/
theorem p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one (g : G) :
    ‖p4Q2PZ37ADR_originalFourCoordinates g‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hCol := p4Q2PZ37ADR_originalFirstColumn_normSq_one g
  simpa [p4Q2PZ37ADR_originalFourCoordinates, Fin.sum_univ_four,
    Complex.normSq_apply, pow_two, add_assoc, add_left_comm, add_comm] using hCol

theorem p4Q2PZ37ADR_originalFourCoordinates_norm_one (g : G) :
    ‖p4Q2PZ37ADR_originalFourCoordinates g‖ = 1 := by
  have hSq := p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one g
  have hNonneg : 0 ≤ ‖p4Q2PZ37ADR_originalFourCoordinates g‖ :=
    norm_nonneg _
  nlinarith only [hSq, hNonneg]

/-- An actual canonical map from the ORIGINAL SU(2) to the unit S³. -/
noncomputable def p4Q2PZ37ADR_originalSU2ToSphere (g : G) : S3 :=
  ⟨p4Q2PZ37ADR_originalFourCoordinates g, by
    change dist (p4Q2PZ37ADR_originalFourCoordinates g) (0 : E4) = 1
    simpa only [dist_zero_right] using
      (p4Q2PZ37ADR_originalFourCoordinates_norm_one g)⟩

/-- The exact original determinant-one unitarity certificate identifies
the genuine matrix adjugate with its genuine conjugate transpose. -/
theorem p4Q2PZ37ADR_originalAdjugate_eq_conjTranspose (g : G) :
    (g : Mat).adjugate = (g : Mat).conjTranspose := by
  have hRight : (g : Mat) * (g : Mat).conjTranspose = (1 : Mat) := by
    simpa only [Matrix.star_eq_conjTranspose] using g.property.1.2
  have hDet : (g : Mat).det = 1 := g.property.2
  calc
    (g : Mat).adjugate =
        (g : Mat).adjugate * ((g : Mat) * (g : Mat).conjTranspose) := by
          rw [hRight, mul_one]
    _ = ((g : Mat).adjugate * (g : Mat)) * (g : Mat).conjTranspose :=
      (mul_assoc _ _ _).symm
    _ = (g : Mat).conjTranspose := by
      rw [Matrix.adjugate_mul, hDet]
      simp

/-- The SECOND original complex column is uniquely forced by the
first column, using true SU(2) determinant one and unitarity. -/
theorem p4Q2PZ37ADR_originalSecondColumn_formula (g : G) :
    (g : Mat) 1 1 = conj ((g : Mat) 0 0) ∧
      (g : Mat) 0 1 = -conj ((g : Mat) 1 0) := by
  have h := p4Q2PZ37ADR_originalAdjugate_eq_conjTranspose g
  have h00 := congrArg (fun A : Mat => A 0 0) h
  have h10 := congrArg (fun A : Mat => A 1 0) h
  constructor
  · simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using h00
  · have hC : -((g : Mat) 1 0) =
        conj ((g : Mat) 0 1) := by
      simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using h10
    have hc := congrArg conj hC
    simpa using hc.symm

/-- Fully explicit quaternion-shaped representative of the SAME
actual SU(2) matrix, with no abstract isomorphism assumptions. -/
theorem p4Q2PZ37ADR_originalMatrix_fromFirstColumn (g : G) :
    (g : Mat) =
      !![((g : Mat) 0 0), -conj ((g : Mat) 1 0);
         ((g : Mat) 1 0), conj ((g : Mat) 0 0)] := by
  obtain ⟨h11, h01⟩ := p4Q2PZ37ADR_originalSecondColumn_formula g
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simpa using h01
  · rfl
  · simpa using h11

/-- The first complex matrix column determines the entire ORIGINAL
SU(2) matrix. This is stronger than the old 8-real-feature injectivity. -/
theorem p4Q2PZ37ADR_originalFirstColumn_injective :
    Function.Injective p4Q2PZ37ADR_originalFirstColumn := by
  intro g h hh
  have hA : (g : Mat) 0 0 = (h : Mat) 0 0 := congrArg Prod.fst hh
  have hB : (g : Mat) 1 0 = (h : Mat) 1 0 := congrArg Prod.snd hh
  apply Subtype.ext
  calc
    (g : Mat) =
        !![((g : Mat) 0 0), -conj ((g : Mat) 1 0);
           ((g : Mat) 1 0), conj ((g : Mat) 0 0)] :=
      p4Q2PZ37ADR_originalMatrix_fromFirstColumn g
    _ = !![((h : Mat) 0 0), -conj ((h : Mat) 1 0);
            ((h : Mat) 1 0), conj ((h : Mat) 0 0)] := by rw [hA, hB]
    _ = (h : Mat) :=
      (p4Q2PZ37ADR_originalMatrix_fromFirstColumn h).symm

/-- Injectivity of the genuine SU(2) → S³ coordinate map.
Surjectivity and normalized Haar preservation are separate theorems. -/
theorem p4Q2PZ37ADR_originalSU2ToSphere_injective :
    Function.Injective p4Q2PZ37ADR_originalSU2ToSphere := by
  intro g h hh
  have hCoord : p4Q2PZ37ADR_originalFourCoordinates g =
      p4Q2PZ37ADR_originalFourCoordinates h :=
    congrArg Subtype.val hh
  apply p4Q2PZ37ADR_originalFirstColumn_injective
  apply Prod.ext
  · apply Complex.ext
    · have hc := congrArg (fun x : E4 => x 0) hCoord
      simpa [p4Q2PZ37ADR_originalFourCoordinates] using hc
    · have hc := congrArg (fun x : E4 => x 1) hCoord
      simpa [p4Q2PZ37ADR_originalFourCoordinates] using hc
  · apply Complex.ext
    · have hc := congrArg (fun x : E4 => x 2) hCoord
      simpa [p4Q2PZ37ADR_originalFourCoordinates] using hc
    · have hc := congrArg (fun x : E4 => x 3) hCoord
      simpa [p4Q2PZ37ADR_originalFourCoordinates] using hc

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADR_originalFirstColumn_normSq_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADR_originalFourCoordinates_norm_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADR_originalAdjugate_eq_conjTranspose
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADR_originalSecondColumn_formula
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADR_originalMatrix_fromFirstColumn
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADR_originalFirstColumn_injective
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADR_originalSU2ToSphere_injective

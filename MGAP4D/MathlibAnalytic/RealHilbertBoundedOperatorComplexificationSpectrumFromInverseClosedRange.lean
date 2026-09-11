import MGAP4D.MathlibAnalytic.RealHilbertBoundedOperatorContinuousFunctionalCalculusFromComplexificationEmbedding
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- Operator-algebra data for a complexification whose range is closed under inverses.

The inverse-closedness field is deliberately stated only for elements coming from the real
operator algebra.  It says that whenever the complexification of a real bounded operator is a
unit, a two-sided inverse can be chosen inside the complexification range.  This is the exact
algebraic property needed to reflect invertibility and hence preserve the real spectrum. -/
structure RealHilbertBoundedOperatorComplexificationInverseClosedRangeData
    (H HC : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC] where
  complexify : (H →L[ℝ] H) →⋆ₐ[ℝ] (HC →L[ℂ] HC)
  isometry_complexify : Isometry complexify
  inverse_closed_range :
    ∀ {T : H →L[ℝ] H}, IsUnit (complexify T) →
      ∃ S : H →L[ℝ] H,
        complexify S * complexify T = 1 ∧
        complexify T * complexify S = 1

namespace RealHilbertBoundedOperatorComplexificationInverseClosedRangeData

variable {H HC : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- The complexification embedding is injective. -/
theorem complexify_injective
    (D : RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC) :
    Function.Injective D.complexify :=
  D.isometry_complexify.injective

/-- Invertibility of a real bounded operator is preserved by complexification. -/
theorem isUnit_complexify_of_isUnit
    (D : RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC)
    {T : H →L[ℝ] H} (hT : IsUnit T) :
    IsUnit (D.complexify T) :=
  hT.map D.complexify.toMonoidHom

/-- Inverse-closedness of the complexification range reflects invertibility back to the real
operator algebra. -/
theorem isUnit_of_isUnit_complexify
    (D : RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC)
    {T : H →L[ℝ] H} (hT : IsUnit (D.complexify T)) :
    IsUnit T := by
  obtain ⟨S, hST, hTS⟩ := D.inverse_closed_range hT
  exact Units.isUnit
    { val := T
      inv := S
      val_inv := by
        apply D.complexify_injective
        simpa using hTS
      inv_val := by
        apply D.complexify_injective
        simpa using hST }

/-- A complexification with inverse-closed range preserves and reflects units. -/
theorem isUnit_complexify_iff
    (D : RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC)
    (T : H →L[ℝ] H) :
    IsUnit (D.complexify T) ↔ IsUnit T :=
  ⟨D.isUnit_of_isUnit_complexify, D.isUnit_complexify_of_isUnit⟩

/-- Inverse-closedness of the complexification range generates preservation of the full real
spectrum of every bounded operator. -/
theorem real_spectrum_eq
    (D : RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC)
    (T : H →L[ℝ] H) :
    spectrum ℝ (D.complexify T) = spectrum ℝ T := by
  ext r
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have hUnits := D.isUnit_complexify_iff (algebraMap ℝ (H →L[ℝ] H) r - T)
  have hScalar :
      D.complexify (algebraMap ℝ (H →L[ℝ] H) r) =
        algebraMap ℝ (HC →L[ℂ] HC) r := by
    simpa only using D.complexify.commutes r
  have hMap :
      D.complexify (algebraMap ℝ (H →L[ℝ] H) r - T) =
        algebraMap ℝ (HC →L[ℂ] HC) r - D.complexify T := by
    rw [map_sub]
    exact congrArg (fun X => X - D.complexify T) hScalar
  rw [← hMap]
  exact not_congr hUnits

/-- Collapse inverse-closed complexification data to the spectrum-preserving embedding interface
used by the real-Hilbert continuous-functional-calculus descent theorem. -/
def toCFCDescentData
    (D : RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC) :
    RealHilbertBoundedOperatorComplexificationCFCDescentData H HC where
  complexify := D.complexify
  isometry_complexify := D.isometry_complexify
  real_spectrum_eq := D.real_spectrum_eq

/-- An isometric complexification with inverse-closed range therefore generates the complete
real-Hilbert bounded self-adjoint continuous functional calculus. -/
@[reducible]
noncomputable def toContinuousFunctionalCalculus
    (D : RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC) :
    ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint :=
  D.toCFCDescentData.toContinuousFunctionalCalculus

/-- Package the generated continuous functional calculus in the existing bounded-transform
interface. -/
noncomputable def toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData
    (D : RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC) :
    RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H :=
  D.toCFCDescentData.toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData

end RealHilbertBoundedOperatorComplexificationInverseClosedRangeData

end

end MathlibAnalytic
end MGAP4D

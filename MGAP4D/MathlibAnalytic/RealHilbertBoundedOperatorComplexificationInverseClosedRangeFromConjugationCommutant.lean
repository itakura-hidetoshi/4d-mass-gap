import MGAP4D.MathlibAnalytic.RealHilbertBoundedOperatorComplexificationSpectrumFromInverseClosedRange
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- Complexification data whose range is characterized as the bounded complex operators commuting
with a conjugation on the complex Hilbert space.

No algebraic or continuity assumption on `conjugation` is needed at this layer.  The standard
complexification will later supply the canonical conjugate-linear isometric involution.  For the
inverse-closedness argument, only the exact range characterization is used. -/
structure RealHilbertBoundedOperatorComplexificationConjugationCommutantData
    (H HC : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC] where
  complexify : (H →L[ℝ] H) →⋆ₐ[ℝ] (HC →L[ℂ] HC)
  isometry_complexify : Isometry complexify
  conjugation : HC → HC
  range_iff_commutes :
    ∀ X : HC →L[ℂ] HC,
      X ∈ complexify.range ↔
        ∀ x : HC, conjugation (X x) = X (conjugation x)

namespace RealHilbertBoundedOperatorComplexificationConjugationCommutantData

variable {H HC : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- Every complexified real operator commutes with the chosen conjugation. -/
theorem complexify_commutes
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC)
    (T : H →L[ℝ] H) (x : HC) :
    D.conjugation (D.complexify T x) = D.complexify T (D.conjugation x) := by
  apply (D.range_iff_commutes (D.complexify T)).mp
  exact ⟨T, rfl⟩

/-- A unit-valued complexified operator is injective as an operator on the complex Hilbert space. -/
theorem complexify_injective_of_isUnit
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC)
    {T : H →L[ℝ] H} (hT : IsUnit (D.complexify T)) :
    Function.Injective (D.complexify T) := by
  let Y : HC →L[ℂ] HC := (↑hT.unit⁻¹ : HC →L[ℂ] HC)
  have hYX : Y * D.complexify T = 1 := by
    simpa [Y, hT.unit_spec] using hT.unit.inv_val
  intro x y hxy
  calc
    x = Y (D.complexify T x) := by
      symm
      have h := congrArg (fun Z : HC →L[ℂ] HC => Z x) hYX
      simpa using h
    _ = Y (D.complexify T y) := congrArg Y hxy
    _ = y := by
      have h := congrArg (fun Z : HC →L[ℂ] HC => Z y) hYX
      simpa using h

/-- The inverse of a unit-valued complexified operator still commutes with conjugation. -/
theorem inverse_commutes
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC)
    {T : H →L[ℝ] H} (hT : IsUnit (D.complexify T))
    (x : HC) :
    D.conjugation ((↑hT.unit⁻¹ : HC →L[ℂ] HC) x) =
      (↑hT.unit⁻¹ : HC →L[ℂ] HC) (D.conjugation x) := by
  let Y : HC →L[ℂ] HC := (↑hT.unit⁻¹ : HC →L[ℂ] HC)
  have hXY : D.complexify T * Y = 1 := by
    simpa [Y, hT.unit_spec] using hT.unit.val_inv
  apply D.complexify_injective_of_isUnit hT
  calc
    D.complexify T (D.conjugation (Y x)) =
        D.conjugation (D.complexify T (Y x)) := by
      symm
      exact D.complexify_commutes T (Y x)
    _ = D.conjugation x := by
      congr 1
      have h := congrArg (fun Z : HC →L[ℂ] HC => Z x) hXY
      simpa using h
    _ = D.complexify T (Y (D.conjugation x)) := by
      symm
      have h := congrArg (fun Z : HC →L[ℂ] HC => Z (D.conjugation x)) hXY
      simpa using h

/-- The inverse of a unit-valued complexified operator belongs to the complexification range. -/
theorem inverse_mem_range
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC)
    {T : H →L[ℝ] H} (hT : IsUnit (D.complexify T)) :
    (↑hT.unit⁻¹ : HC →L[ℂ] HC) ∈ D.complexify.range := by
  apply (D.range_iff_commutes (↑hT.unit⁻¹ : HC →L[ℂ] HC)).mpr
  exact D.inverse_commutes hT

/-- Commutation with conjugation generates inverse-closedness of the complexification range. -/
theorem inverse_closed_range
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC)
    {T : H →L[ℝ] H} (hT : IsUnit (D.complexify T)) :
    ∃ S : H →L[ℝ] H,
      D.complexify S * D.complexify T = 1 ∧
      D.complexify T * D.complexify S = 1 := by
  obtain ⟨S, hS⟩ := D.inverse_mem_range hT
  let Y : HC →L[ℂ] HC := (↑hT.unit⁻¹ : HC →L[ℂ] HC)
  have hS' : D.complexify S = Y := by
    simpa [Y] using hS
  have hYX : Y * D.complexify T = 1 := by
    simpa [Y, hT.unit_spec] using hT.unit.inv_val
  have hXY : D.complexify T * Y = 1 := by
    simpa [Y, hT.unit_spec] using hT.unit.val_inv
  refine ⟨S, ?_, ?_⟩
  · rw [hS']
    exact hYX
  · rw [hS']
    exact hXY

/-- Collapse conjugation-commutant complexification data to the inverse-closed range interface. -/
def toInverseClosedRangeData
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC) :
    RealHilbertBoundedOperatorComplexificationInverseClosedRangeData H HC where
  complexify := D.complexify
  isometry_complexify := D.isometry_complexify
  inverse_closed_range := D.inverse_closed_range

/-- A conjugation-commutant characterization of the complexification range therefore generates
preservation of the full real spectrum. -/
theorem real_spectrum_eq
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC)
    (T : H →L[ℝ] H) :
    spectrum ℝ (D.complexify T) = spectrum ℝ T :=
  D.toInverseClosedRangeData.real_spectrum_eq T

/-- Collapse conjugation-commutant data directly to the spectrum-preserving CFC-descent interface. -/
def toCFCDescentData
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC) :
    RealHilbertBoundedOperatorComplexificationCFCDescentData H HC :=
  D.toInverseClosedRangeData.toCFCDescentData

/-- The conjugation-commutant range characterization generates the complete real-Hilbert bounded
self-adjoint continuous functional calculus. -/
@[reducible]
noncomputable def toContinuousFunctionalCalculus
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC) :
    ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint :=
  D.toInverseClosedRangeData.toContinuousFunctionalCalculus

/-- Package the generated CFC in the existing bounded-transform interface. -/
noncomputable def toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData
    (D : RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC) :
    RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H :=
  D.toInverseClosedRangeData.toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData

end RealHilbertBoundedOperatorComplexificationConjugationCommutantData

end

end MathlibAnalytic
end MGAP4D

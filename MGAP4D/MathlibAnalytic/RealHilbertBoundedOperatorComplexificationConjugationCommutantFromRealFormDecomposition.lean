import MGAP4D.MathlibAnalytic.RealHilbertBoundedOperatorComplexificationInverseClosedRangeFromConjugationCommutant
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- Coordinate-free real-form decomposition data for a complexification of a real Hilbert space.

The fields are exactly the identities supplied by the standard model `HC = H × H`: a real
embedding, a real-part projection, an imaginary coordinate, decomposition into real and imaginary
parts, the fixed-point characterization of the real form, and compatibility of complexified
operators with the real embedding and conjugation.  From these identities the exact
conjugation-commutant characterization of the operator range is generated below. -/
structure RealHilbertBoundedOperatorComplexificationRealFormDecompositionData
    (H HC : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC] where
  complexify : (H →L[ℝ] H) →⋆ₐ[ℝ] (HC →L[ℂ] HC)
  isometry_complexify : Isometry complexify
  conjugation : HC → HC
  ofReal : H →L[ℝ] HC
  realPart : HC →L[ℝ] H
  imagPart : HC → H
  decompose :
    ∀ z : HC,
      z = ofReal (realPart z) + Complex.I • ofReal (imagPart z)
  conjugation_ofReal :
    ∀ x : H, conjugation (ofReal x) = ofReal x
  fixed_eq_ofReal_realPart :
    ∀ z : HC, conjugation z = z → ofReal (realPart z) = z
  complexify_apply_ofReal :
    ∀ (T : H →L[ℝ] H) (x : H), complexify T (ofReal x) = ofReal (T x)
  complexify_commutes :
    ∀ (T : H →L[ℝ] H) (z : HC),
      conjugation (complexify T z) = complexify T (conjugation z)

namespace RealHilbertBoundedOperatorComplexificationRealFormDecompositionData

variable {H HC : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- Reinterpret a complex-linear bounded operator as a real-linear bounded operator.  The real
scalar law is proved directly from complex linearity, avoiding any additional scalar-compatibility
instance beyond the pinned Mathlib revision. -/
def restrictComplexScalarsToReal (X : HC →L[ℂ] HC) : HC →L[ℝ] HC :=
  ⟨
    { toFun := X
      map_add' := X.map_add
      map_smul' := by
        intro r z
        change X ((r : ℂ) • z) = (r : ℂ) • X z
        exact X.map_smul (r : ℂ) z },
    X.continuous⟩

@[simp]
theorem restrictComplexScalarsToReal_apply (X : HC →L[ℂ] HC) (z : HC) :
    restrictComplexScalarsToReal X z = X z :=
  rfl

/-- Restrict a complex-linear operator to the embedded real form and project its values back to
`H`.  When the operator commutes with conjugation, this is the unique real operator from which it
arises by complexification. -/
def realRestriction
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC)
    (X : HC →L[ℂ] HC) : H →L[ℝ] H :=
  D.realPart.comp ((restrictComplexScalarsToReal X).comp D.ofReal)

@[simp]
theorem realRestriction_apply
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC)
    (X : HC →L[ℂ] HC) (x : H) :
    D.realRestriction X x = D.realPart (X (D.ofReal x)) :=
  rfl

/-- Two complex-linear operators agreeing on the embedded real form agree everywhere, because every
complexified vector decomposes into a real vector plus `I` times a real vector. -/
theorem complexLinearMap_eq_of_eq_on_ofReal
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC)
    {X Y : HC →L[ℂ] HC}
    (h : ∀ x : H, X (D.ofReal x) = Y (D.ofReal x)) :
    X = Y := by
  ext z
  calc
    X z = X (D.ofReal (D.realPart z) + Complex.I • D.ofReal (D.imagPart z)) :=
      congrArg X (D.decompose z)
    _ = X (D.ofReal (D.realPart z)) +
        Complex.I • X (D.ofReal (D.imagPart z)) := by simp
    _ = Y (D.ofReal (D.realPart z)) +
        Complex.I • Y (D.ofReal (D.imagPart z)) := by
      rw [h, h]
    _ = Y (D.ofReal (D.realPart z) + Complex.I • D.ofReal (D.imagPart z)) := by simp
    _ = Y z := congrArg Y (D.decompose z).symm

/-- A conjugation-commuting complex operator is recovered on real vectors by restricting to the real
form and projecting to the real part. -/
theorem complexify_realRestriction_apply_ofReal
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC)
    (X : HC →L[ℂ] HC)
    (hX : ∀ z : HC, D.conjugation (X z) = X (D.conjugation z))
    (x : H) :
    D.complexify (D.realRestriction X) (D.ofReal x) = X (D.ofReal x) := by
  have hFixed : D.conjugation (X (D.ofReal x)) = X (D.ofReal x) := by
    calc
      D.conjugation (X (D.ofReal x)) = X (D.conjugation (D.ofReal x)) := hX _
      _ = X (D.ofReal x) := by rw [D.conjugation_ofReal]
  rw [D.complexify_apply_ofReal, D.realRestriction_apply]
  exact D.fixed_eq_ofReal_realPart _ hFixed

/-- A conjugation-commuting complex operator is exactly the complexification of its real
restriction. -/
theorem complexify_realRestriction_eq
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC)
    (X : HC →L[ℂ] HC)
    (hX : ∀ z : HC, D.conjugation (X z) = X (D.conjugation z)) :
    D.complexify (D.realRestriction X) = X := by
  apply D.complexLinearMap_eq_of_eq_on_ofReal
  exact D.complexify_realRestriction_apply_ofReal X hX

/-- The real-form decomposition generates the exact characterization of complexified real bounded
operators as the complex-linear operators commuting with conjugation. -/
theorem range_iff_commutes
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC)
    (X : HC →L[ℂ] HC) :
    X ∈ D.complexify.range ↔
      ∀ z : HC, D.conjugation (X z) = X (D.conjugation z) := by
  constructor
  · rintro ⟨T, hT⟩ z
    have hT' : D.complexify T = X := by
      simpa only using hT
    rw [← hT']
    exact D.complexify_commutes T z
  · intro hX
    refine ⟨D.realRestriction X, ?_⟩
    simpa only using D.complexify_realRestriction_eq X hX

/-- Collapse real-form decomposition data to the conjugation-commutant range interface. -/
def toConjugationCommutantData
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC) :
    RealHilbertBoundedOperatorComplexificationConjugationCommutantData H HC where
  complexify := D.complexify
  isometry_complexify := D.isometry_complexify
  conjugation := D.conjugation
  range_iff_commutes := D.range_iff_commutes

/-- Real-form decomposition therefore generates inverse-closedness of the complexification range. -/
theorem inverse_closed_range
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC)
    {T : H →L[ℝ] H} (hT : IsUnit (D.complexify T)) :
    ∃ S : H →L[ℝ] H,
      D.complexify S * D.complexify T = 1 ∧
      D.complexify T * D.complexify S = 1 :=
  D.toConjugationCommutantData.inverse_closed_range hT

/-- Real-form decomposition generates preservation of the full real spectrum. -/
theorem real_spectrum_eq
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC)
    (T : H →L[ℝ] H) :
    spectrum ℝ (D.complexify T) = spectrum ℝ T :=
  D.toConjugationCommutantData.real_spectrum_eq T

/-- Collapse real-form decomposition directly to the spectrum-preserving CFC-descent interface. -/
def toCFCDescentData
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC) :
    RealHilbertBoundedOperatorComplexificationCFCDescentData H HC :=
  D.toConjugationCommutantData.toCFCDescentData

/-- Real-form decomposition generates the complete real-Hilbert bounded self-adjoint continuous
functional calculus. -/
@[reducible]
noncomputable def toContinuousFunctionalCalculus
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC) :
    ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint :=
  D.toConjugationCommutantData.toContinuousFunctionalCalculus

/-- Package the generated CFC in the existing bounded-transform interface. -/
noncomputable def toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData
    (D : RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC) :
    RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H :=
  D.toConjugationCommutantData.toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData

end RealHilbertBoundedOperatorComplexificationRealFormDecompositionData

end

end MathlibAnalytic
end MGAP4D

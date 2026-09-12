import MGAP4D.MathlibAnalytic.RealHilbertBoundedOperatorComplexificationConjugationCommutantFromRealFormDecomposition
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- Coordinate-equivalence data for a complexification of a real Hilbert space.

The real continuous-linear equivalence `coordinates` identifies the complex Hilbert space with two
copies of the real Hilbert space.  The first compatibility says that multiplication by `I` is the
standard quarter-turn `(x,y) ↦ (-y,x)`.  The second says that the complexification of a real bounded
operator acts diagonally on the two coordinates.

From these two coordinate identities we generate the canonical real embedding, real and imaginary
parts, conjugation, the real-form decomposition, the conjugation-commutant range characterization,
and hence the complete real self-adjoint CFC package. -/
structure RealHilbertBoundedOperatorComplexificationCoordinateEquivData
    (H HC : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC] where
  complexify : (H →L[ℝ] H) →⋆ₐ[ℝ] (HC →L[ℂ] HC)
  isometry_complexify : Isometry complexify
  coordinates : HC ≃L[ℝ] H × H
  coordinates_I_smul :
    ∀ z : HC,
      coordinates (Complex.I • z) =
        (-(coordinates z).2, (coordinates z).1)
  complexify_coordinates :
    ∀ (T : H →L[ℝ] H) (z : HC),
      coordinates (complexify T z) =
        (T (coordinates z).1, T (coordinates z).2)

namespace RealHilbertBoundedOperatorComplexificationCoordinateEquivData

variable {H HC : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- The canonical embedding of the real form into the first coordinate. -/
def ofReal
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC) :
    H →L[ℝ] HC :=
  D.coordinates.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ H H)

/-- The first coordinate of the standard complexification. -/
def realPart
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC) :
    HC →L[ℝ] H :=
  (ContinuousLinearMap.fst ℝ H H).comp D.coordinates.toContinuousLinearMap

/-- The second coordinate of the standard complexification. -/
def imagPart
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC) :
    HC →L[ℝ] H :=
  (ContinuousLinearMap.snd ℝ H H).comp D.coordinates.toContinuousLinearMap

/-- Standard conjugation in real coordinates. -/
def conjugation
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (z : HC) : HC :=
  D.coordinates.symm ((D.coordinates z).1, -(D.coordinates z).2)

@[simp]
theorem coordinates_ofReal
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (x : H) :
    D.coordinates (D.ofReal x) = (x, 0) := by
  simp [ofReal]

@[simp]
theorem realPart_apply
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (z : HC) :
    D.realPart z = (D.coordinates z).1 :=
  rfl

@[simp]
theorem imagPart_apply
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (z : HC) :
    D.imagPart z = (D.coordinates z).2 :=
  rfl

@[simp]
theorem coordinates_conjugation
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (z : HC) :
    D.coordinates (D.conjugation z) =
      ((D.coordinates z).1, -(D.coordinates z).2) := by
  simp [conjugation]

/-- Every vector is its real part plus `I` times its imaginary part. -/
theorem decompose
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (z : HC) :
    z = D.ofReal (D.realPart z) + Complex.I • D.ofReal (D.imagPart z) := by
  apply D.coordinates.injective
  rw [map_add, D.coordinates_I_smul]
  simp

/-- Standard conjugation fixes the embedded real form. -/
theorem conjugation_ofReal
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (x : H) :
    D.conjugation (D.ofReal x) = D.ofReal x := by
  apply D.coordinates.injective
  simp

/-- A vector fixed by standard conjugation has zero imaginary coordinate. -/
theorem imagPart_eq_zero_of_conjugation_eq
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (z : HC) (hz : D.conjugation z = z) :
    D.imagPart z = 0 := by
  have hcoord := congrArg D.coordinates hz
  have hneg : -(D.coordinates z).2 = (D.coordinates z).2 := by
    simpa using congrArg Prod.snd hcoord
  have hsum : (D.coordinates z).2 + (D.coordinates z).2 = 0 := by
    calc
      (D.coordinates z).2 + (D.coordinates z).2 =
          (D.coordinates z).2 + (-(D.coordinates z).2) :=
        congrArg (fun w : H => (D.coordinates z).2 + w) hneg.symm
      _ = 0 := add_neg_cancel _
  have htwo : (2 : ℝ) • (D.coordinates z).2 = 0 := by
    simpa [two_smul] using hsum
  have hzero : (D.coordinates z).2 = 0 := by
    have h := congrArg (fun w : H => (2 : ℝ)⁻¹ • w) htwo
    simpa [smul_smul] using h
  simpa using hzero

/-- The fixed points of standard conjugation are exactly the embedded real vectors. -/
theorem fixed_eq_ofReal_realPart
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (z : HC) (hz : D.conjugation z = z) :
    D.ofReal (D.realPart z) = z := by
  apply D.coordinates.injective
  have him : D.imagPart z = 0 := D.imagPart_eq_zero_of_conjugation_eq z hz
  rw [D.coordinates_ofReal]
  apply Prod.ext
  · simp
  · simpa using him.symm

/-- Complexification acts on embedded real vectors by the original real operator. -/
theorem complexify_apply_ofReal
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (T : H →L[ℝ] H) (x : H) :
    D.complexify T (D.ofReal x) = D.ofReal (T x) := by
  apply D.coordinates.injective
  rw [D.complexify_coordinates]
  simp

/-- Diagonal coordinate action implies commutation with standard conjugation. -/
theorem complexify_commutes
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (T : H →L[ℝ] H) (z : HC) :
    D.conjugation (D.complexify T z) =
      D.complexify T (D.conjugation z) := by
  apply D.coordinates.injective
  simp [D.complexify_coordinates]

/-- Collapse coordinate-equivalence data to the real-form decomposition interface. -/
def toRealFormDecompositionData
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC) :
    RealHilbertBoundedOperatorComplexificationRealFormDecompositionData H HC where
  complexify := D.complexify
  isometry_complexify := D.isometry_complexify
  conjugation := D.conjugation
  ofReal := D.ofReal
  realPart := D.realPart
  imagPart := D.imagPart
  decompose := D.decompose
  conjugation_ofReal := D.conjugation_ofReal
  fixed_eq_ofReal_realPart := D.fixed_eq_ofReal_realPart
  complexify_apply_ofReal := D.complexify_apply_ofReal
  complexify_commutes := D.complexify_commutes

/-- Coordinate-equivalence data generate the exact conjugation-commutant characterization. -/
theorem range_iff_commutes
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (X : HC →L[ℂ] HC) :
    X ∈ D.complexify.range ↔
      ∀ z : HC, D.conjugation (X z) = X (D.conjugation z) :=
  D.toRealFormDecompositionData.range_iff_commutes X

/-- Coordinate-equivalence data generate inverse-closedness of the complexification range. -/
theorem inverse_closed_range
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    {T : H →L[ℝ] H} (hT : IsUnit (D.complexify T)) :
    ∃ S : H →L[ℝ] H,
      D.complexify S * D.complexify T = 1 ∧
      D.complexify T * D.complexify S = 1 :=
  D.toRealFormDecompositionData.inverse_closed_range hT

/-- Coordinate-equivalence data generate preservation of the full real spectrum. -/
theorem real_spectrum_eq
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC)
    (T : H →L[ℝ] H) :
    spectrum ℝ (D.complexify T) = spectrum ℝ T :=
  D.toRealFormDecompositionData.real_spectrum_eq T

/-- Coordinate-equivalence data generate the complete real-Hilbert bounded self-adjoint CFC. -/
@[reducible]
noncomputable def toContinuousFunctionalCalculus
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC) :
    ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint :=
  D.toRealFormDecompositionData.toContinuousFunctionalCalculus

/-- Package the generated CFC in the existing bounded-transform interface. -/
noncomputable def toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData
    (D : RealHilbertBoundedOperatorComplexificationCoordinateEquivData H HC) :
    RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H :=
  D.toRealFormDecompositionData.toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData

end RealHilbertBoundedOperatorComplexificationCoordinateEquivData

end

end MathlibAnalytic
end MGAP4D

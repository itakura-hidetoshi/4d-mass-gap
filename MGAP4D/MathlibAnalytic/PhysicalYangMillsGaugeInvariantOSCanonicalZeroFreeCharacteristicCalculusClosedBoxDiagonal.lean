import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionZeroFreeCharacteristicCalculusClosedBoxDiagonal
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalZeroFreeCharacteristicCalculusClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Diagonal canonical OS reciprocal characteristic calculus on complete closed
half-mass Taylor boxes, with no speed relation between admissible time and
Taylor degree. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_compactReal_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ p, box.Contains p → ∀ z ∈ Z,
          |continuousLinearMapCharacteristicDeterminantReciprocal
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) z -
            continuousLinearMapCharacteristicDeterminantReciprocal
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) z| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_tendsto_degree
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q degree hdegree box Z hZcompact margin hmargin hlimitMargin

/-- Diagonal canonical OS logarithmic absolute characteristic calculus on
complete closed half-mass Taylor boxes. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_compactReal_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ p, box.Contains p → ∀ z ∈ Z,
          |continuousLinearMapCharacteristicDeterminantLogAbs
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) z -
            continuousLinearMapCharacteristicDeterminantLogAbs
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) z| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_tendsto_degree
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q degree hdegree box Z hZcompact margin hmargin hlimitMargin

/-- Diagonal canonical OS two-point characteristic determinant-ratio calculus
on complete closed half-mass boxes and compact numerator/denominator sets. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_compactReal_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z W : Set ℝ) (hZcompact : IsCompact Z) (hWcompact : IsCompact W)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ w ∈ W,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) w|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ p, box.Contains p → ∀ z ∈ Z, ∀ w ∈ W,
          |continuousLinearMapCharacteristicDeterminantRatio
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) z w -
            continuousLinearMapCharacteristicDeterminantRatio
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) z w| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_tendsto_degree
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q degree hdegree box Z W hZcompact hWcompact
        margin hmargin hlimitMargin

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

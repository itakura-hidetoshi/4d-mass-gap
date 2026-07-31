import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionZeroFreeCharacteristicCalculusCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalCharacteristicDeterminantCompact
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

/-- Reciprocal characteristic profiles of compressed canonical OS Taylor
derivatives converge compact-uniformly under a positive continuum margin. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ lambda ∈ K, ∀ z ∈ Z,
          |continuousLinearMapCharacteristicDeterminantReciprocal
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) z -
            continuousLinearMapCharacteristicDeterminantReciprocal
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)) z| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu Z hZcompact
        margin hmargin hlimitMargin

/-- Logarithmic absolute characteristic profiles of compressed canonical OS
Taylor derivatives converge compact-uniformly. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ lambda ∈ K, ∀ z ∈ Z,
          |continuousLinearMapCharacteristicDeterminantLogAbs
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) z -
            continuousLinearMapCharacteristicDeterminantLogAbs
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)) z| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu Z hZcompact
        margin hmargin hlimitMargin

/-- Two-point characteristic determinant ratios of compressed canonical OS
Taylor derivatives converge compact-uniformly under a denominator margin. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (Z W : Set ℝ) (hZcompact : IsCompact Z) (hWcompact : IsCompact W)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ w ∈ W,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda)) w|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
          |continuousLinearMapCharacteristicDeterminantRatio
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) z w -
            continuousLinearMapCharacteristicDeterminantRatio
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)) z w| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu Z W hZcompact hWcompact
        margin hmargin hlimitMargin

/-- Complete finite canonical OS Taylor jets of reciprocal characteristic
profiles converge simultaneously on compact product sets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_product_jet
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
          |continuousLinearMapCharacteristicDeterminantReciprocal
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) z -
            continuousLinearMapCharacteristicDeterminantReciprocal
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)) z| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniformOn_compact_product_jet
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q order K hKcompact hKu hu Z hZcompact
        margin hmargin hlimitMargin

/-- Complete finite canonical OS Taylor jets of logarithmic absolute
characteristic profiles converge simultaneously. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_product_jet
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
          |continuousLinearMapCharacteristicDeterminantLogAbs
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) z -
            continuousLinearMapCharacteristicDeterminantLogAbs
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)) z| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniformOn_compact_product_jet
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q order K hKcompact hKu hu Z hZcompact
        margin hmargin hlimitMargin

/-- Complete finite canonical OS Taylor jets of two-point characteristic ratios
converge simultaneously under a denominator margin. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_product_jet
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (Z W : Set ℝ) (hZcompact : IsCompact Z) (hWcompact : IsCompact W)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ order, ∀ lambda ∈ K, ∀ w ∈ W,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda)) w|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
          |continuousLinearMapCharacteristicDeterminantRatio
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) z w -
            continuousLinearMapCharacteristicDeterminantRatio
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)) z w| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniformOn_compact_product_jet
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q order K hKcompact hKu hu Z W hZcompact hWcompact
        margin hmargin hlimitMargin

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

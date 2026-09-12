import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionCharacteristicDeterminantCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalContinuousSpectralObservableCompact
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

/-- The complete real characteristic determinant profile of a compressed
canonical OS Taylor derivative converges uniformly on compact strict half-mass
Taylor sets × compact real spectral sets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (Z : Set ℝ) (hZcompact : IsCompact Z) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ lambda ∈ K, ∀ z ∈ Z,
          |continuousLinearMapCharacteristicDeterminant
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) z -
            continuousLinearMapCharacteristicDeterminant
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)) z| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu Z hZcompact

/-- Finite vectors of real characteristic determinant samples of compressed
canonical OS Taylor derivatives converge compact-uniformly. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminantSampleJet_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    {sampleOrder : ℕ} (sample : Fin (sampleOrder + 1) → ℝ)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K,
        ‖continuousLinearMapCharacteristicDeterminantSampleJet sample
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric tau) lambda)) -
          continuousLinearMapCharacteristicDeterminantSampleJet sample
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf) lambda))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminantSampleJet_finiteDimensionalCompression_tendsto_uniformOn_compact
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q sample k K hKcompact hKu hu

/-- Complete finite canonical OS Taylor jets of characteristic determinant
profiles converge simultaneously on compact product sets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_product_jet
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (Z : Set ℝ) (hZcompact : IsCompact Z) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
          |continuousLinearMapCharacteristicDeterminant
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) z -
            continuousLinearMapCharacteristicDeterminant
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)) z| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniformOn_compact_product_jet
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q order K hKcompact hKu hu Z hZcompact

/-- A positive continuum characteristic-determinant margin is inherited
uniformly by compressed canonical OS Taylor derivatives. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_eventually_abs_gt_half_margin
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
    ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        margin / 2 < |continuousLinearMapCharacteristicDeterminant
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z| := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_eventually_abs_gt_half_margin
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu Z hZcompact
        margin hmargin hlimitMargin

/-- The positive continuum margin gives stable real characteristic zero-exclusion
for compressed canonical OS Taylor derivatives. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_eventually_ne_zero
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
    ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        continuousLinearMapCharacteristicDeterminant
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z ≠ 0 := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_eventually_ne_zero
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu Z hZcompact
        margin hmargin hlimitMargin

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

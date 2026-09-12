import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionContinuousSpectralObservablePackage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRescaledDefectResolventTaylorJetFiniteDimensionalCompressionTraceDeterminantLimit
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

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Every continuous finite-dimensional observable of a fixed canonical OS
Taylor derivative converges compact-uniformly below the half-mass threshold. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K,
        ‖Phi (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric tau) lambda)) -
          Phi (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf) lambda))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q Phi hPhi k K hKcompact hKu hu

/-- A whole finite canonical OS Taylor jet may carry a different continuous
observable at each derivative level and still converges simultaneously. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_jet
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (Phi : ℕ → (V →L[ℝ] V) → W) (hPhi : ∀ k, Continuous (Phi k))
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ k ≤ order, ∀ lambda ∈ K,
          ‖Phi k (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) -
            Phi k (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q Phi hPhi order K hKcompact hKu hu

/-- Determinants of compressed canonical OS Taylor derivatives converge
compact-uniformly below the half-mass threshold. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_det_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K,
        |(continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric tau) lambda)).det -
          (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf) lambda)).det| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_det_finiteDimensionalCompression_tendsto_uniformOn_compact
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu

/-- Every finite canonical OS Taylor jet has simultaneous compact-uniform
determinant convergence. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_det_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_jet
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ k ≤ order, ∀ lambda ∈ K,
          |(continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)).det -
            (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda)).det| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_det_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q order K hKcompact hKu hu

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

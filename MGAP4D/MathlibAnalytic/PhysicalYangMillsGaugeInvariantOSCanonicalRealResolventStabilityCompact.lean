import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityCompact
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

/-- Canonical OS fixed-Taylor-derivative real-resolvent stability on compact
strict half-mass Taylor sets and arbitrary real spectral sets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K, ∀ z ∈ Z,
      IsUnit (continuousLinearMapRealShift (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) z) ∧
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) z ≤ 2 * (M + 1) ∧
      ‖continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) z - continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q k K hKcompact hKu hu Z margin hmargin hlimitMargin M hM hlimitResolventNorm

/-- Simultaneous canonical OS real-resolvent stability for every compressed
Taylor derivative up to a fixed finite order. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product_jet
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
      IsUnit (continuousLinearMapRealShift (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) z) ∧
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) z ≤ 2 * (M + 1) ∧
      ‖continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) z - continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product_jet
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q order K hKcompact hKu hu Z margin hmargin hlimitMargin M hM hlimitResolventNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

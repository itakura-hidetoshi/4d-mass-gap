import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventHermiteCompactRectangular
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventStabilityCompact
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

variable {κ V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Canonical OS compact-uniform convergence of a normalized multipoint real
resolvent Hermite coefficient after arbitrary finite-dimensional compression. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventHermiteCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : κ → Fin (order + 1) → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K, ∀ q ∈ C,
      ‖continuousLinearMapRealResolventHermiteCoefficient order (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) (nodes q) - continuousLinearMapRealResolventHermiteCoefficient order (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) (nodes q)‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventHermiteCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q k order K hKcompact hKu hu nodes C Z hnodes margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS compact-uniform convergence of the complete normalized
multipoint Hermite jet through a fixed finite order. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : κ → Fin (order + 1) → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K, ∀ q ∈ C,
      ‖continuousLinearMapRealResolventHermiteJet order (fun j => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) (nodes q j)) - continuousLinearMapRealResolventHermiteJet order (fun j => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) (nodes q j))‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q k order K hKcompact hKu hu nodes C Z hnodes margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS simultaneous convergence of the finite Taylor-order by
finite Hermite-order rectangle over an arbitrary spectral-node family. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder hermiteOrder : ℕ) (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : κ → Fin (hermiteOrder + 1) → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ taylorOrder, ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k ≤ taylorOrder, ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ k ≤ taylorOrder, ∀ lambda ∈ K, ∀ q ∈ C,
      ‖continuousLinearMapRealResolventHermiteJet hermiteOrder (fun j => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) (nodes q j)) - continuousLinearMapRealResolventHermiteJet hermiteOrder (fun j => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) (nodes q j))‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q taylorOrder hermiteOrder K hKcompact hKu hu nodes C Z hnodes margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

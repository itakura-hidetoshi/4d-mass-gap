import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitMismatchSplit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairBetaLipschitz
import Mathlib.Tactic

/-!
# Explicit beta majorant for the adjacent SU(2) coupling residual

PR #5108 isolates the same-fine-volume coupling residual

  c_n = ||S_{H_{n+1}, beta_n} - S_{H_{n+1}, beta_{n+1}}||.

PR #5114 gives an explicit beta-Lipschitz estimate for the actual normalized
physical pair transfer.  Specializing that theorem at the common fine volume
turns c_n into a scalar weighted coupling increment

  c_n <= C_n ||beta_{n+1} - beta_n||.

Thus the coupling lane of H1-C3 is closed by summability of this explicit
weighted scalar majorant.  A geometric majorant receiver is included as a
convenient sufficient condition.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentCouplingMajorantTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentCouplingMajorantCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentCouplingMajorantSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentCouplingMajorantMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentCouplingMajorantBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentCouplingMajorantSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

section CouplingMajorant

variable
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Explicit weighted beta increment which majorizes the #5108 same-volume
normalized-pair coupling residual. -/
noncomputable def physicalYangMillsSU2AdjacentCouplingBetaMajorant
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferBetaLipschitzConstant
      (halfExtent (n + 1)) (beta n) (beta (n + 1)) *
    ‖beta (n + 1) - beta n‖

theorem physicalYangMillsSU2AdjacentCouplingBetaMajorant_nonneg
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ)
    (n : ℕ) :
    0 ≤ physicalYangMillsSU2AdjacentCouplingBetaMajorant halfExtent beta n := by
  unfold physicalYangMillsSU2AdjacentCouplingBetaMajorant
  exact mul_nonneg
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferBetaLipschitzConstant_nonneg
      (halfExtent (n + 1)) (beta n) (beta (n + 1)))
    (norm_nonneg _)

/-- The actual #5108 coupling residual is bounded by the explicit weighted
adjacent beta increment from #5114. -/
theorem physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_le_betaMajorant
    (n : ℕ) :
    physicalYangMillsSU2AdjacentCommonTransferCouplingResidual
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n ≤
      physicalYangMillsSU2AdjacentCouplingBetaMajorant halfExtent beta n := by
  unfold physicalYangMillsSU2AdjacentCommonTransferCouplingResidual
  unfold physicalYangMillsSU2AdjacentCouplingBetaMajorant
  calc
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) -
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta (n + 1)) (hbeta (n + 1))‖ =
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta (n + 1)) (hbeta (n + 1)) -
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)‖ := by
      exact norm_sub_rev _ _
    _ ≤
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferBetaLipschitzConstant
          (halfExtent (n + 1)) (beta n) (beta (n + 1)) *
        ‖beta (n + 1) - beta n‖ := by
      exact
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_norm_sub_le_beta
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (beta (n + 1)) (hbeta n) (hbeta (n + 1))

/-- Summability of the explicit weighted beta increments is sufficient for
summability of the actual #5108 coupling residual. -/
theorem physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_summable_of_betaMajorant
    (hMajorant :
      Summable
        (fun n : ℕ =>
          physicalYangMillsSU2AdjacentCouplingBetaMajorant
            halfExtent beta n)) :
    Summable
      (fun n : ℕ =>
        physicalYangMillsSU2AdjacentCommonTransferCouplingResidual
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n) := by
  refine Summable.of_nonneg_of_le
    (fun n =>
      physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_nonneg
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n)
    (fun n =>
      physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_le_betaMajorant
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n)
    hMajorant

/-- A geometric upper bound on the weighted beta increment gives coupling
summability. -/
theorem physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_summable_of_geometric_betaMajorant
    (C q : ℝ)
    (hq_nonneg : 0 ≤ q)
    (hq_lt_one : q < 1)
    (hGeometric :
      ∀ n : ℕ,
        physicalYangMillsSU2AdjacentCouplingBetaMajorant halfExtent beta n ≤
          C * q ^ n) :
    Summable
      (fun n : ℕ =>
        physicalYangMillsSU2AdjacentCommonTransferCouplingResidual
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n) := by
  have hGeomSummable : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left C
  refine Summable.of_nonneg_of_le
    (fun n =>
      physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_nonneg
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n)
    (fun n => ?_)
    hGeomSummable
  exact
    (physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_le_betaMajorant
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n).trans
      (hGeometric n)

end CouplingMajorant

end

end MathlibAnalytic
end MGAP4D

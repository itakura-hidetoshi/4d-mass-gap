import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorParallelHeatBathBlockL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBoundedColorCoercivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

section EightColorBoundedColorBridge

variable (H N : ℕ)
variable (hN : 0 < N)
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable (beta : ℝ) (hBeta : 0 ≤ beta)

local notation "C" =>
  periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
local notation "L2" =>
  PeriodicHypercubicEvenSpecialUnitaryFixedColorGibbsL2 H N hN beta hBeta
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
    H N hN beta hBeta

/-- The existing generic bounded-color common-fixed interface, specialized to
    the canonical eight Wilson heat-bath blocks on the genuine global Gibbs
    `L²` carrier, is exactly simultaneous fixedness under every one-link
    conditional-expectation projection.

    This theorem stays entirely on the Gibbs `L²` Hilbert space.  In
    particular, it does not identify this carrier with the spatial Haar `L²`
    carrier or with its Gauss-law subspace. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_boundedColorCommonFixedSpace_iff_all_singleLink_fixed
    (f : L2) :
    f ∈ boundedColorCommonFixedSpace P8 ↔
      ∀ e : PeriodicHypercubicEvenEdge H,
        (C).singleLinkHeatBathProjectionL2 e f = f := by
  constructor
  · intro hBlocks e
    change ∀ color : PeriodicHypercubicEvenEdgeColor,
      P8 color f = f at hBlocks
    have hColorBlock := hBlocks (periodicHypercubicEvenEdgeColor H e)
    have hColorFixed :=
      (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_apply_eq_self_iff_commonFixed
        H N hN beta hBeta (periodicHypercubicEvenEdgeColor H e) f).1 hColorBlock
    exact hColorFixed ⟨e, rfl⟩
  · intro hLinks
    change ∀ color : PeriodicHypercubicEvenEdgeColor,
      P8 color f = f
    intro color
    apply
      (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_apply_eq_self_iff_commonFixed
        H N hN beta hBeta color f).2
    intro e
    exact hLinks e.1

/-- The canonical eight-color residual energy, expressed through the already
    canonical bounded-color interface.  The normalization is therefore by the
    fixed color count, never by lattice volume. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
    (f : L2) : ℝ :=
  boundedColorNormalizedResidualEnergy P8 f

/-- The eight-color Gibbs `L²` residual energy is nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_nonneg
    (f : L2) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
      H N hN beta hBeta f := by
  simpa [periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2] using
    (boundedColorNormalizedResidualEnergy_nonneg P8 f)

/-- Simultaneous one-link conditional-expectation fixedness annihilates the
    canonical eight-color residual energy. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_eq_zero_of_all_singleLink_fixed
    (f : L2)
    (hFixed : ∀ e : PeriodicHypercubicEvenEdge H,
      (C).singleLinkHeatBathProjectionL2 e f = f) :
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
      H N hN beta hBeta f = 0 := by
  unfold periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
  apply boundedColorNormalizedResidualEnergy_eq_zero_of_mem_commonFixedSpace
  exact
    (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_boundedColorCommonFixedSpace_iff_all_singleLink_fixed
      H N hN beta hBeta f).2 hFixed

/-- Same-carrier specialization of the existing abstract bounded-color
    coercivity reduction to the canonical eight Wilson heat-bath blocks.

    This is deliberately the last theorem before any model-specific comparison
    with the physical one-slab transfer: both `hframe` and `hcompare` live on
    the same global Gibbs `L²` carrier as the eight block projections.  A later
    physical comparison must use an explicit, independently proved carrier
    bridge rather than a coercion or definitional identification. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBath_boundedColorCoercivity_sq_defect_lower_bound
    (κ η : ℝ)
    (hη0 : 0 ≤ η)
    (defect : L2 → ℝ)
    (hframe : ∀ f : L2,
      κ * ‖f‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
          H N hN beta hBeta f)
    (hcompare : ∀ f : L2,
      η * periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
          H N hN beta hBeta f ≤ defect f)
    (f : L2) :
    (η * κ) * ‖f‖ ^ 2 ≤ defect f := by
  apply boundedColorCoercivity_sq_defect_lower_bound P8 κ η hη0 defect
  · intro x
    simpa [periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2] using
      hframe x
  · intro x
    simpa [periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2] using
      hcompare x

end EightColorBoundedColorBridge

end

end MathlibAnalytic
end MGAP4D

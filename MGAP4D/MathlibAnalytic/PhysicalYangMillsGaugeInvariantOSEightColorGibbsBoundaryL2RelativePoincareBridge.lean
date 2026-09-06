import MGAP4D.MathlibAnalytic.BoundedColorResidualRelativePoincare
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorHeatBathBoundedColorBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSEightColorGibbsBoundaryL2PoincareBridge
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

section EightColorRelativeResidual

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

/-- The canonical eight-color Gibbs residual is unchanged after subtracting any
vector fixed by all one-link conditional expectations.  Thus the eight-color
energy is intrinsically an energy on the quotient by the full common fixed
space. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_sub_of_all_singleLink_fixed
    (f z : L2)
    (hz : ∀ e : PeriodicHypercubicEvenEdge H,
      (C).singleLinkHeatBathProjectionL2 e z = z) :
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
        H N hN beta hBeta (f - z) =
      periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
        H N hN beta hBeta f := by
  unfold periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
  apply boundedColorNormalizedResidualEnergy_sub_of_mem_commonFixedSpace
  exact
    (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_boundedColorCommonFixedSpace_iff_all_singleLink_fixed
      H N hN beta hBeta z).2 hz

/-- Relative eight-color coercivity on the genuine global Gibbs `L²` carrier.
The frame estimate is imposed only after subtracting a common-fixed component;
the comparison is still made against the literal uncentered residual because
the two residual energies are exactly equal. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBath_relativeCoercivity_sq_defect_lower_bound
    (κ η : ℝ)
    (hη0 : 0 ≤ η)
    (fixedPart : L2 → L2)
    (hfixed : ∀ f : L2,
      ∀ e : PeriodicHypercubicEvenEdge H,
        (C).singleLinkHeatBathProjectionL2 e (fixedPart f) = fixedPart f)
    (defect : L2 → ℝ)
    (hframe : ∀ f : L2,
      κ * ‖f - fixedPart f‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
          H N hN beta hBeta (f - fixedPart f))
    (hcompare : ∀ f : L2,
      η * periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
          H N hN beta hBeta f ≤ defect f)
    (f : L2) :
    (η * κ) * ‖f - fixedPart f‖ ^ 2 ≤ defect f := by
  apply
    boundedColorRelativeCoercivity_sq_defect_lower_bound
      P8 κ η hη0 fixedPart
  · intro x
    exact
      (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_boundedColorCommonFixedSpace_iff_all_singleLink_fixed
        H N hN beta hBeta (fixedPart x)).2 (hfixed x)
  · intro x
    simpa [periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2] using
      hframe x
  · intro x
    simpa [periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2] using
      hcompare x

end EightColorRelativeResidual

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The low-level boundary residual introduced by the typed Gibbs bridge is
definitionally the canonical bounded-color eight-block residual evaluated on
`boundaryAnalysis`. -/
theorem boundaryAnalyzedEightColorResidualEnergy_eq_normalizedResidual
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    Q.boundaryAnalyzedEightColorResidualEnergy n t v =
      periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
        (halfExtent n) N hN (beta n) (hbeta n)
        (Q.boundaryAnalysis n t v) := by
  rfl

/-- A common-fixed Gibbs component can be subtracted from the typed analyzed
boundary vector without changing the eight-color energy.  This is the exact
centered adapter needed to formulate the model-facing frame/Poincare estimate
on the non-fixed sector. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_sub_commonFixed_eq_boundaryAnalyzed
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
    (z : PeriodicHypercubicEvenSpecialUnitaryGibbsL2
      (halfExtent n) N hN (beta n) (hbeta n))
    (hz : ∀ e : PeriodicHypercubicEvenEdge (halfExtent n),
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
        (beta n) (hbeta n)).singleLinkHeatBathProjectionL2 e z = z) :
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
        (halfExtent n) N hN (beta n) (hbeta n)
        (Q.boundaryAnalysis n t v - z) =
      Q.boundaryAnalyzedEightColorResidualEnergy n t v := by
  rw [periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_sub_of_all_singleLink_fixed
    (halfExtent n) N hN (beta n) (hbeta n) (Q.boundaryAnalysis n t v) z hz]
  exact (Q.boundaryAnalyzedEightColorResidualEnergy_eq_normalizedResidual n t v).symm

/-- Relative/centered version of the eight-color boundary Poincare reduction.

The model may choose, for every analyzed boundary vector, an arbitrary Gibbs
component `fixedPart` fixed by all one-link heat-bath projections.  It suffices
to prove the frame inequality after subtracting this component.  The preceding
translation-invariance theorem turns that centered residual into the existing
boundary residual, so the downstream OS/continuum certificate remains
unchanged. -/
theorem boundaryPoincareDefect_of_eightColorRelativeResidual
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (kappa eta : NNReal → ℝ)
    (heta0 : ∀ t, 0 ≤ eta t)
    (fixedPart : ∀ (n : ℕ) (t : NNReal),
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →
        PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n))
    (hfixed : ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
      (e : PeriodicHypercubicEvenEdge (halfExtent n)),
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
        (beta n) (hbeta n)).singleLinkHeatBathProjectionL2 e
          (fixedPart n t v) = fixedPart n t v)
    (hframe : ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N),
      kappa t * ‖v‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
          (halfExtent n) N hN (beta n) (hbeta n)
          (Q.boundaryAnalysis n t v - fixedPart n t v))
    (hcompare : ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N),
      eta t * Q.boundaryAnalyzedEightColorResidualEnergy n t v ≤
        Q.factorizedBoundarySquaredDefect n t v)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    (eta t * kappa t) * ‖v‖ ^ 2 ≤
      Q.factorizedBoundarySquaredDefect n t v := by
  apply Q.boundaryPoincareDefect_of_eightColorResidual kappa eta heta0
  · intro m s w
    calc
      kappa s * ‖w‖ ^ 2 ≤
          periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
            (halfExtent m) N hN (beta m) (hbeta m)
            (Q.boundaryAnalysis m s w - fixedPart m s w) := hframe m s w
      _ = Q.boundaryAnalyzedEightColorResidualEnergy m s w :=
        Q.periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_sub_commonFixed_eq_boundaryAnalyzed
          m s w (fixedPart m s w) (hfixed m s w)
  · exact hcompare
  · exact n
  · exact t
  · exact v

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate

end MathlibAnalytic
end MGAP4D

end

import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSEightColorGibbsBoundaryL2PoincareBridge
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1000000

section EightColorDirectRelativeResidual

variable (H N : ℕ)
variable (hN : 0 < N)
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable (beta : ℝ) (hBeta : 0 ≤ beta)

local notation "C" =>
  periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
local notation "L2" =>
  PeriodicHypercubicEvenSpecialUnitaryGibbsL2 H N hN beta hBeta
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
    H N hN beta hBeta

/-- The canonical fixed-cardinality eight-color residual written directly on
one finite Wilson Gibbs `L²` carrier.

This definition deliberately uses only the low-level block module already in
the typed Gibbs-boundary import path.  It therefore does not cross-import the
separate physical one-slab bounded-color hierarchy. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
    (f : L2) : ℝ :=
  ((Fintype.card PeriodicHypercubicEvenEdgeColor : ℝ)⁻¹) *
    ∑ color : PeriodicHypercubicEvenEdgeColor,
      ‖f - P8 color f‖ ^ 2

/-- The direct eight-color Gibbs residual is invariant after subtracting a
vector fixed by every one-link heat-bath projection.

The proof first lifts one-link fixedness to each canonical color block and then
uses linearity.  Thus the residual depends only on the class modulo the full
one-link common fixed space, with no carrier identification and no volume
normalization. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2_sub_of_all_singleLink_fixed
    (f z : L2)
    (hz : ∀ e : PeriodicHypercubicEvenEdge H,
      (C).singleLinkHeatBathProjectionL2 e z = z) :
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
        H N hN beta hBeta (f - z) =
      periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
        H N hN beta hBeta f := by
  have hzBlock : ∀ color : PeriodicHypercubicEvenEdgeColor,
      P8 color z = z := by
    intro color
    change
      periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
          H N hN beta hBeta color z = z
    apply
      periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_apply_eq_self_of_commonFixed
        H N hN beta hBeta color z
    intro e
    exact hz e.1
  unfold periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
  apply congrArg
    (fun s : ℝ =>
      ((Fintype.card PeriodicHypercubicEvenEdgeColor : ℝ)⁻¹) * s)
  apply Finset.sum_congr rfl
  intro color _
  have hres :
      f - z - P8 color (f - z) = f - P8 color f := by
    rw [map_sub, hzBlock color]
    abel
  rw [hres]

end EightColorDirectRelativeResidual

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

/-- The residual used by the existing typed Gibbs-boundary certificate is
exactly the direct canonical eight-color residual of the analyzed Gibbs
vector. -/
theorem boundaryAnalyzedEightColorResidualEnergy_eq_directNormalizedResidual
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    Q.boundaryAnalyzedEightColorResidualEnergy n t v =
      periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
        (halfExtent n) N hN (beta n) (hbeta n)
        (Q.boundaryAnalysis n t v) := by
  rfl

/-- Subtracting any explicitly common-fixed Gibbs component from the analyzed
boundary vector leaves the typed eight-color boundary residual unchanged. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2_sub_commonFixed_eq_boundaryAnalyzed
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
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
        (halfExtent n) N hN (beta n) (hbeta n)
        (Q.boundaryAnalysis n t v - z) =
      Q.boundaryAnalyzedEightColorResidualEnergy n t v := by
  rw [periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2_sub_of_all_singleLink_fixed
    (halfExtent n) N hN (beta n) (hbeta n) (Q.boundaryAnalysis n t v) z hz]
  exact (Q.boundaryAnalyzedEightColorResidualEnergy_eq_directNormalizedResidual n t v).symm

/-- Relative/centered form of the eight-color boundary Poincare reduction.

The model-facing frame estimate may be proved after subtracting any Gibbs
component fixed by every one-link heat-bath projection.  Exact residual
translation invariance converts that centered frame estimate to the already
established typed boundary residual, leaving the comparison and downstream
OS/continuum route unchanged. -/
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
        periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
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
          periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
            (halfExtent m) N hN (beta m) (hbeta m)
            (Q.boundaryAnalysis m s w - fixedPart m s w) := hframe m s w
      _ = Q.boundaryAnalyzedEightColorResidualEnergy m s w :=
        Q.periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2_sub_commonFixed_eq_boundaryAnalyzed
          m s w (fixedPart m s w) (hfixed m s w)
  · exact hcompare
  · exact n
  · exact t
  · exact v

/-- Centered eight-color frame estimates can be fed directly into the existing
shared-boundary `L²` Poincare certificate constructor.  This preserves the
established continuum slope field and changes only the model-facing
presentation of the frame obligation. -/
noncomputable def toApproximatingBoundaryL2PoincareGapCertificate_of_eightColorRelativeResidual
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (mass : ℝ)
    (hmass : 0 < mass)
    (kappa eta : NNReal → ℝ)
    (hkappa0 : ∀ t, 0 ≤ kappa t)
    (heta0 : ∀ t, 0 ≤ eta t)
    (hetaKappa_le_one : ∀ t, eta t * kappa t ≤ 1)
    (hslope :
      Tendsto
        (fun t : NNReal =>
          (t : ℝ)⁻¹ *
            (1 - Real.sqrt (1 - eta (t + t) * kappa (t + t))))
        (nhdsWithin 0 (Ioi 0))
        (nhds mass))
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
        periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
          (halfExtent n) N hN (beta n) (hbeta n)
          (Q.boundaryAnalysis n t v - fixedPart n t v))
    (hcompare : ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N),
      eta t * Q.boundaryAnalyzedEightColorResidualEnergy n t v ≤
        Q.factorizedBoundarySquaredDefect n t v) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2PoincareGapCertificate_of_eightColorResidual
    mass hmass kappa eta hkappa0 heta0 hetaKappa_le_one hslope
    (by
      intro n t v
      calc
        kappa t * ‖v‖ ^ 2 ≤
            periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2
              (halfExtent n) N hN (beta n) (hbeta n)
              (Q.boundaryAnalysis n t v - fixedPart n t v) := hframe n t v
        _ = Q.boundaryAnalyzedEightColorResidualEnergy n t v :=
          Q.periodicHypercubicEvenSpecialUnitaryEightColorHeatBathDirectNormalizedResidualEnergyL2_sub_commonFixed_eq_boundaryAnalyzed
            n t v (fixedPart n t v) (hfixed n t v))
    hcompare

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate

end MathlibAnalytic
end MGAP4D

end
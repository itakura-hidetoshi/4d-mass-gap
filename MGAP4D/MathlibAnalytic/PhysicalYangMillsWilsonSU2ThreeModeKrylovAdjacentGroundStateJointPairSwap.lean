import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairSwapEquivariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentExactBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSwapOneLinkConjugacy
import Mathlib.Tactic

/-!
# Intertwining pair-Haar and ground-state joint endpoint swaps

The repository already contains two exact endpoint-swap constructions:

* the pair-Haar L2 swap, now specialized to the actual adjacent Krylov orbit;
* the genuine ground-state joint-L2 swap, together with right/left one-link
  conditional-expectation conjugacy.

The missing bridge is the exact half-density change of measure between those
two Hilbert carriers.  This file proves that the half-density equivalence
intertwines the two swaps,

  S_joint (U f) = U (S_pair f).

The only density input is the already-proved pointwise endpoint symmetry of the
normalized ground-state joint weight.  No uniform density bound is introduced.

Specializing to the actual adjacent SU(2) orbit then gives an exact formula for
the swapped frozen joint vector: its common right factor moves to the first
pair-Haar endpoint and its mode-dependent seed factor moves to the second.
Consequently the original left one-link residual is exactly the ordinary right
one-link residual of that swapped seed-on-the-right vector.

No posterior covariance is identified with an L2 coordinate norm, and no
conditional expectation is identified with the physical transfer operator.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance p3JointPairSwapBridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3JointPairSwapBridgeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3JointPairSwapBridgeSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3JointPairSwapBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3JointPairSwapBridgeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3JointPairSwapBridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The square-root density used by the exact pair-Haar/joint change of measure
inherits the pointwise endpoint symmetry of the normalized joint density. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
        H N hN beta hbeta z.swap =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
        H N hN beta hbeta z := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_swap
      H N hN beta hbeta z
  ]

/-- The exact half-density Hilbert equivalence intertwines the pair-Haar
endpoint swap with the genuine ground-state joint endpoint swap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2_swap_intertwine
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N f) := by
  let muP :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let muJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let S :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  let hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  have hJP : muJ ≪ muP := by
    simpa [muJ, muP] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
        H N hN beta hbeta
  have hSfP :
      S f =ᵐ[muP] fun z => f z.swap := by
    simpa [S, muP] using
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_coeFn
        H N f
  have hSfJ :
      S f =ᵐ[muJ] fun z => f z.swap :=
    hJP.ae_eq hSfP
  have hUf :
      U f =ᵐ[muJ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
          H N hN beta hbeta f := by
    simpa [U] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
        H N hN beta hbeta f
  have hUfSwap :=
    hs.quasiMeasurePreserving.ae hUf
  have hUSf :
      U (S f) =ᵐ[muJ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
          H N hN beta hbeta (S f) := by
    simpa [U] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
        H N hN beta hbeta (S f)
  have hE :
      E (U f) =ᵐ[muJ] fun z => U f z.swap := by
    change
      Lp.compMeasurePreserving Prod.swap hs (U f) =ᵐ[muJ]
        fun z => U f z.swap
    simpa [Function.comp_def] using
      (Lp.coeFn_compMeasurePreserving (U f) hs)
  apply Lp.ext
  filter_upwards [hE, hUfSwap, hUSf, hSfJ] with z hEz hUfs hUS hS
  calc
    E (U f) z = U f z.swap := hEz
    _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
          H N hN beta hbeta f z.swap := hUfs
    _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
          H N hN beta hbeta (S f) z := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
      rw [hS]
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity_swap
          H N hN beta hbeta z
      ]
    _ = U (S f) z := hUS.symm

namespace GroundStatePosteriorJoint

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Orbit" =>
  physicalYangMillsSU2AdjacentFinePairOrbitVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "NormTransfer" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
    Hn 2 Pos (beta n) (hbeta n)
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    Hn 2 Pos (beta n) (hbeta n)
local notation "SPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry Hn 2
local notation "SJoint" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
    Hn 2 Pos (beta n) (hbeta n)

/-- At the final frozen coupling, pair swap commutes with the normalized pair
transfer on the actual adjacent orbit. -/
theorem
    physicalYangMillsSU2AdjacentFinePairOrbit_pairSwap_normalizedTransfer
    (k : Fin 3) :
    SPair (NormTransfer (Orbit n r k)) =
      NormTransfer (SPair (Orbit n r k)) := by
  rw [
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]
  exact
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_pairSwap_commute_decomposable
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r)

/-- Exact swapped form of the unchanged frozen ground-state joint vector.
The common right orbit factor is now first and the mode-dependent seed-evolved
factor is second. -/
theorem
    physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector_swap_eq_decomposable
    (k : Fin 3) :
    SJoint (Frozen n r k) =
      U
        (NormTransfer
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            Hn 2
            (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r k))) := by
  have hFrozen :
      Frozen n r k = U (NormTransfer (Orbit n r k)) := by
    calc
      Frozen n r k =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
            Hn 2 Pos (beta n) (hbeta n)
            (fineFrozenBCF
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r k) :=
        (fineFrozenBCF_rep_eq
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k).symm
      _ = U (NormTransfer (Orbit n r k)) := by
        unfold fineFrozenBCF
        exact
          jointTransferBCF_rep_eq
            Hn 2 Pos (beta n) (hbeta n) (Orbit n r k)
  rw [hFrozen]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2_swap_intertwine
      Hn 2 Pos (beta n) (hbeta n) (NormTransfer (Orbit n r k))
  ]
  rw [
    physicalYangMillsSU2AdjacentFinePairOrbit_pairSwap_normalizedTransfer
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]
  rw [
    physicalYangMillsSU2AdjacentFinePairOrbitVector_pairSwap_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]

/-- The original left one-link residual is exactly the right one-link residual
of the endpoint-swapped frozen vector.  This is the lossless direction needed
to apply right-boundary estimates to the mode-dependent seed factor after
swap. -/
theorem
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_norm_eq_swappedRight
    (k : Fin 3)
    (e : Link) :
    ‖Frozen n r k -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          Hn 2 Pos (beta n) (hbeta n) e (Frozen n r k)‖ =
      ‖SJoint (Frozen n r k) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          Hn 2 Pos (beta n) (hbeta n) e (SJoint (Frozen n r k))‖ := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightResidual_norm_eq_left
      Hn 2 Pos (beta n) (hbeta n) e (SJoint (Frozen n r k))
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_apply_apply
  ] using h

/-- Same residual identity with the swapped frozen vector replaced by its exact
decomposable seed-on-the-right formula. -/
theorem
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_norm_eq_decomposableRight
    (k : Fin 3)
    (e : Link) :
    ‖Frozen n r k -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          Hn 2 Pos (beta n) (hbeta n) e (Frozen n r k)‖ =
      ‖U
          (NormTransfer
            (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
              Hn 2
              (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r)
              (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r k))) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          Hn 2 Pos (beta n) (hbeta n) e
          (U
            (NormTransfer
              (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
                Hn 2
                (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                  n r)
                (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                  n r k))))‖ := by
  rw [
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_norm_eq_swappedRight
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e,
    physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector_swap_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]

end ActualAdjacentOrbit

end GroundStatePosteriorJoint

end

end MathlibAnalytic
end MGAP4D

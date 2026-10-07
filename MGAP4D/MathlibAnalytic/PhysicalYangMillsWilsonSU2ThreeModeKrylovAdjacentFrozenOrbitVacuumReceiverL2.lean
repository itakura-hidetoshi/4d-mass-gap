import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorMeanTransferBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentSwappedSeedRightResampling
import Mathlib.Tactic

/-!
# Uniform vacuum-L2 receiver for the actual frozen adjacent orbit

The exact Gram--Schmidt posterior mean from PR #5254 is a special case of a
canonical bounded-continuous representative of the normalized physical
one-slab transfer, for any genuine physical Haar-L2 input f:

  M_f(B) = lambda^(-1) integral K(A,B) f(A) dHaar(A) / Omega(B).

Its vacuum-L2 class is exactly U(S f), where U is the established
Haar-to-vacuum isometry and S is the normalized physical transfer.  Hence

  ||M_f||_{L2(vacuum)} = ||S f||_{L2(Haar)} <= ||f||_{L2(Haar)}.

The special input f from PR #5254 gives literally the same posterior-mean
BCF, not merely an a.e.-equal substitute.

For the actual adjacent pair orbit, the seed-evolved left and common-right
physical factors are computed with beta(n+1), but the receiver is built
with the separate frozen parameter beta(n).  Both factors have L2 norm
at most one at every finite orbit depth r, so both frozen receiver
vectors lie in the vacuum-L2 unit ball without a volume-dependent
inverse-vacuum supremum.

This file does not assert locality of the evolved input, does not identify
posterior covariance with an L2 coordinate, and does not replace the
signed output drift or the joint Dirichlet energy.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3FrozenOrbitVacuumReceiverTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3FrozenOrbitVacuumReceiverCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3FrozenOrbitVacuumReceiverSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3FrozenOrbitVacuumReceiverMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3FrozenOrbitVacuumReceiverBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3FrozenOrbitVacuumReceiverSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3FrozenOrbitVacuumReceiverProbability
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- Canonical frozen physical transfer receiver, defined for an arbitrary
physical slice L2 input without assuming its pointwise representative is
continuous or supported on finitely many links. -/
noncomputable def normalizedPhysicalOneSlabVacuumReceiverBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun B =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ *
          decomposableOneSliceTransferIntegral H N beta
            (f :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) B /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta B,
      by
        have hInt :=
          decomposableOneSliceTransferIntegral_continuous
            H N hN beta hbeta
            (f :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        have hOmega :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
            H N hN beta hbeta
        exact
          (continuous_const.mul hInt).div hOmega
            (fun B =>
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
                H N hN beta hbeta B).ne')⟩

/-- Exact vacuum-L2 identity, uniformly for every physical input:
the continuous receiver is the old Haar-to-vacuum transform of the
normalized physical transfer, with all normalization factors intact. -/
theorem normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_eq_haarToVacuum_normalizedTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabVacuumReceiverBCF
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let g : Lp ℝ 2 mu :=
    ((S f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 mu)
  let M :=
    normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f
  have hnuMu : nu ≪ mu := by
    simpa [nu, mu] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_absolutelyContinuous_Haar
        H N hN beta hbeta
  have hMrep :=
    BoundedContinuousFunction.coeFn_toLp 2 nu ℝ M
  have hUrep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta g
  have hGmu :
      g =ᵐ[mu] fun B =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ *
          decomposableOneSliceTransferIntegral H N beta
            (f :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            B := by
    simpa [g, S, mu] using
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_ae_eq_inv_mul_decomposableOneSliceTransferIntegral
        H N hN beta hbeta f)
  have hGnu := hnuMu.ae_eq hGmu
  have hOmegaMu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H N hN beta hbeta
  have hOmegaNu := hnuMu.ae_eq hOmegaMu
  change
    BoundedContinuousFunction.toLp 2 nu ℝ M =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H N hN beta hbeta g
  apply Lp.ext
  filter_upwards [hMrep, hUrep, hGnu, hOmegaNu]
      with B hM hU hG hOmega
  rw [hM, hU]
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
      decomposableOneSliceTransferIntegral H N beta
        (f :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        B /
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta B =
      g B /
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 B
  rw [hG, hOmega]

/-- The norm of the physical receiver is exactly the norm of the original
normalized physical transfer image. -/
theorem normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_norm_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabVacuumReceiverBCF
          H N hN beta hbeta f)‖ =
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f‖ := by
  rw [normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_eq_haarToVacuum_normalizedTransfer
    H N hN beta hbeta f]
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ =
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
          H N hN beta hbeta).norm_map _
    _ =
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f‖ := rfl

/-- Contraction of the physical receiver with coefficient one and no
volume-dependent vacuum denominator bound. -/
theorem normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabVacuumReceiverBCF
          H N hN beta hbeta f)‖ ≤ ‖f‖ := by
  rw [normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_norm_eq
    H N hN beta hbeta f]
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  have hNorm :
      ‖S‖ = 1 := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        H N hN beta hbeta
  change ‖S f‖ ≤ ‖f‖
  calc
    ‖S f‖ ≤ ‖S‖ * ‖f‖ := ContinuousLinearMap.le_opNorm S f
    _ = ‖f‖ := by rw [hNorm, one_mul]

/-- At the genuine initial Gram--Schmidt seed, the generic receiver
is literally the posterior-mean BCF already constructed in PR #5254. -/
theorem normalizedPhysicalOneSlabVacuumReceiverBCF_gramSchmidt_eq_posteriorMean
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    normalizedPhysicalOneSlabVacuumReceiverBCF
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H mode) =
      physicalYangMillsSU2PrimaryPlaquetteGramSchmidtVacuumDividedPosteriorMeanBCF
        H mode beta hbeta := by
  apply BoundedContinuousFunction.ext
  intro B
  rfl

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive

/-- Any evolved left factor has frozen beta(n) receiver vacuum-L2 norm
at most one, although its orbit was formed using beta(n+1). -/
theorem physicalYangMillsSU2AdjacentFineOrbitLeftFrozenVacuumReceiver_norm_le_one
    (k : Fin 3) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          Hn 2 Pos (beta n) (hbeta n))
        ℝ
        (normalizedPhysicalOneSlabVacuumReceiverBCF
          Hn 2 Pos (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k))‖ ≤ 1 := by
  have hReceiver :=
    normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_norm_le
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)
  exact hReceiver.trans
    (fineOrbitLeftFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)

/-- The actual common right factor obeys the same frozen receiver bound at
every orbit depth.  No mode index k enters this receiver. -/
theorem physicalYangMillsSU2AdjacentFineOrbitRightFrozenVacuumReceiver_norm_le_one :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          Hn 2 Pos (beta n) (hbeta n))
        ℝ
        (normalizedPhysicalOneSlabVacuumReceiverBCF
          Hn 2 Pos (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r))‖ ≤ 1 := by
  have hReceiver :=
    normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_norm_le
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r)
  exact hReceiver.trans
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r)

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

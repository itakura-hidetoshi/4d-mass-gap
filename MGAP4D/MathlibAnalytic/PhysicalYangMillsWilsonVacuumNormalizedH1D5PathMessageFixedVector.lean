import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5PureUnfixedPathKernelCriterion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterization
import Mathlib.Tactic

/-!
# H1-D5 as a fixed-vector equation for the literal finite Wilson path message

After #5035, H1-D5 is a scalar identity for the unnormalized complete
positive-half Wilson path-kernel moment against all decomposable physical pair
tests.

This file puts that scalar message back into pair-Haar `L²`, without adding a
new integrability hypothesis: multiply the already normalized finite OS vacuum
pair by the positive square root of the finite-volume partition function.  The
existing representative theorems identify the resulting `L²` vector a.e. with
the unnormalized path-kernel moment.

The scalar criterion can then be upgraded, using the completed physical pair
carrier separation theorem, to an exact vector equation.  Equivalently the raw
pair transfer has this finite Wilson path message as an eigenvector with
eigenvalue the square of the physical one-slab top eigenvalue.

No completed-transfer, semigroup-family, Perron--Frobenius alignment, or new
model assumption appears in the right-hand criteria.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5PathMessageTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5PathMessageCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5PathMessageSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5PathMessageMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5PathMessageBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5PathMessageSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5PathMessagePairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

section PathMessage

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- Canonical pair-Haar `L²` realization of the unnormalized complete
positive-half finite Wilson vacuum path message.  It is obtained by undoing
exactly the finite partition square-root normalization of the canonical-sign OS
vacuum pair. -/
noncomputable def physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
  Real.sqrt
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
          (beta n) (hbeta n)).base.partitionFunction •
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n

/-- The path-message `L²` vector is represented a.e. by the literal
unnormalized complete positive-half path-kernel moment. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_coeFn
    (n : ℕ) :
    (fun q =>
      physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
        Q hInvariant n q) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
        (halfExtent n) N]
      periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
        (halfExtent n) N (beta n) := by
  let H := halfExtent n
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
  let z :=
    Real.sqrt
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN
          (beta n) (hbeta n)).base.partitionFunction
  let phi :=
    periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
      H N (beta n)
  have hZ :
      0 <
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN
            (beta n) (hbeta n)).base.partitionFunction :=
    compact_oriented_partitionFunction_pos
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN
          (beta n) (hbeta n)).base
      (continuous_compact_oriented_boltzmannIntegrable
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN
            (beta n) (hbeta n)))
  have hz : z ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hZ)
  have hvac :
      (fun q => vac q) =ᵐ[mu]
        periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
          H N hN (beta n) (hbeta n) := by
    simpa [vac, mu, H] using
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_coeFn_eq_boundaryVacuumMomentPairCoordinate
        Q hInvariant n
  have hsmul := Lp.coeFn_smul z vac
  change
    (fun q => (z • vac) q) =ᵐ[mu] phi
  filter_upwards [hsmul, hvac] with q hsq hvq
  rw [hsq]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hvq]
  rw [
    periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_eq_invSqrtPartition_mul_unfixedPathKernelMomentPairCoordinate
      H N hN (beta n) (hbeta n) q]
  change z * (z⁻¹ * phi q) = phi q
  rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]

/-- The unnormalized path message stays inside the completed physical pair
carrier because it is a nonzero scalar multiple of the theorem-generated
canonical-sign finite OS vacuum pair. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_mem_physicalPairCarrier
    (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
        Q hInvariant n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N := by
  unfold physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
  exact
    Submodule.smul_mem
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N)
      _
      (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_mem_physicalPairCarrier
        Q hInvariant n)

end PathMessage

/-- Generic normalization removal: fixedness under normalized pair transfer is
equivalent to a raw pair-transfer eigen-equation with eigenvalue
`‖T_phys‖²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransfer_fixed_iff_rawPairTransfer_eigen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta f = f ↔
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta f =
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ^ 2) • f := by
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  have hc : c ≠ 0 := by
    exact pow_ne_zero 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta).ne'
  constructor
  · intro h
    change
      c⁻¹ •
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta f = f at h
    calc
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta f =
        (1 : ℝ) •
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta f := by simp
      _ = (c * c⁻¹) •
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta f := by rw [mul_inv_cancel₀ hc]
      _ = c •
          (c⁻¹ •
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta f) := by
            rw [smul_smul]
      _ = c • f := by rw [h]
      _ =
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ^ 2) • f := by rfl
  · intro h
    change
      c⁻¹ •
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta f = f
    change
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta f = c • f at h
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]

section VacuumNormalizedH1D5PathMessage

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- #5035's decomposable-test criterion is equivalent to exact fixedness of the
canonical unnormalized finite Wilson path-message vector under normalized raw
pair transfer. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_unfixedPathKernelMomentPairL2_fixed :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)
            (physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
              Q hInvariant n) =
          physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
            Q hInvariant n := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_pureUnfixedPathKernelMoment
      Q hInvariant C]
  constructor
  · intro h n
    let H := halfExtent n
    let msg :=
      physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
        Q hInvariant n
    let phi :=
      periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
        H N (beta n)
    let S2 :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN (beta n) (hbeta n)
    have hmsg :
        msg ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
      simpa [msg, H] using
        physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_mem_physicalPairCarrier
          Q hInvariant n
    have hSmsg :
        S2 msg ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
          H N hN (beta n) (hbeta n) hmsg
    have hrep :
        msg =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
          phi := by
      simpa [msg, phi, H] using
        physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_coeFn
          Q hInvariant n
    apply
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_of_inner_decomposable_eq
        H N hSmsg hmsg
    intro x y
    have hleft :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_inner_physicalPairDecomposable_eq_literalWilsonIntegral_of_representative
        H N hN (beta n) (hbeta n) msg x y phi hrep
    have hright :=
      periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral_of_representative
        H N msg x y phi hrep
    calc
      inner ℝ (S2 msg)
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N x y) =
        periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
          H N hN (beta n) (hbeta n) phi x y := by
            simpa [S2,
              periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient] using hleft
      _ =
        periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
          H N phi x y := by
            simpa [H, phi] using h n x y
      _ =
        inner ℝ msg
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N x y) := by
            symm
            simpa [
              periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient] using hright
  · intro h n x y
    let H := halfExtent n
    let msg :=
      physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
        Q hInvariant n
    let phi :=
      periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
        H N (beta n)
    let S2 :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN (beta n) (hbeta n)
    have hrep :
        msg =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
          phi := by
      simpa [msg, phi, H] using
        physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_coeFn
          Q hInvariant n
    have hleft :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_inner_physicalPairDecomposable_eq_literalWilsonIntegral_of_representative
        H N hN (beta n) (hbeta n) msg x y phi hrep
    have hright :=
      periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral_of_representative
        H N msg x y phi hrep
    have hfix : S2 msg = msg := by
      simpa [S2, msg, H] using h n
    calc
      periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
          H N hN (beta n) (hbeta n) phi x y =
        inner ℝ (S2 msg)
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N x y) := by
            symm
            simpa [S2,
              periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient] using hleft
      _ =
        inner ℝ msg
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N x y) := by rw [hfix]
      _ =
        periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
          H N phi x y := by
            simpa [
              periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient] using hright

/-- Raw operator form of H1-D5: the unnormalized complete finite Wilson path
message must be an eigenvector of the ambient raw pair transfer with eigenvalue
`‖T_phys‖²`. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_unfixedPathKernelMomentPairL2_rawEigen :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)
            (physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
              Q hInvariant n) =
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)‖ ^ 2) •
            physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
              Q hInvariant n := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_unfixedPathKernelMomentPairL2_fixed
      Q hInvariant C]
  constructor
  · intro h n
    exact
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransfer_fixed_iff_rawPairTransfer_eigen
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
          Q hInvariant n)).1
        (h n)
  · intro h n
    exact
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransfer_fixed_iff_rawPairTransfer_eigen
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
          Q hInvariant n)).2
        (h n)

/-- Fixed-space form: H1-D5 is exactly the statement that the literal
unnormalized finite Wilson path message lies in the completed physical top-top
pair block at every scale. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_unfixedPathKernelMomentPairL2_mem_topTopBlockClosure :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
            Q hInvariant n ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
            (halfExtent n) N hN (beta n) (hbeta n) := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_unfixedPathKernelMomentPairL2_fixed
      Q hInvariant C]
  constructor
  · intro h n
    have hmem :=
      physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_mem_physicalPairCarrier
        Q hInvariant n
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_fixed_iff_mem_topTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
          Q hInvariant n)
        hmem).1
        (h n)
  · intro h n
    have hmem :=
      physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_mem_physicalPairCarrier
        Q hInvariant n
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_fixed_iff_mem_topTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
          Q hInvariant n)
        hmem).2
        (h n)

end VacuumNormalizedH1D5PathMessage

end

end MathlibAnalytic
end MGAP4D

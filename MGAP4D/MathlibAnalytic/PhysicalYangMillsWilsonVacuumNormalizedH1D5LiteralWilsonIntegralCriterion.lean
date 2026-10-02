import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5MatrixCriterion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferFactorization
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelPairingFubini
import Mathlib.Tactic

/-!
# Literal Wilson-integral criterion for the vacuum-normalized H1-D5 seam

The matrix-coefficient reduction of H1-D5 leaves the scalar identity

`⟪S₂ Ω, x ⊠ y⟫ = ⟪Ω, x ⊠ y⟫`

for every finite scale and every pair of one-slice Gauss-law physical test
vectors.

This file removes the remaining operator-level packaging from that criterion.

* The normalized physical pair transfer is unfolded into the inverse square of
  the physical one-slab top eigenvalue times the raw pair transfer.
* The raw pair-transfer matrix coefficient is evaluated by the existing
  Hilbert--Schmidt/Fubini theorem using the literal two-endpoint Wilson kernel.
* The decomposable test vector is evaluated by its literal external-tensor
  representative.

The result is an exact equivalence between H1-D5 and one finite-dimensional
Wilson-kernel integral identity.  In particular the right-hand criterion no
longer mentions the approximating semigroup family `C`: after the completed
OS boundary transfer is known to fix the finite OS vacuum, H1-D5 is a property
of the finite Wilson vacuum and the one-slab Wilson kernel alone.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5LiteralTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5LiteralCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5LiteralSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5LiteralMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5LiteralBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5LiteralSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5LiteralSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance h1d5LiteralPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- Exact literal Wilson/Fubini formula for a normalized pair-transfer matrix
coefficient with an arbitrary source vector and a decomposable physical test.

The source need not itself be decomposable.  This is the form needed for the
finite OS vacuum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_inner_physicalPairDecomposable_eq_literalWilsonIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N x y) =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2)⁻¹ *
        ∫ q, ∫ p,
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
              H N beta (p, q))
            (f p *
              (((x :
                  Lp ℝ 2
                    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                      H N)) q.1) *
                ((y :
                  Lp ℝ 2
                    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                      H N)) q.2)))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
      H N hN beta hbeta
  let g :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
      H N x y
  have hK :
      K =ᵐ[μPair.prod μPair]
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta := by
    simpa [K, μPair] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
        H N hN beta hbeta
  have hg :
      g =ᵐ[μPair]
        fun q =>
          ((x : Lp ℝ 2 μ) q.1) *
            ((y : Lp ℝ 2 μ) q.2) := by
    simpa [
      g, μ, μPair,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2,
      realL2ExternalTensorFunction] using
      (realL2ExternalTensor_coeFn
        (μ := μ) (ν := μ)
        (x : Lp ℝ 2 μ) (y : Lp ℝ 2 μ))
  have hf :
      f =ᵐ[μPair] fun p => f p :=
    Filter.Eventually.of_forall fun _ => rfl
  have hPairing :
      realL2HilbertSchmidtKernelPairing K f g =
        ∫ q, ∫ p,
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
              H N beta (p, q))
            (f p *
              (((x : Lp ℝ 2 μ) q.1) *
                ((y : Lp ℝ 2 μ) q.2)))
          ∂μPair ∂μPair := by
    exact
      realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives
        K f g
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta)
        (fun p => f p)
        (fun q =>
          ((x : Lp ℝ 2 μ) q.1) *
            ((y : Lp ℝ 2 μ) q.2))
        hK hf hg
  change
    inner ℝ
        ((‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖ ^ 2)⁻¹ •
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta f)
        g = _
  rw [real_inner_smul_left]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner]
  simpa [K, μ, μPair, g] using
    congrArg
      (fun z =>
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ^ 2)⁻¹ * z)
      hPairing

/-- Literal pair-Haar integral formula for the matrix coefficient of an
arbitrary source against a decomposable physical pair. -/
theorem
    periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N x y) =
      ∫ q,
        inner ℝ (f q)
          (((x :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  H N)) q.1) *
            ((y :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  H N)) q.2))
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let g :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
      H N x y
  have hg :
      g =ᵐ[μPair]
        fun q =>
          ((x : Lp ℝ 2 μ) q.1) *
            ((y : Lp ℝ 2 μ) q.2) := by
    simpa [
      g, μ, μPair,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2,
      realL2ExternalTensorFunction] using
      (realL2ExternalTensor_coeFn
        (μ := μ) (ν := μ)
        (x : Lp ℝ 2 μ) (y : Lp ℝ 2 μ))
  change inner ℝ f g = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg] with q hq
  rw [hq]

section VacuumNormalizedH1D5LiteralWilson

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

/-- H1-D5 is exactly one finite Wilson-kernel/Fubini identity at every scale
and against every decomposable Gauss-law physical test pair.

The right side contains no completed transfer and no semigroup-family data.
Thus, after the completed OS boundary transfer has been shown to fix the finite
OS vacuum, the remaining seam is a literal finite Wilson model identity. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_literalWilsonIntegral :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        ∀ x y :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N,
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)‖ ^ 2)⁻¹ *
              ∫ q, ∫ p,
                inner ℝ
                  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                    (halfExtent n) N (beta n) (p, q))
                  ((physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
                      (S := S) (D := D) (halfExtent := halfExtent)
                      (N := N) (hN := hN)
                      (beta := beta) (hbeta := hbeta)
                      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n) p *
                    (((x :
                        Lp ℝ 2
                          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                            (halfExtent n) N)) q.1) *
                      ((y :
                        Lp ℝ 2
                          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                            (halfExtent n) N)) q.2)))
                ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                  (halfExtent n) N)
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                (halfExtent n) N) =
            ∫ q,
              inner ℝ
                (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
                  (S := S) (D := D) (halfExtent := halfExtent)
                  (N := N) (hN := hN)
                  (beta := beta) (hbeta := hbeta)
                  (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n q)
                (((x :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        (halfExtent n) N)) q.1) *
                  ((y :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        (halfExtent n) N)) q.2))
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                (halfExtent n) N) := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_normalizedTransfer_pairing_fixed
      Q hInvariant C]
  constructor
  · intro h n x y
    have hxy := h n x y
    rw [
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_inner_physicalPairDecomposable_eq_literalWilsonIntegral,
      periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral
    ] at hxy
    exact hxy
  · intro h n x y
    have hxy := h n x y
    rw [
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_inner_physicalPairDecomposable_eq_literalWilsonIntegral,
      periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral
    ]
    exact hxy

/-- Audit-visible package recording the literal finite-Wilson form of H1-D5. -/
structure PhysicalYangMillsVacuumNormalizedH1D5LiteralWilsonIntegralPackage : Prop where
  completedIffLiteralWilsonIntegral :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        ∀ x y :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N,
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)‖ ^ 2)⁻¹ *
              ∫ q, ∫ p,
                inner ℝ
                  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                    (halfExtent n) N (beta n) (p, q))
                  ((physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
                      (S := S) (D := D) (halfExtent := halfExtent)
                      (N := N) (hN := hN)
                      (beta := beta) (hbeta := hbeta)
                      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n) p *
                    (((x :
                        Lp ℝ 2
                          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                            (halfExtent n) N)) q.1) *
                      ((y :
                        Lp ℝ 2
                          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                            (halfExtent n) N)) q.2)))
                ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                  (halfExtent n) N)
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                (halfExtent n) N) =
            ∫ q,
              inner ℝ
                (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
                  (S := S) (D := D) (halfExtent := halfExtent)
                  (N := N) (hN := hN)
                  (beta := beta) (hbeta := hbeta)
                  (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n q)
                (((x :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        (halfExtent n) N)) q.1) *
                  ((y :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        (halfExtent n) N)) q.2))
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                (halfExtent n) N)

theorem physicalYangMillsVacuumNormalizedH1D5LiteralWilsonIntegralPackage :
    PhysicalYangMillsVacuumNormalizedH1D5LiteralWilsonIntegralPackage
      (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { completedIffLiteralWilsonIntegral :=
      physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_literalWilsonIntegral
        Q hInvariant C }

end VacuumNormalizedH1D5LiteralWilson

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeFeatureAnalysisIndependence
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonEnergySUNTwoModeContinuousBoundaryRepresentative
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSeparableKernelOperator
import Mathlib.Tactic

/-!
# H1-D5 reduced to kernel triviality on the concrete two-mode span

#5044 identifies the literal H1-D5 two-mode determinant with the Gram
determinant of the two one-slab physical feature-analysis images.

This file closes the kinematic input side.  The source SU(N) Wilson two-mode
family is orthonormal.  Its canonical primary-plaquette boundary pullback is a
linear isometry, and the boundary-to-spatial-pair isometry identifies those
boundary modes with

  `f_k ⊠ 1`

where `f_k` is the physical one-slice mode and the companion constant-one
physical vector has norm one.  The exact external-tensor inner-product identity
therefore shows that the one-slice family `f_0,f_1` is itself orthonormal.

Consequently #5044's feature-image independence follows from the sole finite
model statement that the physical one-slab feature-analysis operator has
trivial kernel on the explicit two-dimensional span of `f_0,f_1`.

No continuum, OS-completion, spectral, or top-vector assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5TwoModeKernelTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5TwoModeKernelCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5TwoModeKernelSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5TwoModeKernelMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5TwoModeKernelBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5TwoModeKernelSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5TwoModeKernelSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The canonical boundary-Haar realization of the arbitrary-rank Wilson
two-mode family remains orthonormal. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_orthonormal
    (H N : ℕ)
    (hN2 : 2 ≤ N) :
    Orthonormal ℝ
      (fun k : Fin 2 =>
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
          H hN2 k) := by
  simpa only [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2,
    Function.comp_apply] using
    (periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback_orthonormal
      H N
      (specialUnitaryWilsonHaarTwoMode hN2)
      (specialUnitaryWilsonHaarTwoMode_orthonormal hN2))

/-- The explicit one-slice physical Wilson two-mode family is orthonormal.

The proof transports the already-orthonormal boundary family through the exact
boundary-to-pair isometry and then cancels the unit constant companion factor
using `realL2ExternalTensor_inner`. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_orthonormal
    (H N : ℕ)
    (hN2 : 2 ≤ N) :
    Orthonormal ℝ
      (fun k : Fin 2 =>
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 k) := by
  rw [orthonormal_iff_ite]
  intro i j
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let J :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
  let b := fun k : Fin 2 =>
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
      H hN2 k
  let f := fun k : Fin 2 =>
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2 H hN2 k
  let one :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  have hb : Orthonormal ℝ b := by
    simpa only [b] using
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_orthonormal
        H N hN2
  have hbInner :
      inner ℝ (b i) (b j) = if i = j then 1 else 0 :=
    (orthonormal_iff_ite.mp hb) i j
  have hJinner := J.inner_map_map (b i) (b j)
  have hJi :
      J (b i) =
        periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N (f i) one := by
    simpa only [J, b, f, one] using
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_to_pair_eq_physicalDecomposable
        H hN2 i
  have hJj :
      J (b j) =
        periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N (f j) one := by
    simpa only [J, b, f, one] using
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_to_pair_eq_physicalDecomposable
        H hN2 j
  rw [hJi, hJj] at hJinner
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 at hJinner
  rw [realL2ExternalTensor_inner] at hJinner
  have honeInner :
      inner ℝ
          (one :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          (one :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    change ‖one‖ ^ 2 = 1
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm]
    norm_num
  rw [honeInner, mul_one] at hJinner
  change
    inner ℝ
        (f i :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
        (f j :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      if i = j then 1 else 0
  exact hJinner.trans hbInner

/-- In particular the physical one-slice two-mode family is linearly
independent before applying the one-slab feature analysis. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_linearIndependent
    (H N : ℕ)
    (hN2 : 2 ≤ N) :
    LinearIndependent ℝ
      (fun k : Fin 2 =>
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 k) :=
  (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_orthonormal
    H N hN2).linearIndependent

/-- The concrete two-dimensional physical input span used by the H1-D5
two-mode test. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalSpan
    (H N : ℕ)
    (hN2 : 2 ≤ N) :
    Submodule ℝ
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  Submodule.span ℝ
    (Set.range
      (fun k : Fin 2 =>
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 k))

/-- Triviality of the physical one-slab feature-analysis kernel on the explicit
two-mode span implies linear independence of the two feature images. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage_linearIndependent_of_kernel_trivial_on_span
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hKernel :
      ∀ x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
        x ∈
            periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalSpan
              H N hN2 →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
              H N hN beta hbeta x = 0 →
            x = 0) :
    LinearIndependent ℝ
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
        H N hN hN2 beta hbeta) := by
  let f := fun k : Fin 2 =>
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2 H hN2 k
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
  let M :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalSpan H N hN2
  have hf : LinearIndependent ℝ f := by
    simpa only [f] using
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_linearIndependent
        H N hN2
  have hInj : Set.InjOn A.toLinearMap M := by
    intro x hx y hy hxy
    have hsubMem : x - y ∈ M := M.sub_mem hx hy
    have hsubZero : A (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hzero : x - y = 0 := by
      exact hKernel (x - y) (by simpa only [M] using hsubMem) (by
        simpa only [A] using hsubZero)
    exact sub_eq_zero.mp hzero
  have hMapped := hf.map_injOn A.toLinearMap hInj
  simpa only [
    f, A, Function.comp_apply,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
  ] using hMapped

section H1D5TwoModeKernelResidual

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- Kernel triviality of the one-slab physical feature analysis on the explicit
two-mode span at one finite scale refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_twoModeFeatureAnalysis_kernel_trivial_on_span
    (n : ℕ)
    (hKernel :
      ∀ x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N,
        x ∈
            periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalSpan
              (halfExtent n) N hN2 →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
              (halfExtent n) N hN (beta n) (hbeta n) x = 0 →
            x = 0) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  apply
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_twoModePhysicalFeatureAnalysis_linearIndependent
      (hN2 := hN2) Q hInvariant C n
  exact
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage_linearIndependent_of_kernel_trivial_on_span
      (halfExtent n) N hN hN2 (beta n) (hbeta n) hKernel

/-- Audit-visible final finite-dimensional kernel residual. -/
structure PhysicalYangMillsVacuumNormalizedH1D5TwoModeFeatureKernelResidualPackage : Prop where
  physicalTwoModeOrthonormal :
    ∀ n : ℕ,
      Orthonormal ℝ
        (fun k : Fin 2 =>
          periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
            (halfExtent n) hN2 k)
  kernelTrivialityObstructs :
    ∀ n : ℕ,
      (∀ x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N,
        x ∈
            periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalSpan
              (halfExtent n) N hN2 →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
              (halfExtent n) N hN (beta n) (hbeta n) x = 0 →
            x = 0) →
        ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C

theorem physicalYangMillsVacuumNormalizedH1D5TwoModeFeatureKernelResidualPackage :
    PhysicalYangMillsVacuumNormalizedH1D5TwoModeFeatureKernelResidualPackage
      (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { physicalTwoModeOrthonormal := by
      intro n
      exact
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_orthonormal
          (halfExtent n) N hN2
    kernelTrivialityObstructs := by
      intro n hKernel
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_twoModeFeatureAnalysis_kernel_trivial_on_span
          (hN2 := hN2) Q hInvariant C n hKernel }

end H1D5TwoModeKernelResidual

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryOneSidedPhysicalTransfer
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelPairingFubini
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0RawSectorNormRatioV5_PZ37ALX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMO — actual original SU2 physical one-slab triple-Haar coefficient

AMN proved that the L-periodic deterministic integer configuration shift must
NOT be identified with the strict physical one-slab transfer on nontrivial
vacuum-orthogonal OS excitations. AMO now computes the other object, the true
positive Haar-averaging Wilson kernel, on genuine gauge-invariant spatial-slice
physical vectors.

For any physical Gauss-law state f and arbitrary ordered pair-Haar test z,
the matrix coefficient of the normalized one-sided physical transfer is
exactly the triple *literal* spatial-Haar integral over A (previous slice),
B (next slice), and C (companion top-mode endpoint):

  <J(physicalNormalizedOneSlab f), z> =
  ||P||^-1 * ∫ C ∫ B
    <z(B,C), (∫ A f(A) K_Wilson(A,B) dHaar(A)) * Omega(C)>
    dHaar(B) dHaar(C).

There is no completion-range/surjectivity/finite-to-continuum assumption and
no fake time translation. The kernel K is the actual Gauss-compatible one-slab
Wilson Haar kernel, not the static Gibbs covariance. The original physical
coupling beta0 = log(3/2)/64 is also instantiated explicitly.

This supplies a literal model-facing multiple-Haar-integral RHS suitable for
the next OS boundary raw-path Markov/Fubini comparison. It alone does NOT prove
the one-slab/OS intertwining, that the obstruction in AMM vanishes, or a
continuum four-dimensional Yang–Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMO_sideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance p4Q2PZ37AMO_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AMO_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AMO_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AMO_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AMO_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AMO_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AMO_sliceSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Exact literal triple-Haar representation for the genuine Gauss-invariant
normalized one-sided physical Wilson transfer against an arbitrary pair-Haar
L² test, with the truly integrated first-slab kernel.

Unlike a conditional Markov formula, this identity has no hypotheses about
the test z being decomposable, and no unproved Fubini/intertwining property:
all integrability and interchange follow from the existing actual L² kernel
Fubini theorem and actual one-slab fiber integral representation. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedPhysicalPair_oneStep_inner_eq_tripleHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedPhysicalPairLinearIsometry
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta f)) z =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
      ∫ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        ∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          inner ℝ (z (B, C))
            ((∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
                 (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N f) A *
                   periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                     H N beta A B
               ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) *
              (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
                H N hN beta hbeta) C)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let F := periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N f
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp H N hN beta hbeta
  let phi := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
    H N beta F
  have hFubini :
      realL2HilbertSchmidtKernelPairing z (T F) Omega =
        ∫ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          ∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            inner ℝ (z (B, C)) (phi B * Omega C) ∂μ ∂μ := by
    exact realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives
      (μ := μ) (ν := μ) z (T F) Omega
      (fun p => z p) phi (fun C => Omega C)
      (Filter.EventuallyEq.rfl)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
        H N hN beta hbeta F)
      (Filter.EventuallyEq.rfl)
  rw [periodicHypercubicEvenSpecialUnitaryOneSidedPhysicalPair_oneStep_inner_eq_rawKernel]
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
      realL2HilbertSchmidtKernelPairing z (T F) Omega = _
  rw [hFubini]
  rfl

private instance p4Q2PZ37AMO_su2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace GroundStatePosteriorJoint

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "hbeta0" => p4Q2PZ37ADC_fixedCoupling_pos.le

/-- The exact original beta0=log(3/2)/64 SU2 Wilson physical one-slab
one-particle matrix coefficient equals the true triple spatial-Haar integral
of the unfixed positive Wilson one-slab kernel and the unchanged physical
normalized top eigenmode. No static Gibbs covariance time identification. -/
theorem p4Q2PZ37AMO_originalFixedBeta0PhysicalOneSlab_oneStep_inner_eq_tripleHaar
    (H : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedPhysicalPairLinearIsometry
          H 2 (by norm_num) beta0 hbeta0
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta0 hbeta0 f)) z =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta0 hbeta0‖⁻¹ *
      ∫ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        ∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
          inner ℝ (z (B, C))
            ((∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
                 (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H 2 f) A *
                   periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                     H 2 beta0 A B
               ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) *
              (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
                H 2 (by norm_num) beta0 hbeta0) C)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  exact periodicHypercubicEvenSpecialUnitaryOneSidedPhysicalPair_oneStep_inner_eq_tripleHaar
    H 2 (by norm_num) beta0 hbeta0 f z

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.periodicHypercubicEvenSpecialUnitaryOneSidedPhysicalPair_oneStep_inner_eq_tripleHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMO_originalFixedBeta0PhysicalOneSlab_oneStep_inner_eq_tripleHaar

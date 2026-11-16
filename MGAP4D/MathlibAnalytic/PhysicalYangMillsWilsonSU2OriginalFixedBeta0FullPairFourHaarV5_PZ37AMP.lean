import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0PhysicalOneSlabTripleHaarV5_PZ37AMO
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2LiteralOneSidedDynamics
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelPairingFubini
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMP — genuine full two-ended physical one-slab four-Haar coefficient

AMN distinguishes finite-order deterministic periodic configuration translation
from true positive Haar-averaging physical Wilson time evolution. AMO certifies
a genuine SU2 one-ended physical one-slab TRIPLE Haar coefficient (the other
endpoint is the invariant physical top state).

Here both endpoints carry arbitrary independent physical Gauss-law states,
and both evolve under the true normalized physical one-slab Wilson transfer.
Its exact scalar coefficient against any NONDECOMPOSABLE pair-Haar test z is
the real FOUR-HAAR integral with two genuine original Wilson slab factors:

  inner((P_normalized f) tensor (P_normalized g), z)
   = norm(P)^(-2) * integral_{C} integral_{B}
       inner(z(B,C),
           (integral_A f(A) K_Wilson(A,B)) *
           (integral_D g(D) K_Wilson(D,C))).

This is derived from:
- actual literal pair-Haar one-slab transfer on decomposable *input*,
  with no restriction on the *test* z;
- exact pair-operator/external-tensor vector identity (previous Lean theorem);
- the existing real Hilbert-Schmidt Fubini lemma for arbitrary L2 tests;
- the actual bounded Wilson one-slab fiber-integral representative;
- the unchanged Gauss-law physical normalized transfer on BOTH endpoints.

No common OS-time equivalence or other gluing axiom is introduced. This RHS
is the model-facing FOUR-HAAR target of the preexisting *full pair* OS weak
intertwining predicate, not a proof of that predicate itself.

SU2 at the original fixed beta0 = log(3/2)/64 is separately specialized.
No static Gibbs covariance is equated to time transfer and no Hamiltonian or
continuum 4d Yang-Mills mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMP_sideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance p4Q2PZ37AMP_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AMP_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AMP_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AMP_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AMP_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AMP_sliceLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AMP_sliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The genuine *ambient* Wilson pair-Haar one-slab operator applied to any
decomposable input has a literal FOUR-Haar scalar matrix coefficient against
an arbitrary (possibly entangled/nondecomposable) ordered pair-Haar L2 test.

There is no factorization assumption on the test and no abstract or periodic
configuration time translation. The Wilson kernels remain literal integrands. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_eq_fourHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta (realL2ExternalTensor f g)) z =
      ∫ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        ∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          inner ℝ (z (B,C))
            ((∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
                f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N beta A B
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) *
             (∫ D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
                g D * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N beta D C
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
  rw [real_inner_comm]
  change realL2HilbertSchmidtKernelPairing z (T f) (T g) = _
  exact realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives
    (μ := μ) (ν := μ) z (T f) (T g)
    (fun p => z p)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
      H N beta f)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
      H N beta g)
    (Filter.EventuallyEq.rfl)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
      H N hN beta hbeta f)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
      H N hN beta hbeta g)

/-- For *two arbitrary* genuine Gauss-law physical modes, the physical Wilson
one-slab normalized tensor coefficient equals the literal FOUR-Haar integral.
Both modes are evolved. This is stronger than AMO's one-sided top-mode formula.

The factor norm(P)^(-2) is the exact TWO-ended physical normalization, not an
artificial transfer coefficient or a mass-gap input. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairBothOneStep_inner_eq_fourHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
          H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            H N hN beta hbeta g)) z =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹) ^ 2 *
      ∫ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        ∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          inner ℝ (z (B,C))
            ((∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
                (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N f) A *
                  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H N beta A B
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) *
             (∫ D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
                (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N g) D *
                  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H N beta D C
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let F := periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N f
  let G := periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N g
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  have hNormalize :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
            H N
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
              H N hN beta hbeta f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
              H N hN beta hbeta g)) z =
      c ^ 2 * inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta (realL2ExternalTensor F G)) z := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_eq_normalizedRaw
          H N hN beta hbeta f,
        periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_eq_normalizedRaw
          H N hN beta hbeta g]
    unfold periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
    rw [real_inner_comm]
    change realL2HilbertSchmidtKernelPairing z (c • T F) (c • T G) = _
    rw [realL2HilbertSchmidtKernelPairing_smul_left,
      realL2HilbertSchmidtKernelPairing_smul_right]
    simp only [smul_eq_mul]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor,
      real_inner_comm]
    change c * (c * realL2HilbertSchmidtKernelPairing z (T F) (T G)) =
      c ^ 2 * realL2HilbertSchmidtKernelPairing z (T F) (T G)
    ring
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
          H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            H N hN beta hbeta g)) z =
      c ^ 2 * inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta (realL2ExternalTensor F G)) z := hNormalize
    _ = _ := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_eq_fourHaar
        H N hN beta hbeta F G z]

private instance p4Q2PZ37AMP_su2Nontrivial :
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

/-- Original beta0 SU2 physical full PAIR transfer coefficient is the true
FOUR-Haar double-slab Wilson integral for every pair of Gauss-law states f,g
and arbitrary pair-Haar test z. Both factors use the original one-slab action
and physical normalization, with no static Gibbs or periodic-time surrogate. -/
theorem p4Q2PZ37AMP_originalFixedBeta0PhysicalPairBothOneStep_inner_eq_fourHaar
    (H : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
          H 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            H 2 (by norm_num) beta0 hbeta0 f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            H 2 (by norm_num) beta0 hbeta0 g)) z =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta0 hbeta0‖⁻¹) ^ 2 *
      ∫ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        ∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
          inner ℝ (z (B,C))
            ((∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
                (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H 2 f) A *
                  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H 2 beta0 A B
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) *
             (∫ D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
                (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H 2 g) D *
                  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H 2 beta0 D C
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalPairBothOneStep_inner_eq_fourHaar
    H 2 (by norm_num) beta0 hbeta0 f g z

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_eq_fourHaar
#print axioms MGAP4D.MathlibAnalytic.periodicHypercubicEvenSpecialUnitaryPhysicalPairBothOneStep_inner_eq_fourHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMP_originalFixedBeta0PhysicalPairBothOneStep_inner_eq_fourHaar

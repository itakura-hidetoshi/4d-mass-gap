import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5PathMessagePhysicalTransferCoefficient
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferSelfAdjoint
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2LiteralOneSidedDynamics
import Mathlib.Tactic

/-!
# H1-D5 as a finite physical operator-power identity

#5036 rewrites H1-D5 as a raw pair-transfer eigen-equation for the unnormalized
finite Wilson path-message vector.  #5037 identifies the matrix coefficients of
that vector with the complete positive-half physical transfer
`T_phys^(H+1)`.

This file combines the two finite-volume statements.

The raw pair transfer is self-adjoint and factorizes exactly on decomposable
physical pair tests, so the H1-D5 eigen-equation is equivalent to

`⟪P_H (T x), T y⟫ = ‖T‖² ⟪P_H x, y⟫`

for every physical `x,y`, where `P_H = T^(H+1)`.

By symmetry of `T`, this is an operator identity

`T ∘ P_H ∘ T = ‖T‖² P_H`.

Since `P_H` is a power of the same one-slab transfer, this is equivalently

`T^(H+3) = ‖T‖² T^(H+1)`.

No completed OS transfer, continuum input, or additional model hypothesis is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5PowerTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5PowerCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5PowerSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5PowerMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5PowerBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5PowerSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5PowerPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- Raw pair transfer sends a decomposable physical pair to the decomposable
pair of the two physical one-slab images. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_physicalPairDecomposableL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N x y) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta x)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta y) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor
  ]
  simp only [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe]

section PathMessageSandwich

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

/-- Moving one raw pair-transfer step from the finite Wilson path message onto a
physical decomposable test adds one physical one-slab transfer at each endpoint. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_rawPairTransfer_inner_decomposable_eq_physicalPositiveHalfSandwich
    (n : ℕ)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)
          (physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
            Q hInvariant n))
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          (halfExtent n) N x y) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n) x))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) y) := by
  let H := halfExtent n
  let Tpair :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN (beta n) (hbeta n)
  let msg :=
    physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
      Q hInvariant n
  let test :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 H N x y
  have hsymm :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_isSymmetric
      H N hN (beta n) (hbeta n)
  calc
    inner ℝ (Tpair msg) test =
        inner ℝ msg (Tpair test) := hsymm msg test
    _ =
        inner ℝ msg
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN (beta n) (hbeta n) x)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN (beta n) (hbeta n) y)) := by
          rw [
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_physicalPairDecomposableL2
          ]
    _ =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN (beta n) (hbeta n) x))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN (beta n) (hbeta n) y) := by
          exact
            physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_inner_decomposable_eq_physicalPositiveHalfTransfer
              Q hInvariant n
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN (beta n) (hbeta n) x)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN (beta n) (hbeta n) y)

end PathMessageSandwich

section H1D5SandwichCriterion

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

/-- H1-D5 is equivalent to the finite physical sandwich identity obtained by
adding one physical one-slab transfer at each endpoint of the positive-half
transfer coefficient. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_physicalPositiveHalfSandwich :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        ∀ x y :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N,
          inner ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
                (halfExtent n) N hN (beta n) (hbeta n)
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                  (halfExtent n) N hN (beta n) (hbeta n) x))
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                (halfExtent n) N hN (beta n) (hbeta n) y) =
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                (halfExtent n) N hN (beta n) (hbeta n)‖ ^ 2) *
              inner ℝ
                (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
                  (halfExtent n) N hN (beta n) (hbeta n) x)
                y := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_unfixedPathKernelMomentPairL2_rawEigen
      Q hInvariant C]
  constructor
  · intro h n x y
    let H := halfExtent n
    let msg :=
      physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
        Q hInvariant n
    let test :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 H N x y
    let c : ℝ :=
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN (beta n) (hbeta n)‖ ^ 2
    calc
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN (beta n) (hbeta n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN (beta n) (hbeta n) x))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN (beta n) (hbeta n) y) =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN (beta n) (hbeta n) msg)
          test := by
            symm
            simpa [H, msg, test] using
              physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_rawPairTransfer_inner_decomposable_eq_physicalPositiveHalfSandwich
                Q hInvariant n x y
      _ = inner ℝ (c • msg) test := by rw [h n]
      _ = c * inner ℝ msg test := by rw [real_inner_smul_left]
      _ = c *
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN (beta n) (hbeta n) x)
            y := by
              rw [
                physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_inner_decomposable_eq_physicalPositiveHalfTransfer
                  Q hInvariant n x y
              ]
  · intro h n
    let H := halfExtent n
    let msg :=
      physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2
        Q hInvariant n
    let Tpair :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN (beta n) (hbeta n)
    let S2 :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN (beta n) (hbeta n)
    let c : ℝ :=
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN (beta n) (hbeta n)‖ ^ 2
    have hc : c ≠ 0 := by
      exact pow_ne_zero 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
          H N hN (beta n) (hbeta n)).ne'
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
    have hraw :
        Tpair msg = c • S2 msg := by
      change
        Tpair msg =
          c • (c⁻¹ • Tpair msg)
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hrawMem :
        Tpair msg ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
      rw [hraw]
      exact
        Submodule.smul_mem
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N)
          c hSmsg
    have hrhsMem :
        c • msg ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N :=
      Submodule.smul_mem
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N)
        c hmsg
    apply
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_of_inner_decomposable_eq
        H N hrawMem hrhsMem
    intro x y
    let test :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 H N x y
    calc
      inner ℝ (Tpair msg) test =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN (beta n) (hbeta n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN (beta n) (hbeta n) x))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN (beta n) (hbeta n) y) := by
              simpa [Tpair, msg, test, H] using
                physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_rawPairTransfer_inner_decomposable_eq_physicalPositiveHalfSandwich
                  Q hInvariant n x y
      _ = c *
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN (beta n) (hbeta n) x)
            y := by
              dsimp only [c, H]
              exact h n x y
      _ = c * inner ℝ msg test := by
              rw [
                physicalYangMillsVacuumNormalizedSUNTwoModeUnfixedPathKernelMomentPairL2_inner_decomposable_eq_physicalPositiveHalfTransfer
                  Q hInvariant n x y
              ]
      _ = inner ℝ (c • msg) test := by
              symm
              rw [real_inner_smul_left]

end H1D5SandwichCriterion

/-- For a single physical one-slab transfer `T`, sandwiching its `m`-th
power between one additional `T` on each side is exactly `T^(m+2)`. -/
theorem physicalOneSlabTransfer_comp_pow_comp_self_eq_pow_add_two
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (m : ℕ) :
    T.comp ((T ^ m).comp T) = T ^ (m + 2) := by
  apply ContinuousLinearMap.ext
  intro x
  change T ((T ^ m) (T x)) = (T ^ (m + 2)) x
  calc
    T ((T ^ m) (T x)) =
        (T ^ Nat.succ m) (T x) := by
          rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    _ = (T ^ Nat.succ (Nat.succ m)) x := by
          simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] using
            congrArg
              (fun A : E →L[ℝ] E => A x)
              (pow_succ T (Nat.succ m)).symm
    _ = (T ^ (m + 2)) x := by
          rfl

section H1D5OperatorPower

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

/-- Operator version of the finite H1-D5 sandwich criterion. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_physicalPositiveHalfSandwichOperator :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        let T :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)
        let P :=
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)
        T.comp (P.comp T) = (‖T‖ ^ 2) • P := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_physicalPositiveHalfSandwich
      Q hInvariant C]
  constructor
  · intro h n
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
    have hT :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
        (halfExtent n) N hN (beta n) (hbeta n)
    dsimp only
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℝ
    intro y
    change inner ℝ (T (P (T x))) y = inner ℝ (((‖T‖ ^ 2) • P) x) y
    calc
      inner ℝ (T (P (T x))) y =
          inner ℝ (P (T x)) (T y) := hT (P (T x)) y
      _ = (‖T‖ ^ 2) * inner ℝ (P x) y := by
          simpa [T, P] using h n x y
      _ = inner ℝ (((‖T‖ ^ 2) • P) x) y := by
          rw [smul_apply]
          exact
            (real_inner_smul_left (P x) y (‖T‖ ^ 2)).symm
  · intro h n x y
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
    have hT :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
        (halfExtent n) N hN (beta n) (hbeta n)
    have hop := h n
    change T.comp (P.comp T) = (‖T‖ ^ 2) • P at hop
    calc
      inner ℝ (P (T x)) (T y) =
          inner ℝ (T (P (T x))) y := (hT (P (T x)) y).symm
      _ = inner ℝ (((‖T‖ ^ 2) • P) x) y := by
          rw [show T (P (T x)) = ((T.comp (P.comp T)) x) by rfl, hop]
      _ = (‖T‖ ^ 2) * inner ℝ (P x) y := by
          rw [smul_apply]
          exact
            real_inner_smul_left (P x) y (‖T‖ ^ 2)

/-- Final finite-volume normal form of H1-D5: the physical one-slab transfer
must satisfy a two-step polynomial identity relative to the positive-half
length. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_physicalOneSlabPowerIdentity :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        let T :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)
        T ^ (periodicHypercubicEvenPositiveHalfCylinderSlabCount (halfExtent n) + 2) =
          (‖T‖ ^ 2) •
            (T ^ periodicHypercubicEvenPositiveHalfCylinderSlabCount (halfExtent n)) := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_physicalPositiveHalfSandwichOperator
      Q hInvariant C]
  constructor
  · intro h n
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
    let m := periodicHypercubicEvenPositiveHalfCylinderSlabCount (halfExtent n)
    have hn := h n
    change
      T.comp
          ((T ^ m).comp T) =
        (‖T‖ ^ 2) • (T ^ m) at hn
    rw [physicalOneSlabTransfer_comp_pow_comp_self_eq_pow_add_two T m] at hn
    exact hn
  · intro h n
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
    let m := periodicHypercubicEvenPositiveHalfCylinderSlabCount (halfExtent n)
    have hn := h n
    change T ^ (m + 2) = (‖T‖ ^ 2) • (T ^ m) at hn
    change
      T.comp
          ((T ^ m).comp T) =
        (‖T‖ ^ 2) • (T ^ m)
    rw [physicalOneSlabTransfer_comp_pow_comp_self_eq_pow_add_two T m]
    exact hn

/-- With the explicit positive-half slab count `H+1`, the H1-D5 power identity
is `T^(H+3) = ‖T‖² T^(H+1)`. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_physicalOneSlabPowerIdentity_explicit :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        let H := halfExtent n
        let T :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN (beta n) (hbeta n)
        T ^ (H + 3) = (‖T‖ ^ 2) • (T ^ (H + 1)) := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_physicalOneSlabPowerIdentity
      Q hInvariant C]
  constructor
  · intro h n
    simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount, Nat.add_assoc] using h n
  · intro h n
    simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount, Nat.add_assoc] using h n

end H1D5OperatorPower

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

section PhysicalOneSlab

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta

/-- Sum of the squared local defects associated with a finite family of
bounded-color operators.  The number of colors is kept explicit so that the
later scaling statement can require one fixed `q`, rather than the number of
sites in the spatial slice. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet
    (q : ℕ) (P : Fin q → G →L[ℝ] G) (phi : G) : ℝ :=
  ∑ c, ‖phi - P c phi‖ ^ 2

/-- The color-averaged local Dirichlet form.  Its denominator is the bounded
color count, not the volume. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryBoundedColorAverageDirichlet
    (q : ℕ) (P : Fin q → G →L[ℝ] G) (phi : G) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet
      H N q P phi / (q : ℝ)

/-- A vector is fixed by every local color operator. -/
def periodicHypercubicEvenSpecialUnitaryIsCommonColorFixed
    (q : ℕ) (P : Fin q → G →L[ℝ] G) (psi : G) : Prop :=
  ∀ c, P c psi = psi

/-- The bounded-color Dirichlet form is nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet_nonneg
    (q : ℕ) (P : Fin q → G →L[ℝ] G) (phi : G) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet H N q P phi := by
  unfold periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Common fixed vectors have zero local color defect. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet_eq_zero_of_commonFixed
    (q : ℕ) (P : Fin q → G →L[ℝ] G) (psi : G)
    (hfix : periodicHypercubicEvenSpecialUnitaryIsCommonColorFixed H N q P psi) :
    periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet H N q P psi = 0 := by
  unfold periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet
  simp [periodicHypercubicEvenSpecialUnitaryIsCommonColorFixed] at hfix
  simp [hfix]

/-- Audit-visible single-volume certificate for the local-to-global step.

The operators are required to be symmetric idempotents, so they really encode
orthogonal conditional/block projections.  `commonFixed_eq_physicalFixed`
keeps the full fixed space of the normalized physical transfer; no
one-dimensional-vacuum assumption is made.

The two genuinely model-side obligations are separated:
* `localCoercivity`: the sum of local color defects controls the full
  top-orthogonal norm with constant `kappa`;
* `rawComparison`: the actual Wilson one-slab raw defect controls the averaged
  local Dirichlet form with constant `eta`.

The resulting coefficient is `eta * kappa / q`. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBoundedColorCoercivityCertificate :
    Type where
  q : ℕ
  q_pos : 0 < q
  colorOperator : Fin q → G →L[ℝ] G
  colorIdempotent :
    ∀ c phi, colorOperator c (colorOperator c phi) = colorOperator c phi
  colorSymmetric :
    ∀ c, (colorOperator c : G →ₗ[ℝ] G).IsSymmetric
  kappa : ℝ
  eta : ℝ
  kappa_pos : 0 < kappa
  eta_pos : 0 < eta
  coefficient_le_one : eta * kappa / (q : ℝ) ≤ 1
  commonFixed_eq_physicalFixed :
    ∀ psi : G,
      periodicHypercubicEvenSpecialUnitaryIsCommonColorFixed
          H N q colorOperator psi ↔ S psi = psi
  localCoercivity :
    ∀ x : K,
      kappa * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet
          H N q colorOperator (x : G)
  rawComparison :
    ∀ x : K,
      eta * ‖T‖ ^ 2 *
          periodicHypercubicEvenSpecialUnitaryBoundedColorAverageDirichlet
            H N q colorOperator (x : G) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x

/-- The coefficient supplied by a bounded-color certificate is strictly
positive because the color count is finite and nonzero and both local
constants are strictly positive. -/
theorem PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBoundedColorCoercivityCertificate.coefficient_pos
    (C : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBoundedColorCoercivityCertificate
      H N hN beta hbeta) :
    0 < C.eta * C.kappa / (C.q : ℝ) := by
  have hq : 0 < (C.q : ℝ) := by exact_mod_cast C.q_pos
  exact div_pos (mul_pos C.eta_pos C.kappa_pos) hq

/-- Bounded-color local coercivity plus the physical comparison inequality
produces the exact raw one-slab squared-defect estimate required by the
canonical defect/gap bridge.

The only denominator is `q`, the color count.  In particular no factor equal
to the number of sites or edges is introduced by this reduction. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_of_boundedColorCoercivity
    (C : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBoundedColorCoercivityCertificate
      H N hN beta hbeta)
    (x : K) :
    (C.eta * C.kappa / (C.q : ℝ)) * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
        H N hN beta hbeta x := by
  have hq : 0 < (C.q : ℝ) := by exact_mod_cast C.q_pos
  have hdiv :
      (C.kappa * ‖(x : G)‖ ^ 2) / (C.q : ℝ) ≤
        periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet
          H N C.q C.colorOperator (x : G) / (C.q : ℝ) :=
    (div_le_div_iff_of_pos_right hq).2 (C.localCoercivity x)
  have hscale : 0 ≤ C.eta * ‖T‖ ^ 2 :=
    mul_nonneg C.eta_pos.le (sq_nonneg ‖T‖)
  have hmul := mul_le_mul_of_nonneg_left hdiv hscale
  calc
    (C.eta * C.kappa / (C.q : ℝ)) * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 =
        (C.eta * ‖T‖ ^ 2) *
          ((C.kappa * ‖(x : G)‖ ^ 2) / (C.q : ℝ)) := by ring
    _ ≤ (C.eta * ‖T‖ ^ 2) *
          (periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet
            H N C.q C.colorOperator (x : G) / (C.q : ℝ)) := hmul
    _ = C.eta * ‖T‖ ^ 2 *
          periodicHypercubicEvenSpecialUnitaryBoundedColorAverageDirichlet
            H N C.q C.colorOperator (x : G) := by
      rfl
    _ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x := C.rawComparison x

/-- A single bounded-color certificate gives an explicit lower bound
`eta*kappa/(2*q)` on the canonical finite-volume physical transfer gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_transferGap_lower_bound_of_boundedColorCoercivity
    (C : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBoundedColorCoercivityCertificate
      H N hN beta hbeta) :
    (C.eta * C.kappa / (C.q : ℝ)) / 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_lower_bound_implies_transferGap
    H N hN beta hbeta
    (C.eta * C.kappa / (C.q : ℝ))
    C.coefficient_pos.le C.coefficient_le_one
    (fun x => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_of_boundedColorCoercivity
      H N hN beta hbeta C x)

end PhysicalOneSlab

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- Scale-uniform bounded-color certificate.

Crucially, `q`, `kappa`, and `eta` are fields of the family certificate rather
than functions of the scale.  Hence this package expresses exactly the
volume-independent local mechanism needed to avoid the `1 / volume` loss of a
sitewise average. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleBoundedColorCoercivityCertificate :
    Type where
  q : ℕ
  q_pos : 0 < q
  kappa : ℝ
  eta : ℝ
  kappa_pos : 0 < kappa
  eta_pos : 0 < eta
  coefficient_le_one : eta * kappa / (q : ℝ) ≤ 1
  colorOperator :
    ∀ n,
      Fin q →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N
  colorIdempotent :
    ∀ n c phi,
      colorOperator n c (colorOperator n c phi) = colorOperator n c phi
  colorSymmetric :
    ∀ n c,
      (colorOperator n c :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N →ₗ[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N).IsSymmetric
  commonFixed_eq_physicalFixed :
    ∀ n psi,
      periodicHypercubicEvenSpecialUnitaryIsCommonColorFixed
          (halfExtent n) N q (colorOperator n) psi ↔
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) psi = psi
  localCoercivity :
    ∀ n
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)),
      kappa *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryBoundedColorDirichlet
          (halfExtent n) N q (colorOperator n) x
  rawComparison :
    ∀ n
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)),
      eta *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)‖ ^ 2 *
          periodicHypercubicEvenSpecialUnitaryBoundedColorAverageDirichlet
            (halfExtent n) N q (colorOperator n) x ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          (halfExtent n) N hN (beta n) (hbeta n) x

/-- Restrict a scale-uniform bounded-color certificate to one finite scale. -/
noncomputable def PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleBoundedColorCoercivityCertificate.atScale
    (C : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleBoundedColorCoercivityCertificate
      halfExtent N hN beta hbeta)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBoundedColorCoercivityCertificate
      (halfExtent n) N hN (beta n) (hbeta n) :=
  { q := C.q
    q_pos := C.q_pos
    colorOperator := C.colorOperator n
    colorIdempotent := C.colorIdempotent n
    colorSymmetric := C.colorSymmetric n
    kappa := C.kappa
    eta := C.eta
    kappa_pos := C.kappa_pos
    eta_pos := C.eta_pos
    coefficient_le_one := C.coefficient_le_one
    commonFixed_eq_physicalFixed := C.commonFixed_eq_physicalFixed n
    localCoercivity := C.localCoercivity n
    rawComparison := C.rawComparison n }

/-- A scale-uniform bounded-color certificate supplies the canonical uniform raw
squared-defect certificate with coefficient `eta*kappa/q`. -/
theorem periodicHypercubicEvenSpecialUnitary_scaleBoundedColorCoercivity_implies_uniformRawDefect
    (C : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleBoundedColorCoercivityCertificate
      halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
      halfExtent N hN beta hbeta := by
  let delta : ℝ := C.eta * C.kappa / (C.q : ℝ)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    have hq : 0 < (C.q : ℝ) := by exact_mod_cast C.q_pos
    exact div_pos (mul_pos C.eta_pos C.kappa_pos) hq
  refine ⟨delta, hdelta_pos, ?_, ?_⟩
  · simpa [delta] using C.coefficient_le_one
  · intro n x
    dsimp [delta]
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_of_boundedColorCoercivity
      (halfExtent n) N hN (beta n) (hbeta n) (C.atScale n) x

/-- Main bounded-color endpoint: one fixed finite color count together with
scale-independent local coercivity and physical-comparison constants gives a
uniform positive physical transfer gap. -/
theorem periodicHypercubicEvenSpecialUnitary_scaleBoundedColorCoercivity_implies_uniformTransferGap
    (C : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleBoundedColorCoercivityCertificate
      halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  apply periodicHypercubicEvenSpecialUnitary_uniformRawDefect_implies_uniformTransferGap
    halfExtent N hN beta hbeta
  exact periodicHypercubicEvenSpecialUnitary_scaleBoundedColorCoercivity_implies_uniformRawDefect
    halfExtent N hN beta hbeta C

/-- Explicit witness version of the previous endpoint: the scale-independent
transfer-gap lower bound can be chosen to be `eta*kappa/(2*q)`. -/
theorem periodicHypercubicEvenSpecialUnitary_scaleBoundedColorCoercivity_explicit_transferGap
    (C : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleBoundedColorCoercivityCertificate
      halfExtent N hN beta hbeta) :
    0 < (C.eta * C.kappa / (C.q : ℝ)) / 2 ∧
      ∀ n,
        (C.eta * C.kappa / (C.q : ℝ)) / 2 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
            (halfExtent n) N hN (beta n) (hbeta n) := by
  constructor
  · have hq : 0 < (C.q : ℝ) := by exact_mod_cast C.q_pos
    positivity
  · intro n
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_transferGap_lower_bound_of_boundedColorCoercivity
      (halfExtent n) N hN (beta n) (hbeta n) (C.atScale n)

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D

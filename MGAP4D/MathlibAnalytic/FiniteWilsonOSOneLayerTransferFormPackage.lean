import MGAP4D.MathlibAnalytic.FiniteWilsonOSReflectionPositivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- The geometric one-time-layer Wilson OS transfer form determined directly by
the reflected Wilson kernel.  This is bilinear data before quotient completion
or construction of a bundled transfer operator. -/
def FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (F G : R.PositiveConfiguration → ℝ) : ℝ :=
  ∑ x : R.PositiveConfiguration,
    ∑ y : R.PositiveConfiguration, F x * R.kernel x y * G y

/-- The quadratic one-layer transfer form is exactly the existing Wilson
reflection form. -/
@[simp] theorem
    FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm_self
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (F : R.PositiveConfiguration → ℝ) :
    R.wilsonOneLayerTransferForm F F = R.wilsonReflectionForm F :=
  rfl

/-- The concrete Wilson reflection kernel is symmetric because its supplied
Gram kernel is symmetric and agrees pointwise through the certificate's
configuration equivalence. -/
theorem finite_lattice_wilson_os_reflection_kernel_symmetric
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (x y : R.PositiveConfiguration) :
    R.kernel x y = R.kernel y x := by
  rw [← R.gram_kernel_agrees x y,
    ← R.gram_kernel_agrees y x]
  exact finite_os_reflection_kernel_symmetric R.gram
    (R.positiveConfigurationEquiv x)
    (R.positiveConfigurationEquiv y)

/-- The geometric Wilson one-layer OS transfer form is symmetric. -/
theorem finite_lattice_wilson_os_oneLayerTransferForm_symmetric
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (F G : R.PositiveConfiguration → ℝ) :
    R.wilsonOneLayerTransferForm F G =
      R.wilsonOneLayerTransferForm G F := by
  classical
  unfold FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm
  calc
    (∑ x : R.PositiveConfiguration,
      ∑ y : R.PositiveConfiguration, F x * R.kernel x y * G y) =
      ∑ y : R.PositiveConfiguration,
        ∑ x : R.PositiveConfiguration, F x * R.kernel x y * G y := by
          rw [Finset.sum_comm]
    _ = ∑ y : R.PositiveConfiguration,
        ∑ x : R.PositiveConfiguration, G y * R.kernel y x * F x := by
          apply Finset.sum_congr rfl
          intro y _hy
          apply Finset.sum_congr rfl
          intro x _hx
          rw [finite_lattice_wilson_os_reflection_kernel_symmetric R x y]
          ring
    _ = ∑ x : R.PositiveConfiguration,
        ∑ y : R.PositiveConfiguration, G x * R.kernel x y * F y := by
          rfl

/-- Additivity in the left observable. -/
theorem finite_lattice_wilson_os_oneLayerTransferForm_add_left
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (F₁ F₂ G : R.PositiveConfiguration → ℝ) :
    R.wilsonOneLayerTransferForm (F₁ + F₂) G =
      R.wilsonOneLayerTransferForm F₁ G +
        R.wilsonOneLayerTransferForm F₂ G := by
  classical
  unfold FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Additivity in the right observable. -/
theorem finite_lattice_wilson_os_oneLayerTransferForm_add_right
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (F G₁ G₂ : R.PositiveConfiguration → ℝ) :
    R.wilsonOneLayerTransferForm F (G₁ + G₂) =
      R.wilsonOneLayerTransferForm F G₁ +
        R.wilsonOneLayerTransferForm F G₂ := by
  classical
  unfold FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Real homogeneity in the left observable. -/
theorem finite_lattice_wilson_os_oneLayerTransferForm_smul_left
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (r : ℝ)
    (F G : R.PositiveConfiguration → ℝ) :
    R.wilsonOneLayerTransferForm (r • F) G =
      r * R.wilsonOneLayerTransferForm F G := by
  classical
  unfold FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  ring

/-- Real homogeneity in the right observable. -/
theorem finite_lattice_wilson_os_oneLayerTransferForm_smul_right
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (r : ℝ)
    (F G : R.PositiveConfiguration → ℝ) :
    R.wilsonOneLayerTransferForm F (r • G) =
      r * R.wilsonOneLayerTransferForm F G := by
  classical
  rw [finite_lattice_wilson_os_oneLayerTransferForm_symmetric]
  rw [finite_lattice_wilson_os_oneLayerTransferForm_smul_left]
  rw [finite_lattice_wilson_os_oneLayerTransferForm_symmetric]

/-- The actual geometric Wilson one-layer OS transfer form is nonnegative on
the diagonal once the crossing-plane Gram bridge is supplied. -/
theorem finite_lattice_wilson_os_oneLayerTransferForm_nonneg
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (B : FiniteLatticeWilsonOSGramBridge R)
    (F : R.PositiveConfiguration → ℝ) :
    0 ≤ R.wilsonOneLayerTransferForm F F := by
  rw [R.wilsonOneLayerTransferForm_self]
  exact finite_lattice_wilson_os_reflection_positive R B F

/-- Matrix-element defect between the geometric Wilson one-layer OS form and a
candidate bounded operator acting on an independently supplied Hilbert carrier.
The observable embedding is explicit, so neither carrier equality nor density
is hidden. -/
noncomputable def finiteWilsonOSOneLayerOperatorMatrixDefect
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (observableEmbedding :
      (R.PositiveConfiguration → ℝ) →ₗ[ℝ] K)
    (candidate : K →L[ℝ] K)
    (F G : R.PositiveConfiguration → ℝ) : ℝ :=
  R.wilsonOneLayerTransferForm F G -
    inner ℝ (candidate (observableEmbedding F)) (observableEmbedding G)

/-- Vanishing of one matrix-element defect is exactly reproduction of the
geometric Wilson transfer form on that observable pair. -/
theorem finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (observableEmbedding :
      (R.PositiveConfiguration → ℝ) →ₗ[ℝ] K)
    (candidate : K →L[ℝ] K)
    (F G : R.PositiveConfiguration → ℝ) :
    finiteWilsonOSOneLayerOperatorMatrixDefect
        R observableEmbedding candidate F G = 0 ↔
      inner ℝ (candidate (observableEmbedding F)) (observableEmbedding G) =
        R.wilsonOneLayerTransferForm F G := by
  unfold finiteWilsonOSOneLayerOperatorMatrixDefect
  rw [sub_eq_zero]
  exact eq_comm

/-- Exact reproduction of every geometric Wilson matrix element forces the
candidate to be symmetric on the embedded observable range. -/
theorem finiteWilsonOSOneLayerOperator_symmetric_on_range_of_matrixDefect_eq_zero
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (observableEmbedding :
      (R.PositiveConfiguration → ℝ) →ₗ[ℝ] K)
    (candidate : K →L[ℝ] K)
    (hD : ∀ F G : R.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        R observableEmbedding candidate F G = 0)
    (F G : R.PositiveConfiguration → ℝ) :
    inner ℝ (candidate (observableEmbedding F)) (observableEmbedding G) =
      inner ℝ (observableEmbedding F) (candidate (observableEmbedding G)) := by
  have hFG :=
    (finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
      R observableEmbedding candidate F G).mp (hD F G)
  have hGF :=
    (finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
      R observableEmbedding candidate G F).mp (hD G F)
  rw [hFG, real_inner_comm, hGF]
  exact finite_lattice_wilson_os_oneLayerTransferForm_symmetric R F G

/-- Exact reproduction of every matrix element transfers reflection positivity
to nonnegative quadratic form of the candidate on the embedded observable
range. -/
theorem finiteWilsonOSOneLayerOperator_nonneg_on_range_of_matrixDefect_eq_zero
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (B : FiniteLatticeWilsonOSGramBridge R)
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (observableEmbedding :
      (R.PositiveConfiguration → ℝ) →ₗ[ℝ] K)
    (candidate : K →L[ℝ] K)
    (hD : ∀ F G : R.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        R observableEmbedding candidate F G = 0)
    (F : R.PositiveConfiguration → ℝ) :
    0 ≤ inner ℝ
      (candidate (observableEmbedding F)) (observableEmbedding F) := by
  rw [(finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
    R observableEmbedding candidate F F).mp (hD F F)]
  exact finite_lattice_wilson_os_oneLayerTransferForm_nonneg R B F

/-- A single nonzero matrix-element defect is an exact obstruction to realizing
the geometric Wilson one-layer OS kernel by the proposed operator and
observable embedding. -/
theorem finiteWilsonOSOneLayerOperatorMatrixDefect_no_go
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (observableEmbedding :
      (R.PositiveConfiguration → ℝ) →ₗ[ℝ] K)
    (candidate : K →L[ℝ] K)
    (F G : R.PositiveConfiguration → ℝ)
    (hD : finiteWilsonOSOneLayerOperatorMatrixDefect
      R observableEmbedding candidate F G ≠ 0) :
    ¬ (∀ U V : R.PositiveConfiguration → ℝ,
      inner ℝ (candidate (observableEmbedding U)) (observableEmbedding V) =
        R.wilsonOneLayerTransferForm U V) := by
  intro hAll
  apply hD
  apply
    (finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
      R observableEmbedding candidate F G).2
  exact hAll F G

/-- Public one-layer form receipt: the actual Wilson kernel gives a symmetric
bilinear and reflection-positive geometric OS transfer form. -/
theorem finiteWilsonOSOneLayerTransferFormPackage
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (B : FiniteLatticeWilsonOSGramBridge R) :
    (∀ F G : R.PositiveConfiguration → ℝ,
      R.wilsonOneLayerTransferForm F G =
        R.wilsonOneLayerTransferForm G F) ∧
    (∀ F : R.PositiveConfiguration → ℝ,
      0 ≤ R.wilsonOneLayerTransferForm F F) := by
  exact ⟨
    finite_lattice_wilson_os_oneLayerTransferForm_symmetric R,
    finite_lattice_wilson_os_oneLayerTransferForm_nonneg R B⟩

end

end MathlibAnalytic
end MGAP4D

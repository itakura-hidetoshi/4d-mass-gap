import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPositivePerronVacuumSpatialTransportV5_PZ37AAS
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAS — strictly positive genuine Wilson vacuum spatial rigidity

A strictly positive kernel has at most one strictly positive continuous
eigenfunction at a fixed positive eigenvalue, up to a scalar, on a compact
configuration space. The proof uses the attained minimum of a ratio,
positivity of a genuine integral, and the original pointwise eigen-equations;
it does NOT assume the Haar measure has full support.

Apply this lemma to AAR original Wilson kernel and AAQ original Haar transport.
The original identity boundary is fixed by every spatial translation, and its
vacuum value is strictly positive. Therefore the scalar is 1. We obtain actual
pointwise spatial-translation invariance of the previously constructed
canonical positive Gauss-law Perron vacuum, for every H and beta >= 0.

This does not replace the Wilson kernel, the physical vacuum, nor either
interacting conditional Wilson posterior; AAP posterior response invariance
remains a distinct final transport step. No new axioms or sorry.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAS2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAS2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAS2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAS2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAS2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AAS2_probability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G
private noncomputable instance p4Q2PZ37AAS2_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AAS2_originalHaarProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Rigidity of positive integral eigenfunctions for a strictly positive
kernel. The measure is not replaced, and full support is not assumed:
a.e. equality is promoted to pointwise equality by the two actual
eigenfunction identities with positive eigenvalue. -/
private theorem positiveKernel_continuousEigenfunction_unique_up_to_scale
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X]
    (μ : Measure X) (K : X → X → ℝ) (lambda : ℝ) (hlambda : 0 < lambda)
    (u v : X → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (hvpos : ∀ A, 0 < v A) (hKpos : ∀ A B, 0 < K A B)
    (huInt : ∀ B, Integrable (fun A => u A * K A B) μ)
    (hvInt : ∀ B, Integrable (fun A => v A * K A B) μ)
    (huEig : ∀ B, lambda * u B = ∫ A, u A * K A B ∂μ)
    (hvEig : ∀ B, lambda * v B = ∫ A, v A * K A B ∂μ) :
    ∃ c : ℝ, ∀ B, u B = c * v B := by
  let r : X → ℝ := fun A => u A / v A
  have hr : Continuous r := by
    exact hu.div hv (fun A => (hvpos A).ne')
  obtain ⟨B0, hmin⟩ :=
    hr.exists_forall_le_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace r)
  let c : ℝ := r B0
  have hle (A : X) : c * v A ≤ u A := by
    exact (le_div_iff₀ (hvpos A)).mp (hmin A)
  have hAt : u B0 = c * v B0 := by
    dsimp [c, r]
    exact (div_mul_cancel₀ (hvpos B0).ne').symm
  have hIntF :
      Integrable (fun A : X => (u A - c * v A) * K A B0) μ := by
    have heq :
        (fun A : X => (u A - c * v A) * K A B0) =
          (fun A : X => u A * K A B0 - c * (v A * K A B0)) := by
      funext A
      ring
    rw [heq]
    exact (huInt B0).sub ((hvInt B0).const_mul c)
  have hFnonneg :
      ∀ᵐ A ∂μ, 0 ≤ (u A - c * v A) * K A B0 := by
    filter_upwards with A
    exact mul_nonneg (sub_nonneg.mpr (hle A)) (hKpos A B0).le
  have hFzero :
      (∫ A : X, (u A - c * v A) * K A B0 ∂μ) = 0 := by
    calc
      (∫ A : X, (u A - c * v A) * K A B0 ∂μ) =
          ∫ A : X, u A * K A B0 - c * (v A * K A B0) ∂μ := by
        apply integral_congr_ae
        filter_upwards with A
        ring
      _ = (∫ A : X, u A * K A B0 ∂μ) -
            c * (∫ A : X, v A * K A B0 ∂μ) := by
        rw [integral_sub (huInt B0) ((hvInt B0).const_mul c),
            integral_const_mul]
      _ = lambda * u B0 - c * (lambda * v B0) := by
        rw [← huEig B0, ← hvEig B0]
      _ = 0 := by
        rw [hAt]
        ring
  have hZeroAE :
      (fun A : X => (u A - c * v A) * K A B0) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae hFnonneg hIntF).mp hFzero
  have hEqAE : u =ᵐ[μ] fun A => c * v A := by
    filter_upwards [hZeroAE] with A hA
    have hsub : u A - c * v A = 0 :=
      (mul_eq_zero.mp hA).resolve_right (hKpos A B0).ne'
    exact sub_eq_zero.mp hsub
  refine ⟨c, ?_⟩
  intro B
  have hEqInt :
      (∫ A : X, u A * K A B ∂μ) =
        ∫ A : X, (c * v A) * K A B ∂μ := by
    apply integral_congr_ae
    filter_upwards [hEqAE] with A hA
    rw [hA]
  have hEqLambda :
      lambda * u B = lambda * (c * v B) := by
    calc
      lambda * u B = ∫ A : X, u A * K A B ∂μ := huEig B
      _ = ∫ A : X, (c * v A) * K A B ∂μ := hEqInt
      _ = c * (∫ A : X, v A * K A B ∂μ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with A
        ring
      _ = lambda * (c * v B) := by
        rw [← hvEig B]
        ring
  exact (mul_left_cancel₀ hlambda.ne' hEqLambda)

namespace GroundStatePosteriorJoint

section PerronRigidity
variable (H : ℕ)
local notation "Disp" => PeriodicHypercubicEvenSpatialDisplacement H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" =>
  p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative H 2

/-- The CANONICAL strictly positive true physical Wilson Perron vacuum,
not a Haar surrogate, is pointwise invariant under every original spatial
translation. The proof is independent of a second Gauss-law L2 presentation:
both positive continuous functions satisfy the actual same integral equation,
and the original identity boundary fixes their relative normalization. -/
theorem p4Q2PZ37AAS_originalPositivePerronVacuum_spatialTranslation
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Omega (by norm_num) beta hbeta (T a B) =
      Omega (by norm_num) beta hbeta B := by
  let v : Cfg → ℝ := Omega (by norm_num) beta hbeta
  let u : Cfg → ℝ := fun A => v (T a A)
  let lambda : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖
  have hlambda : 0 < lambda := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H 2 (by norm_num) beta hbeta
  have hv : Continuous v := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
        H 2 (by norm_num) beta hbeta
  have hu : Continuous u :=
    hv.comp (p4Q2PZ37AAS_originalSpatialConfigurationTranslation_continuous H a)
  have hvpos : ∀ A : Cfg, 0 < v A := by
    intro A
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H 2 (by norm_num) beta hbeta A
  have hKpos : ∀ A B : Cfg, 0 < K beta A B := by
    intro A B
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H 2 beta A B
  have hKcont (B : Cfg) : Continuous (fun A : Cfg => K beta A B) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp₂ continuous_id continuous_const
  have huInt (B : Cfg) :
      Integrable (fun A : Cfg => u A * K beta A B) haar :=
    (hu.mul (hKcont B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hvInt (B : Cfg) :
      Integrable (fun A : Cfg => v A * K beta A B) haar :=
    (hv.mul (hKcont B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have huEig (B : Cfg) :
      lambda * u B = ∫ A : Cfg, u A * K beta A B ∂haar := by
    exact p4Q2PZ37AAS_originalTranslatedPerronVacuum_eigenIntegral
      H a beta hbeta B
  have hvEig (B : Cfg) :
      lambda * v B = ∫ A : Cfg, v A * K beta A B ∂haar := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_continuousVacuum_kernel
        H 2 (by norm_num) beta hbeta B
  letI : Nonempty Cfg := ⟨fun _ => 1⟩
  obtain ⟨c, hc⟩ :=
    positiveKernel_continuousEigenfunction_unique_up_to_scale
      haar (K beta) lambda hlambda u v hu hv hvpos hKpos huInt hvInt huEig hvEig
  let I : Cfg := originalWilsonExplicitIdentityBoundary H
  have hAnchor : u I = v I := by
    dsimp [u, I]
    rw [p4Q2PZ37AAQ_identityLeftBoundary_translation H a]
  have hcAt : u I = c * v I := hc I
  have hci : c = 1 := by
    have hzero : (c - 1) * v I = 0 := by
      nlinarith only [hcAt, hAnchor]
    have hz : c - 1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_right (hvpos I).ne'
    linarith
  change u B = v B
  rw [hc B, hci, one_mul]

/-- The unchanged ORIGINAL continuous-vacuum Wilson posterior raw density
is exactly covariant under simultaneous translation of both boundaries.
Neither the inner original GI/FX two-Wilson-posterior quotient nor AAP's
integrated response is yet being identified with this marginal. -/
theorem p4Q2PZ37AAS_originalContinuousVacuumPosteriorRawWeight_spatialTranslation
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta) (B A : Cfg) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
        H 2 (by norm_num) beta hbeta (T a B) (T a A) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
        H 2 (by norm_num) beta hbeta B A := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
  rw [p4Q2PZ37AAS_originalPositivePerronVacuum_spatialTranslation H a beta hbeta A,
    p4Q2PZ37AAR_originalCompleteOneSlabKernel_translation H a beta A B]

end PerronRigidity
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAS_originalPositivePerronVacuum_spatialTranslation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAS_originalContinuousVacuumPosteriorRawWeight_spatialTranslation

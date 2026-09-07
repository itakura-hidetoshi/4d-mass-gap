import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateDoobEightColorDefect
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonVacuumL2LinearIsometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 2000000

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The two ground-state boundary pullbacks of Haar-to-vacuum transforms have
exactly the normalized ambient Wilson transfer matrix coefficient.  The proof
uses only the literal joint density, the a.e. positive vacuum representative,
and the existing Hilbert--Schmidt kernel pairing. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateBoundaryHaarToVacuum_inner_eq_ambientTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H N hN beta hbeta f))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H N hN beta hbeta g)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta f) g := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
    H N hN beta hbeta
  let π := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let E := realL2ExternalTensor g f
  let Uf := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
    H N hN beta hbeta f
  let Ug := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
    H N hN beta hbeta g
  let uf := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
    H N hN beta hbeta f
  let ug := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
    H N hN beta hbeta g
  let rho :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ENNReal :=
    fun z => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z)
  let JR := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
    H N hN beta hbeta
  let JL := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    H N hN beta hbeta
  have hsnd :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_snd_measurePreserving
      H N hN beta hbeta
  have hfst :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_fst_measurePreserving
      H N hN beta hbeta
  have hJR : JR Uf =ᵐ[π] fun z => Uf z.2 := by
    simpa [JR, Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving Uf hsnd)
  have hJL : JL Ug =ᵐ[π] fun z => Ug z.1 := by
    simpa [JL, Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving Ug hfst)
  have hUf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta f
  have hUg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta g
  have hUfJoint : (fun z => Uf z.2) =ᵐ[π] fun z => uf z.2 := by
    simpa [Function.comp_def, Uf, uf, ν, π] using
      hUf.comp_tendsto hsnd.quasiMeasurePreserving.tendsto_ae
  have hUgJoint : (fun z => Ug z.1) =ᵐ[π] fun z => ug z.1 := by
    simpa [Function.comp_def, Ug, ug, ν, π] using
      hUg.comp_tendsto hfst.quasiMeasurePreserving.tendsto_ae
  have hrhoAE : AEMeasurable rho (μ.prod μ) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
        H N hN beta hbeta).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hrhoTop : ∀ᵐ z ∂(μ.prod μ), rho z < (⊤ : ENNReal) := by
    filter_upwards with z
    simp [rho]
  have hWpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
      H N hN beta hbeta
  have hΩpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_pos
      H N hN beta hbeta
  have hΩfst : ∀ᵐ z ∂(μ.prod μ), 0 < (Ω.1 : Lp ℝ 2 μ) z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hΩpos
  have hΩsnd : ∀ᵐ z ∂(μ.prod μ), 0 < (Ω.1 : Lp ℝ 2 μ) z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hΩpos
  have hKrep :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta
  have hErep := realL2ExternalTensor_coeFn g f
  change inner ℝ (JR Uf) (JL Ug) =
    lambda⁻¹ * inner ℝ
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta f) g
  calc
    inner ℝ (JR Uf) (JL Ug) =
        ∫ z, inner ℝ (uf z.2) (ug z.1) ∂π := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hJR, hJL, hUfJoint, hUgJoint] with z hJRz hJLz hUfz hUgz
      rw [hJRz, hJLz, hUfz, hUgz]
    _ = ∫ z, (rho z).toReal • inner ℝ (uf z.2) (ug z.1) ∂(μ.prod μ) := by
      change
        (∫ z, inner ℝ (uf z.2) (ug z.1) ∂((μ.prod μ).withDensity rho)) = _
      exact integral_withDensity_eq_integral_toReal_smul₀ hrhoAE hrhoTop _
    _ = ∫ z, lambda⁻¹ * inner ℝ (K z) (E z) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [hWpos, hΩfst, hΩsnd, hKrep, hErep] with z hW hΩ1 hΩ2 hK hE
      have hΩ1ne : (Ω.1 : Lp ℝ 2 μ) z.1 ≠ 0 := ne_of_gt hΩ1
      have hΩ2ne : (Ω.1 : Lp ℝ 2 μ) z.2 ≠ 0 := ne_of_gt hΩ2
      simp only [smul_eq_mul]
      dsimp [rho]
      rw [ENNReal.toReal_ofReal hW.le, hK, hE]
      simp only [realL2ExternalTensorFunction, real_inner_eq_re_inner (𝕜 := ℝ),
        RCLike.inner_apply, RCLike.re_to_real, conj_trivial]
      dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight,
        uf, ug, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction,
        Ω, lambda]
      have hΩ1ne' :
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) z.1 ≠ 0 := by
        simpa [Ω, μ] using hΩ1ne
      have hΩ2ne' :
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) z.2 ≠ 0 := by
        simpa [Ω, μ] using hΩ2ne
      have hcancel :
          ∀ {a b k x y l : ℝ}, a ≠ 0 → b ≠ 0 →
            a * k * b * x * y * a⁻¹ * b⁻¹ * l = k * x * y * l := by
        intro a b k x y l ha hb
        calc
          a * k * b * x * y * a⁻¹ * b⁻¹ * l =
              (a * a⁻¹) * (b * b⁻¹) * k * x * y * l := by ring
          _ = k * x * y * l := by simp [ha, hb]
      exact hcancel hΩ1ne' hΩ2ne'
    _ = lambda⁻¹ * ∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ) := by
      rw [integral_const_mul]
    _ = lambda⁻¹ * inner ℝ K E := by
      rw [MeasureTheory.L2.inner_def]
      simpa [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure]
    _ = lambda⁻¹ * realL2HilbertSchmidtKernelPairing K g f := by rfl
    _ = lambda⁻¹ * realL2HilbertSchmidtKernelPairing K f g := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_symmetric
        H N hN beta hbeta g f]
    _ = lambda⁻¹ * inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]

/-- On the Gauss-law carrier, the same joint boundary coefficient is exactly
the normalized physical Wilson transfer coefficient. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateBoundaryHaarToVacuum_inner_eq_physicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H N hN beta hbeta
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H N hN beta hbeta
            (g : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta f) g := by
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateBoundaryHaarToVacuum_inner_eq_ambientTransfer
      H N hN beta hbeta
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Matrix coefficients of the Doob boundary operator on transformed physical
vectors are exactly normalized physical transfer matrix coefficients.  No
surjectivity of the ground-state transform is required. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobHaarToVacuum_inner_eq_physicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H N hN beta hbeta
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
          H N hN beta hbeta
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta f) g := by
  let JL :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
      H N hN beta hbeta).toContinuousLinearMap
  let JR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
      H N hN beta hbeta
  let Uf := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  let Ug := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  change inner ℝ ((JL†) (JR Uf)) Ug = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateBoundaryHaarToVacuum_inner_eq_physicalTransfer
      H N hN beta hbeta f g

/-- The norm of the normalized physical transfer image is bounded by the Doob
image of the ground-state transform.  This is obtained directly from the
matrix coefficient identity with `g = T_phys f` and real Cauchy--Schwarz. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNormalizedTransfer_norm_le_groundStateDoob
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
          H N hN beta hbeta
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))‖ := by
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
  let D := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
    H N hN beta hbeta
  let u := U
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  let Tf := T f
  have hpair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobHaarToVacuum_inner_eq_physicalTransfer
      H N hN beta hbeta f Tf
  have hUnorm :
      ‖U
        (Tf : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ = ‖Tf‖ := by
    calc
      ‖U
        (Tf : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ =
          ‖(Tf : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ :=
        U.norm_map _
      _ = ‖Tf‖ := rfl
  have hCS := real_inner_le_norm
    (D u)
    (U
      (Tf : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  have hmain : lambda⁻¹ * ‖Tf‖ ^ 2 ≤ ‖D u‖ * ‖Tf‖ := by
    rw [hpair, real_inner_self_eq_norm_sq, hUnorm] at hCS
    simpa [lambda, T, U, D, u, Tf] using hCS
  change lambda⁻¹ * ‖Tf‖ ≤ ‖D u‖
  by_cases hzero : ‖Tf‖ = 0
  · simp [hzero]
  · have hpos : 0 < ‖Tf‖ := lt_of_le_of_ne (norm_nonneg Tf) (Ne.symm hzero)
    nlinarith [hmain]

/-- Consequently the Doob squared defect of a transformed physical vector is
no larger than the squared defect of the normalized physical transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobDefect_le_normalizedPhysicalDefect
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖f‖ ^ 2 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H N hN beta hbeta
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))‖ ^ 2 ≤
      ‖f‖ ^ 2 -
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta f‖) ^ 2 := by
  let a :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta f‖
  let b :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
        H N hN beta hbeta
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))‖
  have hab : a ≤ b := by
    simpa [a, b] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNormalizedTransfer_norm_le_groundStateDoob
        H N hN beta hbeta f
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hsq : a ^ 2 ≤ b ^ 2 := by
    have h1 : 0 ≤ b - a := sub_nonneg.mpr hab
    have h2 : 0 ≤ b + a := add_nonneg hb0 ha0
    have hprod := mul_nonneg h1 h2
    nlinarith
  change ‖f‖ ^ 2 - b ^ 2 ≤ ‖f‖ ^ 2 - a ^ 2
  linarith

section GroundStatePhysicalEightColorComparison

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "Q" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
local notation "E8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
    H N hN beta hbeta
local notation "Color" => Fin 8

/-- The already-proved joint eight-color Doob comparison therefore descends
to the normalized physical squared transfer defect, without identifying the
joint carrier with global Gibbs `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_eta_le_normalizedPhysicalDefect
    (P : Color → J →L[ℝ] J)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : J →L[ℝ] J) : J →ₗ[ℝ] J).IsSymmetric)
    (hfixed : ∀ c u, P c (Q (R u)) = Q (R u))
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (f : Phys) :
    eta * E8 P (U (f : HaarL2)) ≤
      ‖f‖ ^ 2 - (‖T‖⁻¹ * ‖T f‖) ^ 2 := by
  let u :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
      H N hN beta hbeta
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have hDoob :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_eta_le_doobDefect
      H N hN beta hbeta P hPid hPsymm hfixed eta heta0 heta1 u
  have hBridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobDefect_le_normalizedPhysicalDefect
      H N hN beta hbeta f
  have hu : ‖u‖ = ‖f‖ := by
    calc
      ‖u‖ =
          ‖(f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ := by
        exact
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H N hN beta hbeta).norm_map _
      _ = ‖f‖ := rfl
  calc
    eta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
          H N hN beta hbeta P u ≤
      ‖u‖ ^ 2 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
          H N hN beta hbeta u‖ ^ 2 := hDoob
    _ = ‖f‖ ^ 2 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
          H N hN beta hbeta u‖ ^ 2 := by rw [hu]
    _ ≤ ‖f‖ ^ 2 -
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta f‖) ^ 2 := by
      simpa [u] using hBridge

/-- Clearing the strictly positive physical transfer normalization gives the
raw physical squared defect comparison.  The color family remains abstract in
this theorem; concrete six-spatial plus two temporal conditional expectations
are discharged separately. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_eta_mul_transferNormSq_le_rawPhysicalDefect
    (P : Color → J →L[ℝ] J)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : J →L[ℝ] J) : J →ₗ[ℝ] J).IsSymmetric)
    (hfixed : ∀ c u, P c (Q (R u)) = Q (R u))
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (f : Phys) :
    eta * E8 P (U (f : HaarL2)) * ‖T‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖f‖ ^ 2 - ‖T f‖ ^ 2 := by
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  let t := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta f‖
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
      H N hN beta hbeta P
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
        H N hN beta hbeta
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      )
  have hnormed :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_eta_le_normalizedPhysicalDefect
      H N hN beta hbeta P hPid hPsymm hfixed eta heta0 heta1 f
  have hlambda : 0 < lambda := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda
  have hmul := mul_le_mul_of_nonneg_right hnormed (sq_nonneg lambda)
  change eta * E * lambda ^ 2 ≤ lambda ^ 2 * ‖f‖ ^ 2 - t ^ 2
  calc
    eta * E * lambda ^ 2 ≤
        (‖f‖ ^ 2 - (lambda⁻¹ * t) ^ 2) * lambda ^ 2 := by
      simpa [E, lambda, t, mul_assoc] using hmul
    _ = lambda ^ 2 * ‖f‖ ^ 2 - t ^ 2 := by
      field_simp [hlambda_ne]

end GroundStatePhysicalEightColorComparison

end

end MathlibAnalytic
end MGAP4D

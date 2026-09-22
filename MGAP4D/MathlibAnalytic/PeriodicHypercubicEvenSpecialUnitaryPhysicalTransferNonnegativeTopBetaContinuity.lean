import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferFixedContourProjectorIdentification
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# Coupling continuity of the canonical normalized nonnegative Wilson top mode

The continuous canonical top projection is evaluated on the vacuum at a fixed
base coupling. Physical absolute value removes the sign of this local real top
vector. Normalization then recovers the *existing* canonical nonnegative vacuum,
using top-ray uniqueness and its norm-one normalization.

The projected vector is required to be nonzero only near the base coupling;
there it is nonzero by continuity and its norm-one value at the base. No global
nonvanishing of a fixed reference vector's projection is assumed.

These are finite-volume norm-continuity statements on the nonnegative coupling
half-line, including beta = 0. They do not assert pointwise kernel continuity,
a volume-uniform neighborhood, or a thermodynamic or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- The existing real L2 absolute-value operation is norm-continuous. -/
theorem realL2Abs_continuous
    {α : Type*} [MeasurableSpace α] {μ : Measure α} :
    Continuous (realL2Abs (α := α) (μ := μ)) := by
  change Continuous (fun f : Lp ℝ 2 μ => Lp.posPart f + Lp.negPart f)
  exact Lp.continuous_posPart.add Lp.continuous_negPart

/-- Absolute value removes the scalar sign on a nonnegative real L2 ray. -/
theorem realL2Abs_smul_of_ae_nonnegative
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ a ∂μ, 0 ≤ f a) (c : ℝ) :
    realL2Abs (c • f) = |c| • f := by
  apply Lp.ext
  filter_upwards [realL2Abs_coeFn (c • f),
    Lp.coeFn_smul c f, Lp.coeFn_smul |c| f, hf] with a habs hsc hsa hpos
  have hsc' : (c • f) a = c * f a := hsc
  have hsa' : (|c| • f) a = |c| * f a := hsa
  calc
    realL2Abs (c • f) a = |(c • f) a| := habs
    _ = |c * f a| := congrArg abs hsc'
    _ = |c| * f a := by rw [abs_mul, abs_of_nonneg hpos]
    _ = (|c| • f) a := hsa'.symm

local instance nonnegativeTopBetaContinuitySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance nonnegativeTopBetaContinuitySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance nonnegativeTopBetaContinuitySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance nonnegativeTopBetaContinuitySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance nonnegativeTopBetaContinuitySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance nonnegativeTopBetaContinuitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance nonnegativeTopBetaContinuityRealCompleteSpace (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance nonnegativeTopBetaContinuityComplexCompleteSpace (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The physical absolute value is continuous in the actual gauge-invariant
L2 carrier, not just in a separately chosen model of the top line. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_continuous
    (H N : ℕ) :
    Continuous (periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs
  exact (realL2Abs_continuous.comp continuous_subtype_val).subtype_mk _

/-- Absolute value of a real scalar multiple of the canonical nonnegative
vacuum is the absolute scalar multiple of that same vacuum. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_smul_nonnegativeTop
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (c : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N
        (c • periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta) =
      |c| • periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta hbeta := by
  apply Subtype.ext
  change realL2Abs
      (c • (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta hbeta).1) =
    |c| • (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1
  exact realL2Abs_smul_of_ae_nonnegative _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H N hN beta hbeta) c

/-- Evaluate the continuous complex CFC projector on a fixed real vector, and
recover the real top projection through the same-root real-part map. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_apply_halfLine_continuous
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta.1 beta.2 f) := by
  let EC := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let fC : EC := periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f
  let PC : Set.Ici (0 : ℝ) → EC →L[ℂ] EC :=
    fun beta =>
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta.1 beta.2
  have hPC : Continuous PC :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_halfLine_continuous
      H N hN
  have hEval : Continuous (fun beta : Set.Ici (0 : ℝ) => PC beta fC) :=
    (ContinuousLinearMap.apply ℂ EC fC).continuous.comp hPC
  have hRe :
      Continuous (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N (PC beta fC)) :=
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPartCLM H N).continuous.comp hEval
  have heq :
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N (PC beta fC)) =
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta.1 beta.2 f) := by
    funext beta
    change periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta.1 beta.2 f
    rw [
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_complexification,
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_ofReal,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_ofReal
    ]
  exact heq ▸ hRe

/-- The real top projection fixes the existing nonnegative canonical vacuum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_nonnegativeTop_fixed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta hbeta := by
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta
  have hmem : Omega ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTop]
    exact Submodule.mem_span_singleton_self Omega
  have hfix :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta Omega).mp hmem
  exact (realHilbertTopEigenspaceProjection_apply_eq_self_iff _ Omega).mpr hfix

/-- On a projected real top vector, physical absolute value is its norm times
the canonical nonnegative vacuum. This identifies the sign-free local section. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_topSpectralProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta f) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta f‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H N hN beta hbeta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  have hrange : R.range = ℝ ∙ Omega :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_range
      H N hN beta hbeta).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTop
        H N hN beta hbeta)
  have hmem : R f ∈ ℝ ∙ Omega := by
    rw [← hrange]
    exact ⟨f, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hOmegaNorm : ‖Omega‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H N hN beta hbeta
  have hnorm : ‖R f‖ = |c| := by
    calc
      ‖R f‖ = ‖c • Omega‖ := congrArg (fun v => ‖v‖) hc.symm
      _ = ‖c‖ * ‖Omega‖ := norm_smul c Omega
      _ = |c| := by rw [hOmegaNorm, mul_one, Real.norm_eq_abs]
  change periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N (R f) =
    ‖R f‖ • Omega
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N (R f) =
        periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N (c • Omega) :=
      congrArg (periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N) hc.symm
    _ = |c| • Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_smul_nonnegativeTop
        H N hN beta hbeta c
    _ = ‖R f‖ • Omega := by rw [hnorm]

/-- The original normalized nonnegative physical top eigenvector is continuous
in beta on the nonnegative half-line. The local formula uses a nonzero projected
reference vector only in a neighborhood where continuity supplies nonvanishing. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_halfLine_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta.1 beta.2) := by
  apply continuous_iff_continuousAt.mpr
  intro beta0
  let ER := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  let Omega : Set.Ici (0 : ℝ) → ER :=
    fun beta => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta.1 beta.2
  let v : Set.Ici (0 : ℝ) → ER :=
    fun beta => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta.1 beta.2 (Omega beta0)
  let A : ER → ER := periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N
  let g : Set.Ici (0 : ℝ) → ER := fun beta => ‖v beta‖⁻¹ • A (v beta)
  have hv : Continuous v :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_apply_halfLine_continuous
      H N hN (Omega beta0)
  have hv0 : v beta0 = Omega beta0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_nonnegativeTop_fixed
      H N hN beta0.1 beta0.2
  have hnorm0 : ‖v beta0‖ = 1 :=
    (congrArg (fun x : ER => ‖x‖) hv0).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
        H N hN beta0.1 beta0.2)
  have hn0 : ‖v beta0‖ ≠ 0 := by rw [hnorm0]; exact one_ne_zero
  have hNormAt : ContinuousAt (fun beta => ‖v beta‖) beta0 :=
    hv.continuousAt.norm
  have hAbs : Continuous (fun beta => A (v beta)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_continuous H N).comp hv
  have hg : ContinuousAt g beta0 :=
    (hNormAt.inv₀ hn0).smul hAbs.continuousAt
  have hformula (beta : Set.Ici (0 : ℝ)) (hn : ‖v beta‖ ≠ 0) :
      g beta = Omega beta := by
    have hA : A (v beta) = ‖v beta‖ • Omega beta :=
      periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_topSpectralProjection
        H N hN beta.1 beta.2 (Omega beta0)
    change ‖v beta‖⁻¹ • A (v beta) = Omega beta
    rw [hA, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have heq : ∀ᶠ beta in 𝓝 beta0, g beta = Omega beta := by
    filter_upwards [hNormAt.eventually_ne hn0] with beta hn
    exact hformula beta hn
  have hlimit : Tendsto g (𝓝 beta0) (𝓝 (Omega beta0)) := by
    rw [← hformula beta0 hn0]
    exact hg
  change Tendsto Omega (𝓝 beta0) (𝓝 (Omega beta0))
  exact (Filter.tendsto_congr' heq).mp hlimit

/-- The same-root complex embedding of the canonical nonnegative vacuum is
continuous as well; no independent complex phase choice is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ofReal_halfLine_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta.1 beta.2)) := by
  exact (periodicHypercubicEvenSpecialUnitaryPhysicalOfRealLinearIsometry H N).continuous.comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_halfLine_continuous
      H N hN)

end
end MGAP4D.MathlibAnalytic

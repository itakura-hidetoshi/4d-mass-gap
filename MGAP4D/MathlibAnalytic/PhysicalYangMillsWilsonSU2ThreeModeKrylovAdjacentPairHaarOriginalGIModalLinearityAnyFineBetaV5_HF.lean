import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGIDetectorMassRankOneScalingV5_HE
import Mathlib.Tactic

/-!
# P4-Q2-HF: original two-Wilson-posterior GI detector is exactly linear
# on the ACTUAL finite-depth right physical Krylov coefficient space

GZ identified the true frozen Wilson transfer of every signed finite
fine-right-Krylov source with a real modal linear functional. GN proved
the full GI two-interacting-Wilson-posterior expectation gap is the true
transfer-fiber Haar contrast moment multiplied by the original positive
joint-density factors. Transport GZ's finite linearity through that
integrable genuine density contrast and obtain, for ANY nonnegative
fine beta(n+1) and frozen beta(n),

 Delta_(sum a_j v_j)(e,z) = sum a_j Delta_(v_j)(e,z).

No collapsed fine orbit is assumed! The genuine frozen and fine couplings
remain distinct, all original Wilson conditional posteriors are retained,
and the transfer-fiber moment is integrated against the actual posterior
density contrast, with Haar only the reference integration measure.

The resulting finite coefficient GI detector is a REAL LINEAR MAP.
Its exact kernel is therefore a submodule, and its detectable complement
is open. Conditional on nonzero zero-depth GI detection at a single
actual link/context its kernel is a codimension-one hyperplane even at
arbitrary positive fine beta. Such anchor nonzero is NOT asserted.

No physical all-boundary GI injectivity, coefficient frame, uniform
Gram bound, H1-C3 reconstruction or continuum Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3700000
set_option synthInstance.maxHeartbeats 1000000

local instance p4Q2HF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Scalar algebra for the ACTUAL Wilson transfer-fiber integral.
The same density and normalization denominators are used in every
modal term; none is replaced by a surrogate independent posterior. -/
private theorem p4Q2HF_finiteSum_div_mul
    {ι : Type*} [Fintype ι]
    (a x : ι → ℝ) (q d : ℝ) :
    ((∑ j, a j * x j) / q) * d =
      ∑ j, a j * ((x j / q) * d) := by
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The original GN Wilson transfer-fiber moment is exactly finite
linear on ACTUAL right-Krylov physical source coefficients for any
nonnegative fine coupling. Every summand is genuinely integrable;
the frozen conditional Wilson contrast density remains unchanged. -/
theorem p4Q2HF_actualRightOriginalTransferFiberMoment_finite_sum
    (a : Fin (r + 1) → ℝ) (e : Link) (z : Cfg × Cfg) :
    p4Q2GN_originalTransferFiberContrastMoment Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z =
    ∑ j : Fin (r + 1), a j *
      p4Q2GN_originalTransferFiberContrastMoment Hn (beta n) (hbeta n)
        (RightFactor n (j : ℕ)) e z := by
  classical
  let ν : Measure Gauge := normalizedCompactHaar Gauge
  let F : Phys := ∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)
  let s := continuousJointSqrtDensity Hn 2 (by norm_num) (beta n) (hbeta n)
  let D := p4Q2GB_originalWilsonPosteriorLeftDensityContrast Hn (beta n) (hbeta n)
  let t (f : Phys) (B : Cfg) :=
    decomposableOneSliceTransferIntegral Hn 2 (beta n) f B
  let η (j : Fin (r + 1)) (g : Gauge) : ℝ :=
    (t (RightFactor n (j : ℕ)) (Function.update z.2 e g) /
      s (z.1, Function.update z.2 e g)) * D z.2 e g
  let κ (g : Gauge) : ℝ :=
    (t F (Function.update z.2 e g) /
      s (z.1, Function.update z.2 e g)) * D z.2 e g
  have hT (B : Cfg) :
      t F B =
        ∑ j : Fin (r + 1), a j * t (RightFactor n (j : ℕ)) B := by
    have h :=
      p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a B
    simpa only [t, F, Submodule.coe_sum, Submodule.coe_smul,
      p4Q2GY_actualRightWilsonModalTransfer,
      p4Q2GY_modalTransferLinear_apply] using h
  have hPoint (g : Gauge) :
      κ g = ∑ j : Fin (r + 1), a j * η j g := by
    dsimp [κ, η]
    rw [hT (Function.update z.2 e g)]
    exact p4Q2HF_finiteSum_div_mul a
      (fun j : Fin (r + 1) =>
        t (RightFactor n (j : ℕ)) (Function.update z.2 e g))
      (s (z.1, Function.update z.2 e g)) (D z.2 e g)
  have hInt (j : Fin (r + 1)) :
      Integrable (fun g : Gauge => a j * η j g) ν := by
    have hi := p4Q2GN_originalTransferFiberContrast_integrable
      Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z
    exact hi.const_mul (a j)
  change (∫ g : Gauge, κ g ∂ν) =
    ∑ j : Fin (r + 1), a j * (∫ g : Gauge, η j g ∂ν)
  calc
    (∫ g : Gauge, κ g ∂ν) =
        ∫ g : Gauge, (∑ j : Fin (r + 1), a j * η j g) ∂ν := by
      apply integral_congr_ae
      filter_upwards with g
      exact hPoint g
    _ = ∑ j : Fin (r + 1),
          ∫ g : Gauge, a j * η j g ∂ν := by
      rw [integral_finset_sum]
      intro j _hj
      exact hInt j
    _ = ∑ j : Fin (r + 1),
          a j * (∫ g : Gauge, η j g ∂ν) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact integral_const_mul (a j) (η j)

/-- The ORIGINAL physical response gap between two different
INTERACTING Wilson conditional posteriors is finite real-linear
in all genuine signed fine-right Krylov coefficients, without the
fine-beta-zero restriction from HC. -/
theorem p4Q2HF_actualRightOriginalGIExpectationGap_finite_sum
    (a : Fin (r + 1) → ℝ) (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z =
    ∑ j : Fin (r + 1), a j *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    Hn 2 (by norm_num) (beta n) (hbeta n)‖⁻¹
  let s := continuousJointSqrtDensity Hn 2 (by norm_num) (beta n) (hbeta n)
  let C : ℝ := -L * s z
  let D (f : Phys) :=
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) f e z
  let J (f : Phys) :=
    p4Q2GN_originalTransferFiberContrastMoment
      Hn (beta n) (hbeta n) f e z
  let F : Phys := ∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)
  have hGN (f : Phys) : D f = C * J f := by
    exact p4Q2GN_originalExpectationGap_eq_transferFiberMoment
      Hn (beta n) (hbeta n) f e z
  have hSum : J F = ∑ j : Fin (r + 1), a j * J (RightFactor n (j : ℕ)) :=
    p4Q2HF_actualRightOriginalTransferFiberMoment_finite_sum
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z
  change D F = ∑ j : Fin (r + 1), a j * D (RightFactor n (j : ℕ))
  calc
    D F = C * J F := hGN F
    _ = C * (∑ j : Fin (r + 1), a j * J (RightFactor n (j : ℕ))) := by
      rw [hSum]
    _ = ∑ j : Fin (r + 1), a j * (C * J (RightFactor n (j : ℕ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = ∑ j : Fin (r + 1), a j * D (RightFactor n (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact (congrArg (fun v : ℝ => a j * v)
        (hGN (RightFactor n (j : ℕ)))).symm

/-- The first REAL LINEAR modal coefficient representation of the
original TWO-WILSON-posterior GI detector on the ACTUAL complete
fine-right physical Krylov orbit, valid for ANY nonnegative fine beta. -/
noncomputable def p4Q2HF_actualRightGIModalLinear
    (e : Link) (z : Cfg × Cfg) :
    (Fin (r + 1) → ℝ) →ₗ[ℝ] ℝ :=
  p4Q2GY_modalTransferLinear r
    (fun j : Fin (r + 1) =>
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z)

/-- The actual GI detector integral of EVERY signed fine-right Krylov
physical source is EXACTLY the newly constructed real modal linear
map, without assuming positive fine-beta Krylov independence. -/
theorem p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
    (a : Fin (r + 1) → ℝ) (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z =
    p4Q2HF_actualRightGIModalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z a := by
  simpa only [p4Q2HF_actualRightGIModalLinear,
    p4Q2GY_modalTransferLinear_apply] using
    (p4Q2HF_actualRightOriginalGIExpectationGap_finite_sum
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z)

/-- For all actual fine couplings, the GI detector-zero coefficient
locus at one original Wilson link/context is the kernel of a genuine
finite-dimensional REAL linear map. It may be the entire space. -/
theorem p4Q2HF_actualRightGI_null_iff_mem_modalKernel
    (a : Fin (r + 1) → ℝ) (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 ↔
    a ∈ (p4Q2HF_actualRightGIModalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z).ker := by
  rw [p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a e z]
  exact (LinearMap.mem_ker).symm

/-- The nonzero genuine GI detector coefficient locus is an OPEN
subset of the physical finite-dimensional signed Krylov coefficient
space at ANY genuine fine beta. -/
theorem p4Q2HF_actualRightGI_detected_isOpen (e : Link) (z : Cfg × Cfg) :
    IsOpen {a : Fin (r + 1) → ℝ |
      p4Q2HF_actualRightGIModalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z a ≠ 0} := by
  exact p4Q2GY_modalTransferLinear_detected_isOpen r
    (fun j : Fin (r + 1) =>
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z)

/-- If the TRUE zero-depth physical source has a nonzero GI posterior
expectation gap at this ACTUAL Wilson link/background, then the
coefficient detector has precisely one-dimensional range and
codimension-one kernel, even at arbitrary positive fine beta.
Nonvanishing is an EXPLICIT unproved physical hypothesis. -/
theorem p4Q2HF_actualRightGI_modalKernel_finrank_of_anchor_ne
    (e : Link) (z : Cfg × Cfg)
    (hAnchor :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z ≠ 0) :
    Module.finrank ℝ
      ↥(p4Q2HF_actualRightGIModalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z).ker = r := by
  let w : Fin (r + 1) → ℝ := fun j =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z
  let L := p4Q2GY_modalTransferLinear r w
  let v := p4Q2GX_rightZeroCoefficient r
  have hLv : L v ≠ 0 := by
    change p4Q2GY_modalTransferLinear r w (p4Q2GX_rightZeroCoefficient r) ≠ 0
    rw [p4Q2GY_modalTransferLinear_anchor]
    exact hAnchor
  have hSurj : Function.Surjective L := by
    intro y
    refine ⟨(y / L v) • v, ?_⟩
    change L ((y / L v) • v) = y
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ y hLv
  have hRange : L.range = ⊤ := LinearMap.range_eq_top.mpr hSurj
  have hDimRange : Module.finrank ℝ ↥L.range = 1 := by
    rw [hRange]
    simp
  have hDimSource : Module.finrank ℝ (Fin (r + 1) → ℝ) = r + 1 := by
    simp
  have hRank :
      Module.finrank ℝ ↥L.range + Module.finrank ℝ ↥L.ker =
        Module.finrank ℝ (Fin (r + 1) → ℝ) :=
    LinearMap.finrank_range_add_finrank_ker L
  change Module.finrank ℝ ↥L.ker = r
  omega

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HF_actualRightOriginalTransferFiberMoment_finite_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HF_actualRightOriginalGIExpectationGap_finite_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HF_actualRightGI_null_iff_mem_modalKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HF_actualRightGI_detected_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HF_actualRightGI_modalKernel_finrank_of_anchor_ne

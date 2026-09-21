import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumTopRayUniqueness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperatorLinear
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# One-slab physical transfer: operator-norm Lipschitz continuity in beta

The finite-volume Wilson top ray is now unique.  To use the existing
Riesz/CFC spectral-projection machinery for beta continuation, the next
analytic input is norm continuity of the actual one-slab physical transfer.

The proof remains entirely on the literal finite-volume Wilson carrier:

* the one-slab kernel is `exp (-beta * S(A,B))`;
* the action has the existing finite global budget `C_H`;
* the mean-value theorem gives the pointwise bound
  `|K_gamma-K_beta| <= C_H |gamma-beta|`;
* product Haar is a probability measure, so the same bound controls the
  product-`L2` kernel difference;
* the Hilbert--Schmidt kernel-to-operator map has norm at most one;
* restriction to the Gauss-law physical subspace cannot increase the bound.

Thus the genuine physical one-slab transfer is globally Lipschitz on the
nonnegative Wilson-coupling half-line for every fixed finite volume.

The constant is finite-volume dependent; it is used only for local spectral
continuation at a fixed volume.  No volume-uniform transfer gap, covariance
decay, Poincare inequality, coercivity, or mass-gap input is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

noncomputable section

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabOperatorNormBetaLipschitzSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise beta derivative of the literal symmetric one-slab Wilson kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_hasDerivAt_beta
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    HasDerivAt
      (fun beta' : ℝ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta' A B)
      (-periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B)
      beta := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B
  have hlinear : HasDerivAt (fun beta' : ℝ => -beta' * S) (-S) beta := by
    simpa [S] using (hasDerivAt_id (x := beta)).neg.mul_const S
  have hexp :
      HasDerivAt
        (fun beta' : ℝ => Real.exp (-beta' * S))
        (Real.exp (-beta * S) * (-S))
        beta :=
    hlinear.exp
  simpa only [
    S,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    neg_mul, mul_neg, neg_neg, mul_comm, mul_left_comm, mul_assoc] using hexp

/-- Pointwise finite-volume Lipschitz estimate in the Wilson coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N gamma A B -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let S :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B
  let K := fun t : ℝ =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N t A B
  let dK := fun t : ℝ => -S * K t
  have hC : 0 ≤ C := by
    unfold C periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    positivity
  have hS0 : 0 ≤ S := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
        H N hN A B
  have hSle : S ≤ C := by
    simpa [S, C] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
        H N hN A B
  have hSnorm : ‖S‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg hS0]
    exact hSle
  have hderiv :
      ∀ t ∈ Ici (0 : ℝ),
        HasDerivWithinAt K (dK t) (Ici (0 : ℝ)) t := by
    intro t ht
    have h :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_hasDerivAt_beta
        H N t A B
    simpa [K, dK, S] using h.hasDerivWithinAt
  have hbound : ∀ t ∈ Ici (0 : ℝ), ‖dK t‖ ≤ C := by
    intro t ht
    have hKt : |K t| ≤ 1 := by
      simpa [K] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
          H N hN t ht A B
    calc
      ‖dK t‖ = ‖S‖ * |K t| := by
        simp [dK, Real.norm_eq_abs]
      _ ≤ C * 1 := mul_le_mul hSnorm hKt (abs_nonneg _) hC
      _ = C := by ring
  have hmvt :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_Ici (0 : ℝ)) hbeta hgamma
  simpa [K, C] using hmvt

/-- The product-Haar `L2` norm of the literal one-slab kernel difference has
the same beta-Lipschitz bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  let pairMu :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let Kgamma :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN gamma hgamma
  let Kbeta :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta
  let D : Lp ℝ 2 pairMu := Kgamma - Kbeta
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let R := C * ‖gamma - beta‖
  have hC : 0 ≤ C := by
    unfold C periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    positivity
  have hR : 0 ≤ R := mul_nonneg hC (norm_nonneg _)
  have hDrep :
      (fun p => D p) =ᵐ[pairMu]
        (fun p =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N gamma p.1 p.2 -
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta p.1 p.2) := by
    have hsub := Lp.coeFn_sub Kgamma Kbeta
    have hgammaRep :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H N hN gamma hgamma
    have hbetaRep :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H N hN beta hbeta
    filter_upwards [hsub, hgammaRep, hbetaRep] with p hsubp hgp hbp
    change D p =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N gamma p.1 p.2 -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2
    rw [show D p = Kgamma p - Kbeta p by simpa [D] using hsubp, hgp, hbp]
  have hDSqInt : Integrable (fun p => ‖D p‖ ^ 2) pairMu := by
    simpa [Real.norm_eq_abs, sq_abs] using (Lp.memLp D).integrable_sq
  have hConstInt : Integrable (fun _p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      R ^ 2) pairMu :=
    integrable_const _
  have hSq :
      ‖D‖ ^ 2 ≤ R ^ 2 := by
    rw [realL2_norm_sq_eq_integral_norm_sq D]
    calc
      (∫ p, ‖D p‖ ^ 2 ∂pairMu) ≤ ∫ _p, R ^ 2 ∂pairMu := by
        apply integral_mono_ae hDSqInt hConstInt
        filter_upwards [hDrep] with p hp
        rw [hp]
        have hk :=
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le_beta
            H N hN beta gamma hbeta hgamma p.1 p.2
        have hk' :
            ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N gamma p.1 p.2 -
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N beta p.1 p.2‖ ≤ R := by
          simpa [R, C] using hk
        exact pow_le_pow_left₀ (norm_nonneg _) hk' 2
      _ = R ^ 2 := by
        simp [pairMu]
  have hDnonneg : 0 ≤ ‖D‖ := norm_nonneg _
  have hnorm : ‖D‖ ≤ R := by
    nlinarith
  simpa [D, Kgamma, Kbeta, R, C, pairMu] using hnorm

/-- On a square `L2` carrier, the original and rectangular Fréchet--Riesz
Hilbert--Schmidt constructions agree. -/
private theorem oneSlabOperatorNormBetaLipschitz_square_eq_rectangular
    {α : Type*}
    [MeasurableSpace α]
    {μ : Measure α}
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ)) :
    realL2HilbertSchmidtKernelOperator K =
      realL2HilbertSchmidtRectangularKernelOperator K := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [realL2HilbertSchmidtKernelOperator_inner]
  rw [realL2HilbertSchmidtRectangularKernelOperator_inner]

/-- Ambient Haar-`L2` one-slab transfer is operator-norm Lipschitz in beta. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  let Kgamma :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN gamma hgamma
  let Kbeta :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta
  have hK :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_norm_sub_le_beta
      H N hN beta gamma hbeta hgamma
  change
    ‖realL2HilbertSchmidtKernelOperator Kgamma -
        realL2HilbertSchmidtKernelOperator Kbeta‖ ≤ _
  rw [
    oneSlabOperatorNormBetaLipschitz_square_eq_rectangular Kgamma,
    oneSlabOperatorNormBetaLipschitz_square_eq_rectangular Kbeta]
  have hop :
      realL2HilbertSchmidtRectangularKernelOperator Kgamma -
          realL2HilbertSchmidtRectangularKernelOperator Kbeta =
        realL2HilbertSchmidtRectangularKernelOperator (Kgamma - Kbeta) := by
    have hmap :=
      (realL2HilbertSchmidtRectangularKernelToOperatorLinearMap
        (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).map_sub
          Kgamma Kbeta
    simpa using hmap.symm
  rw [hop]
  exact
    (realL2HilbertSchmidtRectangularKernelOperator_norm_le (Kgamma - Kbeta)).trans
      (by simpa [Kgamma, Kbeta] using hK)

/-- The actual Gauss-law physical one-slab transfer inherits the same
operator-norm beta-Lipschitz estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN gamma hgamma -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      ‖gamma - beta‖
  have hC0 : 0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    positivity
  have hC : 0 ≤ C := mul_nonneg hC0 (norm_nonneg _)
  have hAmbient :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_sub_le_beta
      H N hN beta gamma hbeta hgamma
  change ‖D‖ ≤ C
  apply ContinuousLinearMap.opNorm_le_bound D hC
  intro f
  have hcoe :
      (((D f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
              H N hN gamma hgamma -
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
              H N hN beta hbeta)
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
    simp [D,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe]
  change
    ‖(((D f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))‖ ≤
      C *
        ‖(f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖
  rw [hcoe]
  exact
    (ContinuousLinearMap.le_opNorm
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta)
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))).trans
      (by
        have hf0 : 0 ≤ ‖(f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ :=
          norm_nonneg _
        exact mul_le_mul_of_nonneg_right
          (by simpa [C] using hAmbient)
          hf0)

/-- The physical top-transfer norm is Lipschitz in beta with the same
finite-volume coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    |‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma‖ -
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  exact
    (abs_norm_sub_norm_le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN gamma hgamma)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta)).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
        H N hN beta gamma hbeta hgamma)

end

end MathlibAnalytic
end MGAP4D

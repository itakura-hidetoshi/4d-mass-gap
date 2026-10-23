import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRawTwoSlabSpatialMinorV5_PI
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullOneSlabStrictTransferV5_LJ
import MGAP4D.MathlibAnalytic.RealL2BoundedKernelIntegralRepresentation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-PJ — exact ORIGINAL Wilson double-Haar two-slab kernel

PI removes the unknown transfer norm from the genuine three-point
Wilson third-mode determinant. PJ exposes the resulting raw two-slab
quantity as a literal DOUBLE HAAR INTEGRAL of the SAME unchanged
complete Wilson one-slab kernel.

For the true finite spatial SU(2) configuration space Cfg and its
original spatial product Haar reference μ, let
  K_t(X,Y) = ORIGINAL full symmetrized one-slab Wilson kernel,
including BOTH unchanged spatial Wilson halfweights and the full
temporal plaquette crossing action. With the actual Gauss-law unit U,
write W_t for its ORIGINAL physical Haar-L2 transfer.

First show, for EVERY genuine Gauss-law physical f with a continuous
representative ψ, the continuous Moore–Aronszajn image OU(W_t f)
coincides AT EACH SPATIAL CONFIGURATION B with
  ∫ A, K_t(A,B) ψ(A) dμ(A).
The proof uses the actual product-Haar Hilbert-Schmidt transfer
factorization and the original full-support Haar measure, not a
surrogate posterior or a spectral representation.

For ψ=PI's original one-slab output W_t U, obtain
  PI_raw_two(B) = ∫ A, ∫ X, K_t(A,B)*K_t(X,A) dμ(X) dμ(A).

This exact two-step kernel gives a fully literal original Wilson
three-boundary determinant whose nonzero witness is equivalent,
under the already PROVED D2>0 gate, to the true third physical
Hankel D3>0. Existence of a nonzero triple is STILL OPEN.
No Dobrushin, independent posterior, artificial rank,
sorry/admit, new axiom, U0 or continuum Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PJ_specialUnitaryNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun V : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (V : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00
local instance p4Q2PJ_specialUnitaryHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance
local instance p4Q2PJ_spatialFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PJ_productHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PJ_productHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section OriginalTwoSlabLiteralSpatialKernel
variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Raw" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 t
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "D2" => p4Q2PD_originalWilsonTwoMomentDet H t ht
local notation "D3" => p4Q2PD_originalWilsonThirdMomentGap H t ht

/-- The actual unnormalized original Wilson physical operator, on
an arbitrary real Gauss-law Hilbert source represented by the genuine
continuous spatial profile ψ, has this precise kernel integral as
an almost-everywhere spatial Haar representative. -/
theorem p4Q2PJ_originalRawPhysical_ae_originalKernelIntegral
    (f : Phys) (ψ : C(Cfg, ℝ))
    (hLp : (f : Lp ℝ 2 haar) = L ψ) :
    (fun B : Cfg => ((Raw f : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar]
      (fun B : Cfg => ∫ A : Cfg, K A B * ψ A ∂haar) := by
  let k : Cfg → Cfg → ℝ := K
  let K2 : Lp ℝ 2 (Measure.prod haar haar) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H 2 specialUnitaryTwoWilsonRankPositive t ht
  have hKernel :
      (fun p : Cfg × Cfg => K2 p) =ᵐ[Measure.prod haar haar]
        (fun p : Cfg × Cfg => k p.1 p.2) := by
    simpa only [k, K2,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H 2 specialUnitaryTwoWilsonRankPositive t ht)
  have hMeas :
      AEStronglyMeasurable (fun p : Cfg × Cfg => k p.1 p.2)
        (Measure.prod haar haar) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 t).measurable.aestronglyMeasurable
  have hBound (A B : Cfg) : |k A B| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H 2 specialUnitaryTwoWilsonRankPositive t ht A B
  have hRawL2 :
      ((Raw f : Phys) : Lp ℝ 2 haar) =
        realL2BoundedKernelIntegralOutputL2
          (μ := haar) k hMeas hBound (f : Lp ℝ 2 haar) := by
    change realL2HilbertSchmidtKernelOperator K2
        (f : Lp ℝ 2 haar) = _
    exact realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2
      (μ := haar) k K2 hKernel hMeas hBound (f : Lp ℝ 2 haar)
  have hInput :
      (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] ψ := by
    rw [hLp]
    exact ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hFiber (B : Cfg) :
      (∫ A : Cfg, k A B * ((f : Phys) : Lp ℝ 2 haar) A ∂haar) =
        ∫ A : Cfg, k A B * ψ A ∂haar := by
    apply integral_congr_ae
    filter_upwards [hInput] with A hA
    rw [hA]
  have hOutput :=
    realL2BoundedKernelIntegralOutputL2_coeFn
      (μ := haar) k hMeas hBound (f : Lp ℝ 2 haar)
  rw [hRawL2]
  filter_upwards [hOutput] with B hB
  exact hB.trans (hFiber B)

/-- The authentic Wilson kernel applied to a continuous physical
input, as a CONTINUOUS function of the right spatial boundary.
Bochner integration of the unchanged kernel's ContinuousMap curry
makes this a genuine, canonical C(Cfg,R) profile. -/
noncomputable def p4Q2PJ_originalKernelIntegralContinuous
    (ψ : C(Cfg, ℝ)) : C(Cfg, ℝ) :=
  let g : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => K p.1 p.2 * ψ p.1),
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H 2 t).mul (ψ.continuous.comp continuous_fst)⟩
  ∫ A : Cfg, g.curry A ∂haar

/-- The preceding continuous profile is POINTWISE the literal
original complete one-slab Wilson kernel integral. -/
theorem p4Q2PJ_originalKernelIntegralContinuous_apply
    (ψ : C(Cfg, ℝ)) (B : Cfg) :
    p4Q2PJ_originalKernelIntegralContinuous H t ψ B =
      ∫ A : Cfg, K A B * ψ A ∂haar := by
  let g : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => K p.1 p.2 * ψ p.1),
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H 2 t).mul (ψ.continuous.comp continuous_fst)⟩
  let v : C(Cfg, C(Cfg, ℝ)) := g.curry
  have hvInt : Integrable (fun A : Cfg => v A) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ A : Cfg, v A ∂haar) B = _
  rw [ContinuousMap.integral_apply hvInt B]
  rfl

/-- Exact pointwise literal ORIGINAL Wilson kernel formula for
the actual unnormalized physical transfer on ANY Gauss-law f
possessing a continuous spatial Haar representative ψ. -/
theorem p4Q2PJ_originalRawContinuous_pointwise_kernelIntegral
    (f : Phys) (ψ : C(Cfg, ℝ))
    (hLp : (f : Lp ℝ 2 haar) = L ψ)
    (B : Cfg) :
    p4Q2OU_originalPhysicalTransferContinuous H t ht f B =
      ∫ A : Cfg, K A B * ψ A ∂haar := by
  let φ : C(Cfg, ℝ) := p4Q2OU_originalPhysicalTransferContinuous H t ht f
  let g : C(Cfg, ℝ) := p4Q2PJ_originalKernelIntegralContinuous H t ψ
  have hOU :
      (fun X : Cfg => ((Raw f : Phys) : Lp ℝ 2 haar) X) =ᵐ[haar] φ := by
    rw [p4Q2OU_originalPhysicalTransferContinuous_toLp H t ht f]
    exact φ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hKernel :=
    p4Q2PJ_originalRawPhysical_ae_originalKernelIntegral H t ht f ψ hLp
  have hg :
      (fun X : Cfg => ((Raw f : Phys) : Lp ℝ 2 haar) X) =ᵐ[haar] g := by
    filter_upwards [hKernel] with X hX
    rw [p4Q2PJ_originalKernelIntegralContinuous_apply H t ψ X]
    exact hX
  have heq : (φ : Cfg → ℝ) = (g : Cfg → ℝ) :=
    MeasureTheory.Measure.eq_of_ae_eq (hOU.symm.trans hg)
      φ.continuous g.continuous
  change φ B = _
  rw [congrFun heq B]
  exact p4Q2PJ_originalKernelIntegralContinuous_apply H t ψ B

/-- Literal original complete Wilson kernel after TWO slabs.
The inner and outer Haar integrations use the SAME true spatial
product Haar, and EACH K is the original unmodified one-slab
Wilson action with both boundary halfweights. -/
noncomputable def p4Q2PJ_originalWilsonLiteralTwoSlabKernel (B : Cfg) : ℝ :=
  ∫ A : Cfg, ∫ X : Cfg, K A B * K X A ∂haar ∂haar

/-- EXACT original Wilson two-slab physical continuous profile,
pointwise on EVERY genuine spatial gauge configuration, equals
the literal double Haar integral of the SAME full Wilson kernel.
No surrogate Markov/posterior kernel is introduced. -/
theorem p4Q2PJ_originalRawTwoSlab_eq_literalDoubleWilsonKernel
    (B : Cfg) :
    p4Q2PI_originalRawTwoSlabContinuous H t ht B =
      p4Q2PJ_originalWilsonLiteralTwoSlabKernel H t B := by
  have hSource :
      ((Raw U : Phys) : Lp ℝ 2 haar) =
        L (p4Q2PI_originalRawOneSlabContinuous H t ht) := by
    simpa only [p4Q2PI_originalRawOneSlabContinuous] using
      (p4Q2OU_originalPhysicalTransferContinuous_toLp H t ht U)
  calc
    p4Q2PI_originalRawTwoSlabContinuous H t ht B =
        ∫ A : Cfg, K A B *
          p4Q2PI_originalRawOneSlabContinuous H t ht A ∂haar := by
      exact p4Q2PJ_originalRawContinuous_pointwise_kernelIntegral
        H t ht (Raw U) (p4Q2PI_originalRawOneSlabContinuous H t ht)
        hSource B
    _ = ∫ A : Cfg, K A B *
          (∫ X : Cfg, K X A ∂haar) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PI_originalRawOneSlab_eq_literalWilsonHaarRow H t ht A]
      rfl
    _ = p4Q2PJ_originalWilsonLiteralTwoSlabKernel H t B := by
      unfold p4Q2PJ_originalWilsonLiteralTwoSlabKernel
      apply integral_congr_ae
      filter_upwards with A
      rw [integral_const_mul]

/-- A 3-point determinant using ONLY literal integral values
from the ORIGINAL complete Wilson one-slab kernel and its true
two-slab double-Haar composition. -/
noncomputable def p4Q2PJ_originalWilsonLiteralThreeSpatialMinor
    (A B C : Cfg) : ℝ :=
  (p4Q2IV_originalWilsonUnitHaarKernelSection H t B -
      p4Q2IV_originalWilsonUnitHaarKernelSection H t A) *
    (p4Q2PJ_originalWilsonLiteralTwoSlabKernel H t C -
      p4Q2PJ_originalWilsonLiteralTwoSlabKernel H t A) -
  (p4Q2IV_originalWilsonUnitHaarKernelSection H t C -
      p4Q2IV_originalWilsonUnitHaarKernelSection H t A) *
    (p4Q2PJ_originalWilsonLiteralTwoSlabKernel H t B -
      p4Q2PJ_originalWilsonLiteralTwoSlabKernel H t A)

/-- EXACT equality of the original raw physical PI determinant and
the same determinant formed from the literal original Wilson
one- and two-slab Haar kernel integrals. -/
theorem p4Q2PJ_originalRawThreeSpatialMinor_eq_literalKernelMinor
    (A B C : Cfg) :
    p4Q2PI_originalRawThreeSpatialPointMinor H t ht A B C =
      p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H t A B C := by
  unfold p4Q2PI_originalRawThreeSpatialPointMinor
    p4Q2PJ_originalWilsonLiteralThreeSpatialMinor
  rw [p4Q2PI_originalRawOneSlab_eq_literalWilsonHaarRow H t ht A,
    p4Q2PI_originalRawOneSlab_eq_literalWilsonHaarRow H t ht B,
    p4Q2PI_originalRawOneSlab_eq_literalWilsonHaarRow H t ht C,
    p4Q2PJ_originalRawTwoSlab_eq_literalDoubleWilsonKernel H t ht A,
    p4Q2PJ_originalRawTwoSlab_eq_literalDoubleWilsonKernel H t ht B,
    p4Q2PJ_originalRawTwoSlab_eq_literalDoubleWilsonKernel H t ht C]

/-- PH/PI's physical third Wilson Hankel gap is positive iff
there is a nonzero literal three-configuration determinant formed
ENTIRELY from repeated integration of the original one-slab
Wilson Boltzmann kernel, under the independently proven D2>0 gate.
Existence of that triple remains open. -/
theorem p4Q2PJ_originalThirdMoment_pos_iff_exists_literalWilsonKernelMinor
    (hTwo : 0 < D2) :
    0 < D3 ↔
      ∃ A B C : Cfg,
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H t A B C ≠ 0 := by
  rw [p4Q2PI_originalThirdMoment_pos_iff_exists_rawSpatialMinor H t ht hTwo]
  constructor
  · rintro ⟨A, B, C, hRaw⟩
    refine ⟨A, B, C, ?_⟩
    rw [← p4Q2PJ_originalRawThreeSpatialMinor_eq_literalKernelMinor H t ht A B C]
    exact hRaw
  · rintro ⟨A, B, C, hLiteral⟩
    refine ⟨A, B, C, ?_⟩
    rw [p4Q2PJ_originalRawThreeSpatialMinor_eq_literalKernelMinor H t ht A B C]
    exact hLiteral

end OriginalTwoSlabLiteralSpatialKernel

section PositiveFrozenSmallFineLiteralWilsonKernel
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn

/-- The existing genuine positive-frozen original small-positive-fine
D2 interval makes D3>0 exactly equivalent to a nonzero determinant
of the same literal Wilson one-slab and double-Haar two-slab kernel.
No pointwise nonzero boundary triple has yet been constructed. -/
theorem p4Q2PJ_actualSmallFine_thirdMoment_pos_iff_exists_literalKernelMinor
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (0 < p4Q2PD_originalWilsonThirdMomentGap
            Hn (beta (n + 1)) (hbeta (n + 1)) ↔
          ∃ A B C : Cfg,
            p4Q2PJ_originalWilsonLiteralThreeSpatialMinor
              Hn (beta (n + 1)) A B C ≠ 0)) := by
  obtain ⟨delta, hdelta, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  exact p4Q2PJ_originalThirdMoment_pos_iff_exists_literalWilsonKernelMinor
    Hn (beta (n + 1)) (hbeta (n + 1)) (hTwo ht hsmall)

end PositiveFrozenSmallFineLiteralWilsonKernel

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawPhysical_ae_originalKernelIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalKernelIntegralContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawContinuous_pointwise_kernelIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawTwoSlab_eq_literalDoubleWilsonKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawThreeSpatialMinor_eq_literalKernelMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalThirdMoment_pos_iff_exists_literalWilsonKernelMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_actualSmallFine_thirdMoment_pos_iff_exists_literalKernelMinor

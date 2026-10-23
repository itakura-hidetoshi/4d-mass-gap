import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRawTwoSlabSpatialMinorV5_PI
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullOneSlabStrictTransferV5_LJ
import MGAP4D.MathlibAnalytic.RealL2BoundedKernelIntegralRepresentation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-PJ — original Wilson two-slab is the LITERAL double Haar kernel

PI proved exact normalized-to-raw determinant scaling and identified
the genuine one-slab OU continuous representative with the literal
spatial SU(2) Wilson Haar kernel row ∫ K_t(A,B) dHaar(A).

Here close the TWO-SLAB integral bridge in the ACTUAL physical Wilson
Gauss-law model, with its original positive spatial Wilson halfweights:
  G2(B) = ∫_A K_t(A,B) G1(A) dHaar(A)
        = ∫_A K_t(A,B) (∫_C K_t(C,A) dHaar(C)) dHaar(A).

First prove for EVERY authentic physical f that the physical raw
Wilson transfer is Haar-a.e. the literal kernel integral. Then
prove pointwise equality between OU's continuous true physical
transfer and the continuous integral kernel applied to any genuine
continuous Haar-L2 representative ψ of f. The pointwise step uses
only the original compact spatial SU(2) Haar full support.

Use these exact identities to identify PI's unnormalized two-step
spatial determinant with an entirely LITERAL one-/two-slab Haar
kernel determinant. In the original D2>0 physical interval:
  D3>0 iff EXISTS A,B,C with nonzero actual literal double-kernel minor.

NO nonzero triple is asserted; a future Taylor/character argument must
construct it. No replacement interaction, imaginary spectrum,
independent Haar posterior, Dobrushin, sorry/admit, new axiom,
volume-uniform U0 or 4D continuum Yang-Mills mass-gap claim.
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

local instance p4Q2PJ_spatialProductHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section OriginalWilsonTrueDoubleIntegral
variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 t
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Raw" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
local notation "D2" => p4Q2PD_originalWilsonTwoMomentDet H t ht
local notation "D3" => p4Q2PD_originalWilsonThirdMomentGap H t ht
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- The entire ORIGINAL unnormalized physical one-slab Wilson output
of ANY Gauss-law physical L2 input is represented almost everywhere
by the LITERAL original Haar kernel integral (not a Markov substitute). -/
theorem p4Q2PJ_originalRawPhysicalTransfer_literalKernelIntegral_ae
    (f : Phys) :
    (fun B : Cfg => ((Raw f : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar]
      (fun B : Cfg =>
        ∫ A : Cfg, K A B * ((f : Phys) : Lp ℝ 2 haar) A ∂haar) := by
  let k : Cfg → Cfg → ℝ := K
  let K2 : Lp ℝ 2 (Measure.prod haar haar) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H 2 specialUnitaryTwoWilsonRankPositive t ht
  let u : Lp ℝ 2 haar := (f : Phys)
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
  have hPhysical :
      ((Raw f : Phys) : Lp ℝ 2 haar) =
        realL2BoundedKernelIntegralOutputL2
          (μ := haar) k hMeas hBound u := by
    change realL2HilbertSchmidtKernelOperator K2 u = _
    exact realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2
      (μ := haar) k K2 hKernel hMeas hBound u
  have hOut :=
    realL2BoundedKernelIntegralOutputL2_coeFn
      (μ := haar) k hMeas hBound u
  change (fun B : Cfg => ((Raw f : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar] _
  rw [hPhysical]
  exact hOut

/-- The TRUE raw Wilson physical continuous output for a source f with
a continuous original-Haar representative ψ equals the genuine
one-slab spatial Wilson kernel integral at EVERY actual boundary. -/
theorem p4Q2PJ_originalRawContinuous_eq_literalKernelIntegral
    (f : Phys) (ψ : C(Cfg, ℝ))
    (hRep : ((f : Phys) : Lp ℝ 2 haar) = L ψ)
    (B : Cfg) :
    p4Q2OU_originalPhysicalTransferContinuous H t ht f B =
      ∫ A : Cfg, K A B * ψ A ∂haar := by
  let g : C(Cfg × Cfg, ℝ) := p4Q2LJ_originalFullWilsonOneSlabContinuous H t
  let c : C(Cfg, C(Cfg, ℝ)) := g.curry
  let weighted : Cfg → C(Cfg, ℝ) := fun A => ψ A • c A
  have hCont : Continuous weighted := ψ.continuous.smul c.continuous
  have hWeighted : Integrable weighted haar :=
    hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let F : C(Cfg, ℝ) := ∫ A : Cfg, weighted A ∂haar
  have hEval (X : Cfg) :
      F X = ∫ A : Cfg, K A X * ψ A ∂haar := by
    change (∫ A : Cfg, weighted A ∂haar) X = _
    rw [ContinuousMap.integral_apply hWeighted X]
    apply integral_congr_ae
    filter_upwards with A
    change ψ A * K A X = K A X * ψ A
    ring
  have hRawAE :=
    p4Q2PJ_originalRawPhysicalTransfer_literalKernelIntegral_ae H t ht f
  have hfAE :
      (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] ψ := by
    rw [hRep]
    exact ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hFiber (X : Cfg) :
      (∫ A : Cfg, K A X * ((f : Phys) : Lp ℝ 2 haar) A ∂haar) =
        ∫ A : Cfg, K A X * ψ A ∂haar := by
    apply integral_congr_ae
    filter_upwards [hfAE] with A hA
    rw [hA]
  have hLiteralAE :
      (fun X : Cfg => ((Raw f : Phys) : Lp ℝ 2 haar) X) =ᵐ[haar]
        (fun X : Cfg => ∫ A : Cfg, K A X * ψ A ∂haar) := by
    filter_upwards [hRawAE] with X hX
    exact hX.trans (hFiber X)
  have hFAE :
      (fun X : Cfg => ∫ A : Cfg, K A X * ψ A ∂haar) =ᵐ[haar] F := by
    filter_upwards with X
    exact (hEval X).symm
  have hOUAE :
      (fun X : Cfg => ((Raw f : Phys) : Lp ℝ 2 haar) X) =ᵐ[haar]
        p4Q2OU_originalPhysicalTransferContinuous H t ht f := by
    rw [p4Q2OU_originalPhysicalTransferContinuous_toLp H t ht f]
    exact
      (p4Q2OU_originalPhysicalTransferContinuous H t ht f).coeFn_toLp
        (p := 2) (𝕜 := ℝ) haar
  have hPointwise :
      (p4Q2OU_originalPhysicalTransferContinuous H t ht f : Cfg → ℝ) =
        (F : Cfg → ℝ) :=
    MeasureTheory.Measure.eq_of_ae_eq
      (hOUAE.symm.trans (hLiteralAE.trans hFAE))
      (p4Q2OU_originalPhysicalTransferContinuous H t ht f).continuous F.continuous
  exact (congrFun hPointwise B).trans (hEval B)

/-- The actual TWO-step unnormalized Wilson Gauss-law constant source
is a concrete one-slab kernel integral of the actual ONE-step profile. -/
theorem p4Q2PJ_originalRawTwoSlab_eq_kernelIntegral
    (B : Cfg) :
    p4Q2PI_originalRawTwoSlabContinuous H t ht B =
      ∫ A : Cfg, K A B *
        p4Q2PI_originalRawOneSlabContinuous H t ht A ∂haar := by
  have hRep :
      ((Raw U : Phys) : Lp ℝ 2 haar) =
        L (p4Q2PI_originalRawOneSlabContinuous H t ht) := by
    simpa only [p4Q2PI_originalRawOneSlabContinuous] using
      (p4Q2OU_originalPhysicalTransferContinuous_toLp H t ht U)
  exact p4Q2PJ_originalRawContinuous_eq_literalKernelIntegral
    H t ht (Raw U) (p4Q2PI_originalRawOneSlabContinuous H t ht) hRep B

/-- The actual TWO-step original physical Wilson transfer is literally
a TWO-FOLD Haar integral of the SAME unmodified positive SU(2) kernel. -/
theorem p4Q2PJ_originalRawTwoSlab_eq_literalDoubleHaar
    (B : Cfg) :
    p4Q2PI_originalRawTwoSlabContinuous H t ht B =
      ∫ A : Cfg, K A B *
        (∫ C : Cfg, K C A ∂haar) ∂haar := by
  rw [p4Q2PJ_originalRawTwoSlab_eq_kernelIntegral H t ht B]
  apply integral_congr_ae
  filter_upwards with A
  rw [p4Q2PI_originalRawOneSlab_eq_literalWilsonHaarRow H t ht A]
  rfl

/-- One-step original kernel Haar row on an actual physical spatial
boundary, with unchanged full Wilson crossing/spatial halfweights. -/
noncomputable def p4Q2PJ_literalOneSlabRow (B : Cfg) : ℝ :=
  ∫ A : Cfg, K A B ∂haar

/-- Two-step original kernel Haar row, exactly integrating over the
TRUE intermediate original spatial SU(2) boundary configuration. -/
noncomputable def p4Q2PJ_literalTwoSlabRow (B : Cfg) : ℝ :=
  ∫ A : Cfg, K A B *
    (∫ C : Cfg, K C A ∂haar) ∂haar

/-- The fully literal ORIGINAL spatial three-point determinant built
ONLY from one- and two-slab physical Wilson kernels and true Haar. -/
noncomputable def p4Q2PJ_literalWilsonDoubleHaarThreePointMinor
    (A B C : Cfg) : ℝ :=
  (p4Q2PJ_literalOneSlabRow H t B - p4Q2PJ_literalOneSlabRow H t A) *
    (p4Q2PJ_literalTwoSlabRow H t C - p4Q2PJ_literalTwoSlabRow H t A) -
  (p4Q2PJ_literalOneSlabRow H t C - p4Q2PJ_literalOneSlabRow H t A) *
    (p4Q2PJ_literalTwoSlabRow H t B - p4Q2PJ_literalTwoSlabRow H t A)

/-- PI's authentic raw physical three-point determinant equals exactly
the original single- and double-Wilson-kernel Haar determinant. -/
theorem p4Q2PJ_originalRawThreePointMinor_eq_literalDoubleHaar
    (A B C : Cfg) :
    p4Q2PI_originalRawThreeSpatialPointMinor H t ht A B C =
      p4Q2PJ_literalWilsonDoubleHaarThreePointMinor H t A B C := by
  unfold p4Q2PI_originalRawThreeSpatialPointMinor
    p4Q2PJ_literalWilsonDoubleHaarThreePointMinor
  have hOne (X : Cfg) :
      p4Q2PI_originalRawOneSlabContinuous H t ht X =
        p4Q2PJ_literalOneSlabRow H t X := by
    rw [p4Q2PI_originalRawOneSlab_eq_literalWilsonHaarRow H t ht X]
    rfl
  have hTwo (X : Cfg) :
      p4Q2PI_originalRawTwoSlabContinuous H t ht X =
        p4Q2PJ_literalTwoSlabRow H t X :=
    p4Q2PJ_originalRawTwoSlab_eq_literalDoubleHaar H t ht X
  rw [hOne A, hOne B, hOne C, hTwo A, hTwo B, hTwo C]

/-- EXACT physical D3>0 is equivalent, on the already-proved physical
D2>0 gate, to one truly NONZERO three-boundary determinant of the
LITERAL unmodified Wilson one-/two-slab Haar kernels. Its existence
is still the genuine missing analytic configuration witness. -/
theorem p4Q2PJ_originalThirdMoment_pos_iff_literalDoubleHaarMinor
    (hTwo : 0 < D2) :
    0 < D3 ↔
      ∃ A B C : Cfg,
        p4Q2PJ_literalWilsonDoubleHaarThreePointMinor H t A B C ≠ 0 := by
  rw [p4Q2PI_originalThirdMoment_pos_iff_exists_rawSpatialMinor H t ht hTwo]
  constructor
  · rintro ⟨A, B, C, hRaw⟩
    refine ⟨A, B, C, ?_⟩
    rw [← p4Q2PJ_originalRawThreePointMinor_eq_literalDoubleHaar H t ht A B C]
    exact hRaw
  · rintro ⟨A, B, C, hLiteral⟩
    refine ⟨A, B, C, ?_⟩
    rw [p4Q2PJ_originalRawThreePointMinor_eq_literalDoubleHaar H t ht A B C]
    exact hLiteral

end OriginalWilsonTrueDoubleIntegral

section SmallPositiveFineLiteralDoubleHaar
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn

/-- In the original frozen-positive physical small-fine two-mode
interval, the TRUE third Hankel determinant is positive iff ONE
actual spatial triple has nonzero literal double-Wilson Haar minor.
No nonzero triple is postulated or constructed. -/
theorem p4Q2PJ_actualSmallFine_thirdMoment_pos_iff_literalDoubleHaar
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (0 < p4Q2PD_originalWilsonThirdMomentGap
            Hn (beta (n + 1)) (hbeta (n + 1)) ↔
          ∃ A B C : Cfg,
            p4Q2PJ_literalWilsonDoubleHaarThreePointMinor
              Hn (beta (n + 1)) A B C ≠ 0)) := by
  obtain ⟨delta, hdelta, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  exact p4Q2PJ_originalThirdMoment_pos_iff_literalDoubleHaarMinor
    Hn (beta (n + 1)) (hbeta (n + 1)) (hTwo ht hsmall)

end SmallPositiveFineLiteralDoubleHaar

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawPhysicalTransfer_literalKernelIntegral_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawContinuous_eq_literalKernelIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawTwoSlab_eq_kernelIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawTwoSlab_eq_literalDoubleHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalRawThreePointMinor_eq_literalDoubleHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_originalThirdMoment_pos_iff_literalDoubleHaarMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PJ_actualSmallFine_thirdMoment_pos_iff_literalDoubleHaar

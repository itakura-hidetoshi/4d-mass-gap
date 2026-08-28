import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicity
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct ContinuousFunctionalCalculus CompactlySupported

noncomputable section

/-- A coercive self-adjoint bounded real-Hilbert endomorphism has positive
shift `G - gap I`.  This is the direct Hilbert-space form of the Loewner lower
bound and deliberately avoids requiring additive order typeclasses on the
endomorphism algebra. -/
theorem realContinuousLinearMap_sub_gap_smul_one_isPositive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (G : E →L[ℝ] E)
    (gap : ℝ)
    (hself : IsSelfAdjoint G)
    (hcoercive : ∀ u : E, gap * ‖u‖ ^ 2 ≤ inner ℝ (G u) u) :
    (G - gap • (1 : E →L[ℝ] E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff'
    (G - gap • (1 : E →L[ℝ] E))).2
  constructor
  · exact realContinuousLinearMap_sub_smul_one_isSelfAdjoint G hself gap
  · intro u
    change 0 ≤ inner ℝ (G u - gap • u) u
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hcoercive u]

/-- Fixed-vector quadratic evaluation after a real self-adjoint continuous
functional calculus, promoted to a positive linear functional on compactly
supported continuous spectral functions.

The positivity transport is an explicit hypothesis.  This is intentional:
pinned Mathlib supplies the required CFC/order package for complex C⋆-algebras,
but not for arbitrary real-Hilbert bounded endomorphisms. -/
noncomputable def realContinuousLinearMap_spectralQuadraticPositiveLinearMap
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (G : E →L[ℝ] E)
    (hself : IsSelfAdjoint G)
    (u : E)
    (hquadNonneg :
      ∀ f : C(spectrum ℝ G, ℝ),
        (∀ x, 0 ≤ f x) →
          0 ≤ inner ℝ ((cfcHom hself f) u) u) :
    C_c(spectrum ℝ G, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => inner ℝ ((cfcHom hself f.toContinuousMap) u) u
      map_add' := by
        intro f g
        have hfg :
            (f + g).toContinuousMap =
              f.toContinuousMap + g.toContinuousMap := by
          ext x
          rfl
        rw [hfg, map_add, ContinuousLinearMap.add_apply, inner_add_left]
      map_smul' := by
        intro c f
        have hcf :
            (c • f).toContinuousMap = c • f.toContinuousMap := by
          ext x
          rfl
        rw [hcf, map_smul, ContinuousLinearMap.smul_apply,
          real_inner_smul_left]
        simp only [RingHom.id_apply, smul_eq_mul] }
    (by
      intro f hf
      apply hquadNonneg f.toContinuousMap
      intro x
      exact hf x)

/-- The positive scalar spectral measure obtained by applying
Riesz--Markov--Kakutani to fixed-vector CFC quadratic evaluation. -/
noncomputable def realContinuousLinearMap_spectralQuadraticMeasure
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (G : E →L[ℝ] E)
    (hself : IsSelfAdjoint G)
    (u : E)
    (hquadNonneg :
      ∀ f : C(spectrum ℝ G, ℝ),
        (∀ x, 0 ≤ f x) →
          0 ≤ inner ℝ ((cfcHom hself f) u) u) :
    Measure (spectrum ℝ G) :=
  RealRMK.rieszMeasure
    (realContinuousLinearMap_spectralQuadraticPositiveLinearMap
      G hself u hquadNonneg)

/-- Riesz--Markov--Kakutani realizes every compactly supported continuous
spectral function as its fixed-vector CFC quadratic form. -/
theorem realContinuousLinearMap_integral_spectralQuadraticMeasure
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (G : E →L[ℝ] E)
    (hself : IsSelfAdjoint G)
    (u : E)
    (hquadNonneg :
      ∀ f : C(spectrum ℝ G, ℝ),
        (∀ x, 0 ≤ f x) →
          0 ≤ inner ℝ ((cfcHom hself f) u) u)
    (f : C_c(spectrum ℝ G, ℝ)) :
    ∫ x, f x ∂(realContinuousLinearMap_spectralQuadraticMeasure
        G hself u hquadNonneg) =
      inner ℝ ((cfcHom hself f.toContinuousMap) u) u := by
  exact
    RealRMK.integral_rieszMeasure
      (realContinuousLinearMap_spectralQuadraticPositiveLinearMap
        G hself u hquadNonneg) f

/-- Reciprocal spectral kernel below a known lower bound on the spectrum. -/
noncomputable def realContinuousLinearMap_spectralResolventKernel
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hspec : ∀ x ∈ spectrum ℝ G, gap ≤ x)
    (hlambda : lambda < gap) :
    C_c(spectrum ℝ G, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    { toFun := fun x : spectrum ℝ G => (x.1 - lambda)⁻¹
      continuous_toFun := by
        have hcont : Continuous (fun x : spectrum ℝ G => x.1 - lambda) :=
          continuous_subtype_val.sub continuous_const
        apply hcont.inv₀
        intro x
        have hx : lambda < x.1 :=
          lt_of_lt_of_le hlambda (hspec x.1 x.2)
        exact sub_ne_zero.mpr hx.ne' }

@[simp]
theorem realContinuousLinearMap_spectralResolventKernel_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hspec : ∀ x ∈ spectrum ℝ G, gap ≤ x)
    (hlambda : lambda < gap)
    (x : spectrum ℝ G) :
    realContinuousLinearMap_spectralResolventKernel
        G gap lambda hspec hlambda x =
      (x.1 - lambda)⁻¹ :=
  rfl

/-- The self-adjoint continuous functional calculus sends the reciprocal
kernel to the ring inverse of `G - lambda I`. -/
theorem realContinuousLinearMap_cfc_resolventKernel_eq_ringInverse
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hself : IsSelfAdjoint G)
    (hspec : ∀ x ∈ spectrum ℝ G, gap ≤ x)
    (hlambda : lambda < gap) :
    cfc (fun x : ℝ => (x - lambda)⁻¹) G =
      Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) := by
  have hshiftCont :
      ContinuousOn (fun x : ℝ => x - lambda) (spectrum ℝ G) :=
    (continuous_id.sub continuous_const).continuousOn
  have hnonzero : ∀ x ∈ spectrum ℝ G, x - lambda ≠ 0 := by
    intro x hx
    have hxlambda : lambda < x :=
      lt_of_lt_of_le hlambda (hspec x hx)
    exact sub_ne_zero.mpr hxlambda.ne'
  have hinv :=
    cfc_inv (fun x : ℝ => x - lambda) G hnonzero hshiftCont hself
  have hidCont : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ G) :=
    continuous_id.continuousOn
  have hconstCont :
      ContinuousOn (fun _ : ℝ => lambda) (spectrum ℝ G) :=
    continuous_const.continuousOn
  have hshift :
      cfc (fun x : ℝ => x - lambda) G =
        G - lambda • (1 : E →L[ℝ] E) := by
    calc
      cfc (fun x : ℝ => x - lambda) G =
          cfc (id : ℝ → ℝ) G - cfc (fun _ : ℝ => lambda) G := by
        simpa only [id_eq] using
          cfc_sub (id : ℝ → ℝ) (fun _ : ℝ => lambda) G
            hidCont hconstCont
      _ = G - algebraMap ℝ (E →L[ℝ] E) lambda := by
        rw [cfc_id ℝ G hself, cfc_const lambda G hself]
      _ = G - lambda • (1 : E →L[ℝ] E) := by
        rw [Algebra.algebraMap_eq_smul_one]
  rw [hshift] at hinv
  exact hinv

/-- Abstract Stieltjes representation of a fixed-vector resolvent below a
known spectral lower bound.  The only positivity input is the explicit
quadratic positivity of the real CFC on nonnegative spectral functions. -/
theorem realContinuousLinearMap_resolventQuadratic_eq_stieltjesIntegral
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hself : IsSelfAdjoint G)
    (hspec : ∀ x ∈ spectrum ℝ G, gap ≤ x)
    (hlambda : lambda < gap)
    (u : E)
    (hquadNonneg :
      ∀ f : C(spectrum ℝ G, ℝ),
        (∀ x, 0 ≤ f x) →
          0 ≤ inner ℝ ((cfcHom hself f) u) u) :
    inner ℝ (Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) u) u =
      ∫ x : spectrum ℝ G, (x.1 - lambda)⁻¹
        ∂(realContinuousLinearMap_spectralQuadraticMeasure
          G hself u hquadNonneg) := by
  let k :=
    realContinuousLinearMap_spectralResolventKernel
      G gap lambda hspec hlambda
  have hRMK :=
    realContinuousLinearMap_integral_spectralQuadraticMeasure
      G hself u hquadNonneg k
  have hcfc :
      cfc (fun x : ℝ => (x - lambda)⁻¹) G =
        Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) :=
    realContinuousLinearMap_cfc_resolventKernel_eq_ringInverse
      G gap lambda hself hspec hlambda
  have hkernelCont :
      ContinuousOn (fun x : ℝ => (x - lambda)⁻¹) (spectrum ℝ G) := by
    have hbase :
        ContinuousOn (fun x : ℝ => x - lambda) (spectrum ℝ G) :=
      (continuous_id.sub continuous_const).continuousOn
    apply hbase.inv₀
    intro x hx
    have hxlambda : lambda < x :=
      lt_of_lt_of_le hlambda (hspec x hx)
    exact sub_ne_zero.mpr hxlambda.ne'
  have hkCFC :
      cfcHom hself k.toContinuousMap =
        Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) := by
    calc
      cfcHom hself k.toContinuousMap =
          cfcHom hself
            ⟨fun x : spectrum ℝ G => (x.1 - lambda)⁻¹,
              hkernelCont.restrict⟩ := by
        congr 1
      _ = cfc (fun x : ℝ => (x - lambda)⁻¹) G :=
        (cfc_apply (fun x : ℝ => (x - lambda)⁻¹) G
          hself hkernelCont).symm
      _ = Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) := hcfc
  rw [hkCFC] at hRMK
  simpa [k] using hRMK.symm

local instance osBoundaryExcitationCompletedSpectralStieltjesSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedSpectralStieltjesSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedSpectralStieltjesSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedSpectralStieltjesSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedSpectralStieltjesSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedSpectralStieltjesSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedSpectralStieltjesSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedSpectralStieltjesPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The completed finite-volume one-step generator shifted by its explicit gap
is a positive bounded real-Hilbert operator.  This is unconditional and uses
only the already-proved self-adjointness and coercive lower bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_sub_gap_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta -
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta •
        (1 :
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta →L[ℝ]
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta)).IsPositive := by
  exact
    realContinuousLinearMap_sub_gap_smul_one_isPositive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_isSelfAdjoint
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_lower_bound
        H N hN beta hbeta)

/-- The real spectrum of the completed finite-volume one-step generator lies
above the explicit gap.  This is proved directly from the already-established
below-gap resolvent-set theorem, so it does not require a real CFC instance. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_ge_gap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ x ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta ≤ x := by
  intro x hx
  by_contra hge
  have hlt :
      x <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta :=
    lt_of_not_ge hge
  have hres :
      x ∈ resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_lt_gap
      H N hN beta hbeta x hlt
  change
    x ∉ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta) at hx
  exact hx hres

/-- Audit-visible unconditional real spectral-support package for the completed
finite-volume generator. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedRealSpectralSupportPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  shiftedGeneratorPositive :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta -
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta •
        (1 :
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta →L[ℝ]
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta)).IsPositive
  realSpectrumAboveGap :
    ∀ x ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta ≤ x

/-- Construct the unconditional completed real spectral-support package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedRealSpectralSupportPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedRealSpectralSupportPackage
      H N hN beta hbeta :=
  { shiftedGeneratorPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_sub_gap_isPositive
        H N hN beta hbeta
    realSpectrumAboveGap :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_ge_gap
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D

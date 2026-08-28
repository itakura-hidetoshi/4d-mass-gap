import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicity
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct ContinuousFunctionalCalculus CompactlySupported

noncomputable section

/-- A self-adjoint bounded real-Hilbert endomorphism whose quadratic form is
bounded below by `gap` is above `gap I` in the Loewner order.  This is the
order-theoretic form of coercivity needed for spectral support. -/
theorem realContinuousLinearMap_algebraMap_le_of_inner_lower_bound
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (G : E →L[ℝ] E)
    (gap : ℝ)
    (hself : IsSelfAdjoint G)
    (hcoercive : ∀ u : E, gap * ‖u‖ ^ 2 ≤ inner ℝ (G u) u) :
    algebraMap ℝ (E →L[ℝ] E) gap ≤ G := by
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive]
  apply (ContinuousLinearMap.isPositive_iff'
    (G - algebraMap ℝ (E →L[ℝ] E) gap)).2
  constructor
  · rw [Algebra.algebraMap_eq_smul_one]
    exact realContinuousLinearMap_sub_smul_one_isSelfAdjoint G hself gap
  · intro u
    rw [Algebra.algebraMap_eq_smul_one]
    change 0 ≤ inner ℝ (G u - gap • u) u
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hcoercive u]

/-- Whenever a real self-adjoint continuous functional calculus is available,
coercivity localizes the real spectrum to `[gap, ∞)`.  The theorem is stated
with the calculus as an explicit typeclass parameter because pinned Mathlib
currently has no such instance for general real-Hilbert bounded endomorphisms. -/
theorem realContinuousLinearMap_spectrum_ge_of_inner_lower_bound
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (E →L[ℝ] E)]
    (G : E →L[ℝ] E)
    (gap : ℝ)
    (hself : IsSelfAdjoint G)
    (hcoercive : ∀ u : E, gap * ‖u‖ ^ 2 ≤ inner ℝ (G u) u) :
    ∀ x ∈ spectrum ℝ G, gap ≤ x := by
  exact
    (algebraMap_le_iff_le_spectrum hself).1
      (realContinuousLinearMap_algebraMap_le_of_inner_lower_bound
        G gap hself hcoercive)

/-- Fixed-vector quadratic evaluation after the self-adjoint continuous
functional calculus, regarded as a positive linear functional on compactly
supported continuous functions on the spectrum. -/
noncomputable def realContinuousLinearMap_spectralQuadraticPositiveLinearMap
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (E →L[ℝ] E)]
    (G : E →L[ℝ] E)
    (hself : IsSelfAdjoint G)
    (u : E) :
    C_c(spectrum ℝ G, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => inner ℝ ((cfcHom hself f.toContinuousMap) u) u
      map_add' := by
        intro f g
        rw [map_add, ContinuousLinearMap.add_apply, inner_add_left]
      map_smul' := by
        intro c f
        rw [map_smul, ContinuousLinearMap.smul_apply, real_inner_smul_left]
        rfl }
    (by
      intro f hf
      have hf' : 0 ≤ f.toContinuousMap := by
        intro x
        exact hf x
      have hcfc : 0 ≤ cfcHom hself f.toContinuousMap :=
        (cfcHom_nonneg_iff hself).2 hf'
      have hpositive :
          (cfcHom hself f.toContinuousMap : E →L[ℝ] E).IsPositive :=
        (ContinuousLinearMap.nonneg_iff_isPositive _).mp hcfc
      exact hpositive.inner_nonneg_left u)

/-- The positive finite scalar spectral measure furnished by
Riesz--Markov--Kakutani from fixed-vector quadratic CFC evaluation. -/
noncomputable def realContinuousLinearMap_spectralQuadraticMeasure
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (E →L[ℝ] E)]
    (G : E →L[ℝ] E)
    (hself : IsSelfAdjoint G)
    (u : E) :
    Measure (spectrum ℝ G) :=
  RealRMK.rieszMeasure
    (realContinuousLinearMap_spectralQuadraticPositiveLinearMap G hself u)

/-- Riesz--Markov--Kakutani realizes every compactly supported continuous
spectral function as its fixed-vector CFC quadratic form. -/
theorem realContinuousLinearMap_integral_spectralQuadraticMeasure
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (E →L[ℝ] E)]
    (G : E →L[ℝ] E)
    (hself : IsSelfAdjoint G)
    (u : E)
    (f : C_c(spectrum ℝ G, ℝ)) :
    ∫ x, f x ∂(realContinuousLinearMap_spectralQuadraticMeasure G hself u) =
      inner ℝ ((cfcHom hself f.toContinuousMap) u) u := by
  simpa only [realContinuousLinearMap_spectralQuadraticMeasure,
    realContinuousLinearMap_spectralQuadraticPositiveLinearMap] using
    (RealRMK.integral_rieszMeasure
      (realContinuousLinearMap_spectralQuadraticPositiveLinearMap G hself u) f)

/-- Reciprocal spectral kernel below a known spectral lower bound. -/
noncomputable def realContinuousLinearMap_spectralResolventKernel
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (E →L[ℝ] E)]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hspec : ∀ x ∈ spectrum ℝ G, gap ≤ x)
    (hlambda : lambda < gap) :
    C_c(spectrum ℝ G, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    { toFun := fun x : spectrum ℝ G => (x.1 - lambda)⁻¹
      continuous_toFun := by
        have hcont : Continuous (fun x : spectrum ℝ G => x.1 - lambda) :=
          continuous_sub continuous_subtype_val continuous_const
        apply hcont.inv₀
        intro x
        have hx : lambda < x.1 := lt_of_lt_of_le hlambda (hspec x.1 x.2)
        exact sub_ne_zero.mpr hx.ne' }

@[simp]
theorem realContinuousLinearMap_spectralResolventKernel_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (E →L[ℝ] E)]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hspec : ∀ x ∈ spectrum ℝ G, gap ≤ x)
    (hlambda : lambda < gap)
    (x : spectrum ℝ G) :
    realContinuousLinearMap_spectralResolventKernel G gap lambda hspec hlambda x =
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
    [NonnegSpectrumClass ℝ (E →L[ℝ] E)]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hself : IsSelfAdjoint G)
    (hspec : ∀ x ∈ spectrum ℝ G, gap ≤ x)
    (hlambda : lambda < gap) :
    cfc (fun x : ℝ => (x - lambda)⁻¹) G =
      Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) := by
  have hshiftCont :
      ContinuousOn (fun x : ℝ => x - lambda) (spectrum ℝ G) := by
    fun_prop
  have hnonzero : ∀ x ∈ spectrum ℝ G, x - lambda ≠ 0 := by
    intro x hx
    have hxlambda : lambda < x := lt_of_lt_of_le hlambda (hspec x hx)
    exact sub_ne_zero.mpr hxlambda.ne'
  have hinv :=
    cfc_inv (fun x : ℝ => x - lambda) G hnonzero hshiftCont hself
  have hshift :
      cfc (fun x : ℝ => x - lambda) G =
        G - lambda • (1 : E →L[ℝ] E) := by
    calc
      cfc (fun x : ℝ => x - lambda) G =
          cfc (id : ℝ → ℝ) G - cfc (fun _ : ℝ => lambda) G := by
        simpa only [id_eq] using
          cfc_sub (id : ℝ → ℝ) (fun _ : ℝ => lambda) G
      _ = G - algebraMap ℝ (E →L[ℝ] E) lambda := by
        rw [cfc_id ℝ G hself, cfc_const lambda G hself]
      _ = G - lambda • (1 : E →L[ℝ] E) := by
        rw [Algebra.algebraMap_eq_smul_one]
  rw [hshift] at hinv
  exact hinv

/-- Abstract Stieltjes representation of a fixed-vector below-spectrum
resolvent quadratic form. -/
theorem realContinuousLinearMap_resolventQuadratic_eq_stieltjesIntegral
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (E →L[ℝ] E)]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hself : IsSelfAdjoint G)
    (hspec : ∀ x ∈ spectrum ℝ G, gap ≤ x)
    (hlambda : lambda < gap)
    (u : E) :
    inner ℝ (Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) u) u =
      ∫ x : spectrum ℝ G, (x.1 - lambda)⁻¹
        ∂(realContinuousLinearMap_spectralQuadraticMeasure G hself u) := by
  let k := realContinuousLinearMap_spectralResolventKernel G gap lambda hspec hlambda
  have hRMK :=
    realContinuousLinearMap_integral_spectralQuadraticMeasure G hself u k
  have hcfc :
      cfc (fun x : ℝ => (x - lambda)⁻¹) G =
        Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) :=
    realContinuousLinearMap_cfc_resolventKernel_eq_ringInverse
      G gap lambda hself hspec hlambda
  have hkCFC :
      cfcHom hself k.toContinuousMap =
        Ring.inverse (G - lambda • (1 : E →L[ℝ] E)) := by
    rw [← hcfc]
    rw [cfc_apply (fun x : ℝ => (x - lambda)⁻¹) G]
    congr 1
    ext x
    rfl
  rw [hkCFC] at hRMK
  simpa [k] using hRMK.symm

/-- The completed finite-volume one-step generator is above its explicit gap
in the Loewner order.  This statement uses only the already-proved coercive
quadratic lower bound and does not assume a spectral theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_gap_algebraMap_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    algebraMap ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            H N hN beta hbeta →L[ℝ]
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta := by
  exact
    realContinuousLinearMap_algebraMap_le_of_inner_lower_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_isSelfAdjoint
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_lower_bound
        H N hN beta hbeta)

/-- Explicit interface describing the sole missing library bridge for applying
Riesz--Markov spectral measure construction directly to the completed real
Hilbert generator.  Once a real self-adjoint continuous functional calculus
and its nonnegative-spectrum class are supplied for the completed bounded
endomorphism algebra, the abstract Stieltjes theorem above specializes with no
new mathematical hypothesis on the generator itself. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedRealSpectralCalculusBridge
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  realCFC :
    ContinuousFunctionalCalculus ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
      IsSelfAdjoint
  nonnegativeRealSpectrum :
    @NonnegSpectrumClass ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
      _ _ _ _ _ _ _ _ _

end

end MathlibAnalytic
end MGAP4D

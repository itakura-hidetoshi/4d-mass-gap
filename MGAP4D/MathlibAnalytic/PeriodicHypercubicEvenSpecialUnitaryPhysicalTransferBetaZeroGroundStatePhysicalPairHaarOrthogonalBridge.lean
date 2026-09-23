import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroExactTransferGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarProjection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic

/-!
# Beta-zero physical-to-pair-Haar boundary orthogonality bridge

This file isolates the remaining endpoint bridge between the genuine physical
beta-zero top-orthogonal sector and the literal pair-Haar boundary carrier.

The construction is deliberately kept on the literal product-Haar carrier.
The proof-indexed ground-state carrier is transported only in a later theorem
unit.  This keeps dependent `Lp` rewriting out of the Hilbert geometry.

The new input is a general product-probability lemma:

* a right-coordinate-measurable real `L²` vector with zero mean is orthogonal
  to the complete left-coordinate `L²` subspace.

For the Wilson endpoint, physical top-orthogonality gives zero Haar mean.
The literal right-boundary pullback is an isometry and preserves the
constant-one vector, hence it preserves this zero-mean condition.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- On a product probability space, a right-coordinate-measurable real `L²`
vector with zero mean lies in the orthogonal complement of the complete
left-coordinate measurable `L²` subspace. -/
theorem realL2_product_snd_mean_zero_mem_fst_orthogonal
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (f : Lp ℝ 2 (μ.prod ν))
    (hf_snd :
      f ∈ lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace β))
        2 (μ.prod ν))
    (hf_mean : (∫ z, f z ∂(μ.prod ν)) = 0) :
    f ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace α))
        2 (μ.prod ν))ᗮ := by
  let mFst : MeasurableSpace (α × β) :=
    MeasurableSpace.comap Prod.fst
      (inferInstance : MeasurableSpace α)
  let mSnd : MeasurableSpace (α × β) :=
    MeasurableSpace.comap Prod.snd
      (inferInstance : MeasurableSpace β)
  have hleFst :
      mFst ≤ (inferInstance : MeasurableSpace (α × β)) := by
    simpa only [mFst] using
      (measurable_fst.comap_le :
        MeasurableSpace.comap Prod.fst
            (inferInstance : MeasurableSpace α) ≤
          (inferInstance : MeasurableSpace (α × β)))
  have hleSnd :
      mSnd ≤ (inferInstance : MeasurableSpace (α × β)) := by
    simpa only [mSnd] using
      (measurable_snd.comap_le :
        MeasurableSpace.comap Prod.snd
            (inferInstance : MeasurableSpace β) ≤
          (inferInstance : MeasurableSpace (α × β)))
  have hfSnd :
      AEStronglyMeasurable[mSnd] (f : α × β → ℝ) (μ.prod ν) := by
    exact mem_lpMeas_iff_aestronglyMeasurable.mp hf_snd
  let g : α × β → ℝ := hfSnd.mk f
  have hfg : (f : α × β → ℝ) =ᵐ[μ.prod ν] g := by
    exact hfSnd.ae_eq_mk
  have hgSnd : StronglyMeasurable[mSnd] g := by
    exact hfSnd.stronglyMeasurable_mk
  have hgLp : MemLp g 2 (μ.prod ν) := by
    exact (memLp_congr_ae hfg).1 (Lp.memLp f)
  have hIndepFstSnd : Indep mFst mSnd (μ.prod ν) := by
    change IndepFun Prod.fst Prod.snd (μ.prod ν)
    simpa using
      (indepFun_prod
        (μ := μ) (ν := ν) (X := id) (Y := id)
        measurable_id measurable_id)
  have hCond :
      (μ.prod ν)[g | mFst] =ᵐ[μ.prod ν]
        fun _ => ∫ z, g z ∂(μ.prod ν) := by
    exact
      condExp_indep_eq
        (m₁ := mSnd)
        (m₂ := mFst)
        (m := (inferInstance : MeasurableSpace (α × β)))
        (μ := μ.prod ν)
        hleSnd hleFst hgSnd hIndepFstSnd.symm
  have hgMean : (∫ z, g z ∂(μ.prod ν)) = 0 := by
    calc
      (∫ z, g z ∂(μ.prod ν)) =
          ∫ z, f z ∂(μ.prod ν) := integral_congr_ae hfg.symm
      _ = 0 := hf_mean
  have hCondZero :
      (μ.prod ν)[g | mFst] =ᵐ[μ.prod ν] (fun _ => (0 : ℝ)) := by
    exact hCond.trans <|
      Filter.Eventually.of_forall fun _ => by simp [hgMean]
  have hToLp : hgLp.toLp g = f := by
    apply Lp.ext
    exact hgLp.coeFn_toLp.trans hfg.symm
  have hCondL2 :
      (condExpL2 ℝ ℝ hleFst (hgLp.toLp g) :
          α × β → ℝ) =ᵐ[μ.prod ν]
        (μ.prod ν)[g | mFst] := by
    exact
      MemLp.condExpL2_ae_eq_condExp
        (m₀ := (inferInstance : MeasurableSpace (α × β)))
        (m := mFst)
        (μ := μ.prod ν)
        (f := g)
        (𝕜 := ℝ)
        hleFst hgLp
  have hProjectionAE :
      (condExpL2 ℝ ℝ hleFst f :
          α × β → ℝ) =ᵐ[μ.prod ν] (fun _ => (0 : ℝ)) := by
    rw [← hToLp]
    exact hCondL2.trans hCondZero
  have hProjectionZero :
      condExpL2 ℝ ℝ hleFst f = 0 := by
    apply Subtype.ext
    apply Lp.ext
    simpa using hProjectionAE
  rw [← Submodule.orthogonalProjection_eq_zero_iff]
  simpa [condExpL2] using hProjectionZero

local instance betaZeroPhysicalPairHaarBridgeTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroPhysicalPairHaarBridgeCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroPhysicalPairHaarBridgeSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroPhysicalPairHaarBridgeMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroPhysicalPairHaarBridgeBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroPhysicalPairHaarBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal beta-zero right-boundary pullback from one-slice Haar `L²` into
pair-Haar `L²`.  This is kept independent of the proof-indexed ground-state
carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
    (H N : ℕ) :
    Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
        H N := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod μ)
  exact
    Lp.compMeasurePreservingₗᵢ ℝ Prod.snd
      (MeasureTheory.measurePreserving_snd (μ := μ) (ν := μ))

/-- The literal beta-zero right-boundary pullback is measurable with respect
to the right-coordinate sigma-algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundary_mem_snd_lpMeas
    (H N : ℕ)
    (f :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
        H N f ∈
      lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  have hfMap :
      AEStronglyMeasurable
        (f :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
        (Measure.map Prod.snd (μ.prod μ)) := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact Lp.aestronglyMeasurable f
  have hComp :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
        ((fun A => f A) ∘ Prod.snd) (μ.prod μ) :=
    AEStronglyMeasurable.comp_ae_measurable'
      hfMap measurable_snd.aemeasurable
  have hPull :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
          H N f =ᵐ[μ.prod μ]
        fun z => f z.2 := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      Function.comp_def, μ] using
      (Lp.coeFn_compMeasurePreserving f
        (MeasureTheory.measurePreserving_snd (μ := μ) (ν := μ)))
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure, μ] using
    hComp.congr hPull.symm

/-- The literal beta-zero right-boundary pullback preserves the constant-one
vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundary_const_one
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
        H N
        (Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
          (1 : ℝ)) =
      Lp.const 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (1 : ℝ) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let oneHaar : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  have hPull :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
          H N oneHaar =ᵐ[μ.prod μ]
        fun z => oneHaar z.2 := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      Function.comp_def, oneHaar, μ] using
      (Lp.coeFn_compMeasurePreserving oneHaar
        (MeasureTheory.measurePreserving_snd (μ := μ) (ν := μ)))
  have hOneBase :
      (fun z => oneHaar z.2) =ᵐ[μ.prod μ] (fun _ => (1 : ℝ)) := by
    have hOne :=
      Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))
    simpa [Function.comp_def, oneHaar] using
      hOne.comp_tendsto
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).tendsto_ae
  have hOnePair :
      (Lp.const 2 (μ.prod μ) (1 : ℝ) : _ → ℝ) =ᵐ[μ.prod μ]
        fun _ => (1 : ℝ) :=
    Lp.coeFn_const (μ := μ.prod μ) (p := 2) (c := (1 : ℝ))
  apply Lp.ext
  simpa [
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
    oneHaar, μ] using
    hPull.trans (hOneBase.trans hOnePair.symm)

/-- Endpoint bridge on the literal carrier: every genuine physical beta-zero
top-orthogonal vector, pulled to the right coordinate of pair Haar, lies in the
orthogonal complement of the complete left-boundary `L²` sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundary_topOrthogonal_mem_fst_orthogonal
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
        H N
        (((x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))ᗮ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let f : Lp ℝ 2 μ :=
    ((x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) :
      Lp ℝ 2 μ)
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
      H N
  have hfInner :
      inner ℝ (Lp.const 2 μ (1 : ℝ)) f = 0 := by
    simpa [μ, f,
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal_zero_inner_constantUnit
        H N hN x)
  have hRInner :
      inner ℝ
        (Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
          (1 : ℝ))
        (R f) = 0 := by
    calc
      inner ℝ
          (Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ))
          (R f) =
        inner ℝ (R (Lp.const 2 μ (1 : ℝ))) (R f) := by
          rw [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundary_const_one
              H N]
      _ = inner ℝ (Lp.const 2 μ (1 : ℝ)) f := by
        exact R.inner_map_map _ _
      _ = 0 := hfInner
  have hRMean :
      (∫ z, R f z
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) = 0 := by
    rw [← realL2_inner_const_one_eq_integral]
    exact hRInner
  have hRSnd :
      R f ∈
        lpMeas ℝ ℝ
          (MeasurableSpace.comap Prod.snd
            (inferInstance : MeasurableSpace
              (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
          2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundary_mem_snd_lpMeas
        H N f
  simpa [
    R, f, μ,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
    (realL2_product_snd_mean_zero_mem_fst_orthogonal
      μ μ (R f) hRSnd hRMean)

end

end MGAP4D.MathlibAnalytic

import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5HalfWeightCrossingGramStrict
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonEnergySU2ContinuousTwoModeTraceSpan
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeFeatureKernelResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabTransferRawIntegral
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
# Positive-coupling SU(2) no-go theorem for completed H1-D5

PR #5058 proves strict positivity of the exact half-weight temporal-crossing
quadratic form for every nonzero finite primary normalized-trace polynomial.
PR #5059 identifies the continuous SU(2) Wilson two-mode carrier with the
literal trace span `span {1,r}`.

This file closes the remaining finite-dimensional bridge:

* every nonzero vector in the physical SU(2) two-mode span has a nonzero
  degree-one normalized-trace polynomial representative;
* its physical one-slab quadratic form is exactly the #5058 half-weight
  crossing quadratic form;
* therefore the physical feature-analysis operator has trivial kernel on the
  two-mode span at strictly positive coupling;
* the #5045/#5044/#5043 chain then refutes the old completed H1-D5
  compatibility.

No Gram--Schmidt coefficients are computed explicitly.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

private theorem h1d5SU2NoGoRankPositive : 0 < (2 : ℕ) := by
  norm_num

private theorem h1d5SU2NoGoRankTwo : 2 ≤ (2 : ℕ) := by
  norm_num

local instance h1d5SU2NoGoNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance h1d5SU2NoGoTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance h1d5SU2NoGoCompactGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance h1d5SU2NoGoSecondCountableGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance h1d5SU2NoGoMeasurableGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance h1d5SU2NoGoBorelGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance h1d5SU2NoGoSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5SU2NoGoSpatialHaarProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The canonical primary-spatial plaquette holonomy as a continuous map into
SU(2). -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomyTwoContinuous
    (H : ℕ) :
    C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨fun A =>
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialSlicePlaquette H),
    by
      unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      fun_prop⟩

/-- Continuous one-slice representative of the chosen SU(2) Wilson two-mode
physical vector. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
    (H : ℕ)
    (k : Fin 2) :
    C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ) :=
  (specialUnitaryWilsonContinuousTwoMode h1d5SU2NoGoRankTwo k).comp
    (periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomyTwoContinuous H)

/-- The physical one-slice L2 mode is exactly the L2 class of its chosen
continuous plaquette representative. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_eq_toLp_continuousRepresentative
    (H : ℕ)
    (k : Fin 2) :
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H h1d5SU2NoGoRankTwo k :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
          H k) := by
  apply Lp.ext
  have hphysical :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_coeFn
      H h1d5SU2NoGoRankTwo k
  have hcontinuous :=
    ContinuousMap.coeFn_toLp
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
        H k)
  filter_upwards [hphysical, hcontinuous] with A hphysicalA hcontinuousA
  calc
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H h1d5SU2NoGoRankTwo k :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) A =
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable
          H h1d5SU2NoGoRankTwo k A := hphysicalA
    _ =
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
          H k A := by
          rfl
    _ =
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
            H k)) A := hcontinuousA.symm

/-- Pulling a literal SU(2) trace-seed linear combination to the primary
plaquette gives exactly the degree-one one-slice normalized-trace polynomial. -/
theorem
    specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed_primarySpatialSlice_eq_polynomial
    (H : ℕ)
    (c : Fin 2 → ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∑ j : Fin 2, c j • specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed j)
        (periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomyTwoContinuous H A) =
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H 1 c A := by
  simp [
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial,
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous,
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyTwoContinuous,
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomyTwoContinuous,
    specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed,
    specialUnitaryWilsonPlaquetteEnergyContinuous,
    Fin.sum_univ_two
  ]

/-- Every nonzero vector in the physical SU(2) two-mode span has a nonzero
literal degree-one normalized-trace polynomial representative. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceSU2TwoModePhysicalSpan_exists_nonzero_normalizedTracePolynomial
    (H : ℕ)
    (x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (hxSpan :
      x ∈ periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalSpan
        H 2 h1d5SU2NoGoRankTwo)
    (hxne : x ≠ 0) :
    ∃ c : Fin 2 → ℝ,
      c ≠ 0 ∧
      (x :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H 1 c) := by
  let G :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  change
    x ∈ Submodule.span ℝ
      (Set.range
        (fun k : Fin 2 =>
          periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
            H h1d5SU2NoGoRankTwo k)) at hxSpan
  obtain ⟨b, hb⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hxSpan
  let q : C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ) :=
    ∑ k : Fin 2, b k •
      specialUnitaryWilsonContinuousTwoMode h1d5SU2NoGoRankTwo k
  have hqMem :
      q ∈ Submodule.span ℝ
        (Set.range
          (specialUnitaryWilsonContinuousTwoMode h1d5SU2NoGoRankTwo)) := by
    apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
    exact ⟨b, rfl⟩
  rw [specialUnitaryWilsonContinuousTwoMode_two_span_eq_normalizedTraceSeed] at hqMem
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hqMem
  have hSpatial :
      (∑ k : Fin 2, b k •
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
          H k) =
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H 1 c := by
    ext A
    have heval :=
      congrArg
        (fun f : C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ) =>
          f (periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomyTwoContinuous H A))
        hc
    calc
      (∑ k : Fin 2, b k •
          periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
            H k) A =
        q (periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomyTwoContinuous H A) := by
          simp [q,
            periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative]
      _ =
        (∑ j : Fin 2,
          c j • specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed j)
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomyTwoContinuous H A) :=
          heval.symm
      _ =
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H 1 c A :=
          specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed_primarySpatialSlice_eq_polynomial
            H c A
  have hbLp :
      (∑ k : Fin 2,
        b k •
          ((periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
              H h1d5SU2NoGoRankTwo k :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))) =
        (x :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
    have hb' := congrArg
      (fun y :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 =>
          G.subtypeL y)
      hb
    simpa [G] using hb'
  have hxLp :
      (x :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H 1 c) := by
    calc
      (x :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        ∑ k : Fin 2,
          b k •
            ((periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
                H h1d5SU2NoGoRankTwo k :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) :=
          hbLp.symm
      _ =
        ∑ k : Fin 2,
          b k •
            ContinuousMap.toLp
              (E := ℝ) 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
              (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
                H k) := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [
            periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_eq_toLp_continuousRepresentative
              H k]
      _ =
        ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (∑ k : Fin 2,
            b k •
              periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalContinuousRepresentative
                H k) := by
          symm
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [map_smul]
      _ =
        ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H 1 c) := by
          rw [hSpatial]
  have hcne : c ≠ 0 := by
    intro hc0
    have hp0 :
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H 1 c = 0 := by
      simp [hc0, periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial]
    apply hxne
    apply Subtype.ext
    have hxLp0 :
        (x :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
      rw [hxLp, hp0]
      simp
    exact hxLp0
  exact ⟨c, hcne, hxLp⟩

/-- If a physical SU(2) vector is represented by a continuous one-slice
function p, its physical one-slab quadratic form is exactly the bare temporal
crossing quadratic form under the positive half-weight endpoint measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPhysicalOneSlabTransfer_quadratic_eq_halfWeightCrossing_of_eq_toLp
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (p :
      C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))
    (hxp :
      (x :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ p) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 h1d5SU2NoGoRankPositive beta hbeta x)
        x =
      ∫ A₁, ∫ A₂,
        p A₁ * p A₂ *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A₁ A₂
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let ν :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta
  let w :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H 2 beta
  letI hfin : IsFiniteMeasure ν := by
    dsimp [ν]
    exact
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_isFiniteMeasure
        H 2 h1d5SU2NoGoRankPositive beta hbeta
  have hxcoe :
      (fun A => (x : Lp ℝ 2 μ) A) =ᵐ[μ] fun A => p A := by
    rw [hxp]
    exact
      ContinuousMap.coeFn_toLp
        (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (μ := μ) p
  have hxFst :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hxcoe
  have hxSnd :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hxcoe
  have hraw :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 h1d5SU2NoGoRankPositive beta hbeta x)
          x =
        ∫ z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H 2 beta z.1 z.2 *
            (p z.1 * p z.2)
          ∂(μ.prod μ) := by
    calc
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 h1d5SU2NoGoRankPositive beta hbeta x)
          x =
        ∫ z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H 2 beta z.1 z.2 *
            (((x :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
                z.1) *
              ((x :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
                z.2))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) :=
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_rawIntegral
              H 2 h1d5SU2NoGoRankPositive beta hbeta x x
      _ =
        ∫ z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H 2 beta z.1 z.2 *
            (p z.1 * p z.2)
          ∂(μ.prod μ) := by
            unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
            apply integral_congr_ae
            filter_upwards [hxFst, hxSnd] with z hzFst hzSnd
            have hzFst' : (x : Lp ℝ 2 μ) z.1 = p z.1 := by
              simpa [Function.comp_def] using hzFst
            have hzSnd' : (x : Lp ℝ 2 μ) z.2 = p z.2 := by
              simpa [Function.comp_def] using hzSnd
            change
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H 2 beta z.1 z.2 *
                (((x : Lp ℝ 2 μ) z.1) * ((x : Lp ℝ 2 μ) z.2)) =
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H 2 beta z.1 z.2 *
                (p z.1 * p z.2)
            rw [hzFst', hzSnd']
  have hw : Measurable w := by
    simpa [w] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
        H 2 beta
  have hpairMeas :
      Measurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
          w z.1 * w z.2) :=
    (hw.comp measurable_fst).mul (hw.comp measurable_snd)
  have hpairTop :
      ∀ᵐ z ∂(μ.prod μ), w z.1 * w z.2 < (⊤ : ENNReal) := by
    filter_upwards with z
    calc
      w z.1 * w z.2 ≤ 1 * 1 := by
        exact mul_le_mul'
          (by
            simpa [w] using
              periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_le_one
                H 2 h1d5SU2NoGoRankPositive beta hbeta z.1)
          (by
            simpa [w] using
              periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_le_one
                H 2 h1d5SU2NoGoRankPositive beta hbeta z.2)
      _ < (⊤ : ENNReal) := by simp
  have hprod :
      ν.prod ν =
        (μ.prod μ).withDensity
          (fun z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
            w z.1 * w z.2) := by
    simpa [ν, μ, w,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_prod
        H 2 beta
  have hdensity :
      (∫ z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        p z.1 * p z.2 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta z.1 z.2
        ∂(ν.prod ν)) =
        ∫ z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H 2 beta z.1 z.2 *
            (p z.1 * p z.2)
          ∂(μ.prod μ) := by
    rw [hprod]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hpairMeas.aemeasurable hpairTop]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [smul_eq_mul]
    dsimp [w, periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity]
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
          H 2 beta z.1).le,
      ENNReal.toReal_ofReal
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
          H 2 beta z.2).le]
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    ring
  have hContinuous :
      Continuous
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
          p z.1 * p z.2 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
              H 2 beta z.1 z.2) := by
    exact
      ((p.continuous.comp continuous_fst).mul
        (p.continuous.comp continuous_snd)).mul
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
            H 2 beta)
  let F :
      BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun z =>
          p z.1 * p z.2 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
              H 2 beta z.1 z.2,
        hContinuous⟩
  have hIntegrable :
      Integrable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
          p z.1 * p z.2 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
              H 2 beta z.1 z.2)
        (ν.prod ν) := by
    simpa [F] using
      BoundedContinuousFunction.integrable (ν.prod ν) F
  have hFubini :=
    MeasureTheory.integral_prod
      (μ := ν) (ν := ν)
      (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        p z.1 * p z.2 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta z.1 z.2)
      hIntegrable
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 h1d5SU2NoGoRankPositive beta hbeta x)
        x =
      ∫ z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H 2 beta z.1 z.2 *
          (p z.1 * p z.2)
        ∂(μ.prod μ) := hraw
    _ =
      ∫ z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        p z.1 * p z.2 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta z.1 z.2
        ∂(ν.prod ν) := hdensity.symm
    _ =
      ∫ A₁, ∫ A₂,
        p A₁ * p A₂ *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A₁ A₂ ∂ν ∂ν := hFubini

/-- At strictly positive coupling the physical one-slab feature-analysis
operator has trivial kernel on the complete SU(2) two-mode physical span. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceSU2TwoModePhysicalFeatureAnalysis_kernel_trivial_on_span
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (hxSpan :
      x ∈ periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalSpan
        H 2 h1d5SU2NoGoRankTwo)
    (hAx :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H 2 h1d5SU2NoGoRankPositive beta hbeta.le x = 0) :
    x = 0 := by
  by_contra hxne
  rcases
    periodicHypercubicEvenPrimarySpatialSliceSU2TwoModePhysicalSpan_exists_nonzero_normalizedTracePolynomial
      H x hxSpan hxne with
    ⟨c, hc, hxp⟩
  rcases
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_halfWeightMeasure_exists_positiveDegree_crossingGram_pos
      H beta hbeta 1 c hc with
    ⟨_i, _hi, hcrossPos⟩
  let p :=
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H 1 c
  have hquad :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 h1d5SU2NoGoRankPositive beta hbeta.le x)
          x =
        ∫ A₁, ∫ A₂,
          p A₁ * p A₂ *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
              H 2 beta A₁ A₂
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) := by
    apply
      periodicHypercubicEvenSpecialUnitaryTwoPhysicalOneSlabTransfer_quadratic_eq_halfWeightCrossing_of_eq_toLp
        H beta hbeta.le x p
    simpa [p] using hxp
  have hquadZero :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 h1d5SU2NoGoRankPositive beta hbeta.le x)
          x = 0 := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_analysis]
    rw [hAx]
    simp
  have hcrossZero :
      (∫ A₁, ∫ A₂,
        p A₁ * p A₂ *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A₁ A₂
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta)) = 0 := by
    rw [← hquad]
    exact hquadZero
  exact (ne_of_gt (by simpa [p] using hcrossPos)) hcrossZero

section H1D5SU2NoGo

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 h1d5SU2NoGoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 h1d5SU2NoGoRankPositive beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- One strictly positive finite-scale coupling is enough to refute the old
completed H1-D5 compatibility in the concrete SU(2) two-mode model. -/
theorem
    physicalYangMillsVacuumNormalizedSU2TwoMode_not_completedCompatibility_of_pos
    (n : ℕ)
    (hpos : 0 < beta n) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := 2) (hN := h1d5SU2NoGoRankPositive)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  apply
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_twoModeFeatureAnalysis_kernel_trivial_on_span
      (hN2 := h1d5SU2NoGoRankTwo) Q hInvariant C n
  intro x hxSpan hAx
  exact
    periodicHypercubicEvenPrimarySpatialSliceSU2TwoModePhysicalFeatureAnalysis_kernel_trivial_on_span
      (halfExtent n) (beta n) hpos x hxSpan hAx

/-- If the coupling is strictly positive at some finite scale, the old
completed H1-D5 compatibility is impossible. -/
theorem
    physicalYangMillsVacuumNormalizedSU2TwoMode_not_completedCompatibility_of_exists_pos
    (hpos : ∃ n : ℕ, 0 < beta n) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := 2) (hN := h1d5SU2NoGoRankPositive)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  rcases hpos with ⟨n, hn⟩
  exact
    physicalYangMillsVacuumNormalizedSU2TwoMode_not_completedCompatibility_of_pos
      Q hInvariant C n hn

end H1D5SU2NoGo

end

end MathlibAnalytic
end MGAP4D

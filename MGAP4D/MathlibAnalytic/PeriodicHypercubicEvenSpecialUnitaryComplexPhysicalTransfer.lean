import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexGaussLawHilbert
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalization
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

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

noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart
    (H N : ℕ) :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  Complex.reCLM.compLpL 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart
    (H N : ℕ) :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  Complex.imCLM.compLpL 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal
    (H N : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  Complex.ofRealCLM.compLpL 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn
    (H N : ℕ)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N f =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun A => (f A).re := by
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart] using
    (ContinuousLinearMap.coeFn_compLpL Complex.reCLM f)

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn
    (H N : ℕ)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N f =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun A => (f A).im := by
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart] using
    (ContinuousLinearMap.coeFn_compLpL Complex.imCLM f)

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal_coeFn
    (H N : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun A => (f A : ℂ) := by
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal] using
    (ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f)

theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullback_realPart
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
          H N γ f) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N f) := by
  apply Lp.ext
  have hReLeft := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn
    H N (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
      H N γ f)
  have hPullC :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry_coeFn
      H N γ f
  have hPullR :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N f)
  have hRe := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn H N f
  have hRePull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H N γ).quasiMeasurePreserving.ae_eq hRe
  filter_upwards [hReLeft, hPullC, hPullR, hRePull] with A hrl hc hr hrp
  calc
    _ = (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
          H N γ f A).re := hrl
    _ = (f (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)).re :=
      congrArg Complex.re hc
    _ = periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N f
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) := by
      simpa [Function.comp_def] using hrp.symm
    _ = _ := hr.symm

theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullback_imagPart
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
          H N γ f) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N f) := by
  apply Lp.ext
  have hImLeft := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn
    H N (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
      H N γ f)
  have hPullC :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry_coeFn
      H N γ f
  have hPullR :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N f)
  have hIm := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn H N f
  have hImPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H N γ).quasiMeasurePreserving.ae_eq hIm
  filter_upwards [hImLeft, hPullC, hPullR, hImPull] with A hil hc hr hip
  calc
    _ = (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry
          H N γ f A).im := hil
    _ = (f (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)).im :=
      congrArg Complex.im hc
    _ = periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N f
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) := by
      simpa [Function.comp_def] using hip.symm
    _ = _ := hr.symm

theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullback_ofReal
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ f) := by
  apply Lp.ext
  have hPullC :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullbackLinearIsometry_coeFn
      H N γ (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f)
  have hOf := periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal_coeFn H N f
  have hOfPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H N γ).quasiMeasurePreserving.ae_eq hOf
  have hOfRight := periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal_coeFn
    H N (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ f)
  have hPullR :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ f
  filter_upwards [hPullC, hOfPull, hOfRight, hPullR] with A hc hop hor hr
  calc
    _ = periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) := hc
    _ = (f (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) : ℂ) := by
      simpa [Function.comp_def] using hop
    _ = ((periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ f) A : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ)) hr.symm
    _ = _ := hor.symm

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_ofReal
    (H N : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f) = f := by
  apply Lp.ext
  have hre := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn H N
    (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f)
  have hof := periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal_coeFn H N f
  filter_upwards [hre, hof] with A hr ho
  calc
    _ = (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f A).re := hr
    _ = ((f A : ℂ)).re := congrArg Complex.re ho
    _ = _ := by simp

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_ofReal
    (H N : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f) = 0 := by
  apply Lp.ext
  have him := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn H N
    (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f)
  have hof := periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal_coeFn H N f
  filter_upwards [him, hof, Lp.coeFn_zero ℝ 2
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)] with A hi ho hz
  calc
    _ = (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N f A).im := hi
    _ = ((f A : ℂ)).im := congrArg Complex.im ho
    _ = 0 := by simp
    _ = _ := hz.symm

noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)), by
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem]
    intro γ
    rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullback_realPart]
    rw [f.property γ]⟩

noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)), by
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem]
    intro γ
    rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullback_imagPart]
    rw [f.property γ]⟩

noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOfReal
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N (f :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)), by
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugeInvariantL2Submodule_mem]
    intro γ
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexGaugePullback_ofReal]
    rw [f.property γ]⟩

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_ofReal
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f) = f := by
  apply Subtype.ext
  change periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N
      (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  exact periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_ofReal H N _

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_ofReal
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f) = 0 := by
  apply Subtype.ext
  change periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N
      (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) = 0
  exact periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_ofReal H N _

theorem periodicHypercubicEvenSpecialUnitaryComplexPhysical_ext_components
    (H N : ℕ)
    {f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N}
    (hre : periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g)
    (him : periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g) :
    f = g := by
  apply Subtype.ext
  change (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
    (g : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  apply Lp.ext
  have hre' :
      periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (f :
          Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
        periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (g :
          Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
    congrArg Subtype.val hre
  have him' :
      periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (f :
          Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
        periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (g :
          Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
    congrArg Subtype.val him
  have hrf := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn H N (f :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have hrg := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn H N (g :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have hif := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn H N (f :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have hig := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn H N (g :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  rw [hre'] at hrf
  rw [him'] at hif
  filter_upwards [hrf, hrg, hif, hig] with A hrfA hrgA hifA higA
  apply Complex.ext
  · exact hrfA.symm.trans hrgA
  · exact hifA.symm.trans higA

theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_smul
    (H N : ℕ) (c : ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N (c • f) =
      c.re • periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f -
        c.im • periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f := by
  apply Subtype.ext
  change periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N
      (c • (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
    c.re • periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (f :
        Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) -
      c.im • periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (f :
        Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  apply Lp.ext
  have hleft := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn H N
    (c • (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  have hsmul := Lp.coeFn_smul c (f :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have hre := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn H N (f :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have him := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn H N (f :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have hrs := Lp.coeFn_smul c.re
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  have his := Lp.coeFn_smul c.im
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  have hsub := Lp.coeFn_sub
    (c.re • periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
    (c.im • periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  filter_upwards [hleft, hsmul, hre, him, hrs, his, hsub] with A hl hs hr hi hrsA hisA hsubA
  let fL2 : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := f
  calc
    _ = ((c • fL2) A).re := hl
    _ = (c * fL2 A).re := by simpa [smul_eq_mul] using congrArg Complex.re hs
    _ = c.re * (fL2 A).re - c.im * (fL2 A).im := Complex.mul_re _ _
    _ = _ := by
      rw [hsubA, hrsA, hisA, hr, hi]
      rfl

theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_smul
    (H N : ℕ) (c : ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N (c • f) =
      c.im • periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f +
        c.re • periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f := by
  apply Subtype.ext
  change periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N
      (c • (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
    c.im • periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (f :
        Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) +
      c.re • periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (f :
        Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  apply Lp.ext
  have hleft := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn H N
    (c • (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  have hsmul := Lp.coeFn_smul c (f :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have hre := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn H N (f :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have him := periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn H N (f :
    Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have his := Lp.coeFn_smul c.im
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  have hrs := Lp.coeFn_smul c.re
    (periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  have hadd := Lp.coeFn_add
    (c.im • periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
    (c.re • periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N (f :
      Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  filter_upwards [hleft, hsmul, hre, him, his, hrs, hadd] with A hl hs hr hi hisA hrsA haddA
  let fL2 : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := f
  calc
    _ = ((c • fL2) A).im := hl
    _ = (c * fL2 A).im := by simpa [smul_eq_mul] using congrArg Complex.im hs
    _ = c.re * (fL2 A).im + c.im * (fL2 A).re := Complex.mul_im _ _
    _ = c.im * (fL2 A).re + c.re * (fL2 A).im := by ring
    _ = _ := by
      rw [haddA, hisA, hrsA, hr, hi]
      rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_add
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N (f + g) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f +
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g := by
  apply Subtype.ext
  exact map_add _ _ _

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_add
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N (f + g) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f +
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g := by
  apply Subtype.ext
  exact map_add _ _ _

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_add
    (H N : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N (f + g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f +
        periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N g := by
  apply Subtype.ext
  exact map_add _ _ _

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_smul
    (H N : ℕ) (c : ℝ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N (c • f) =
      c • periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f := by
  apply Subtype.ext
  exact map_smul _ _ _

theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_norm_le
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f‖ ≤ ‖f‖ := by
  change ‖periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart H N
      (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ ≤
    ‖(f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2RealPart_coeFn H N
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))] with A hA
  rw [hA]
  exact Complex.abs_re_le_norm
    ((f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) A)

theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_norm_le
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f‖ ≤ ‖f‖ := by
  change ‖periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart H N
      (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ ≤
    ‖(f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [periodicHypercubicEvenSpecialUnitarySpatialSliceComplexL2ImagPart_coeFn H N
    (f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))] with A hA
  rw [hA]
  exact Complex.abs_im_le_norm
    ((f : Lp ℂ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) A)

theorem periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f‖ = ‖f‖ := by
  apply le_antisymm
  · change ‖periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ ≤
      ‖(f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal_coeFn H N
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))] with A hA
    rw [hA]
    simp
  · have hre := periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_norm_le H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f)
    simpa using hre

noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
      (T (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f)) +
    Complex.I • periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
      (T (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f))

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun_realPart
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun H N T f) =
      T (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f) := by
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_smul]

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun_imagPart
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun H N T f) =
      T (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f) := by
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_smul]

noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationLinearMap
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →ₗ[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N where
  toFun := periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun H N T
  map_add' := by
    intro f g
    apply periodicHypercubicEvenSpecialUnitaryComplexPhysical_ext_components H N
    · simp
    · simp
  map_smul' := by
    intro c f
    apply periodicHypercubicEvenSpecialUnitaryComplexPhysical_ext_components H N
    · simp [periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_smul,
        map_sub, map_smul]
    · simp [periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_smul,
        map_add, map_smul]

theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun_norm_le
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun H N T f‖ ≤
      (2 * ‖T‖) * ‖f‖ := by
  let xr := periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f
  let xi := periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun H N T f‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N (T xr)‖ +
          ‖Complex.I • periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N (T xi)‖ :=
      norm_add_le _ _
    _ = ‖T xr‖ + ‖T xi‖ := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm,
        norm_smul, Complex.norm_I, one_mul,
        periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm]
    _ ≤ ‖T‖ * ‖xr‖ + ‖T‖ * ‖xi‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm T xr) (ContinuousLinearMap.le_opNorm T xi)
    _ ≤ ‖T‖ * ‖f‖ + ‖T‖ * ‖f‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_norm_le H N f)
          (norm_nonneg T))
        (mul_le_mul_of_nonneg_left
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_norm_le H N f)
          (norm_nonneg T))
    _ = (2 * ‖T‖) * ‖f‖ := by ring

noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  LinearMap.mkContinuous
    (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationLinearMap H N T)
    (2 * ‖T‖)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun_norm_le H N T)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun H N T f := rfl

theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_ofReal
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T
        (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N (T f) := by
  apply periodicHypercubicEvenSpecialUnitaryComplexPhysical_ext_components H N
  · simp
  · simp

noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

noncomputable def periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransferOperator_ofReal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransferOperator
        H N hN beta hbeta (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_ofReal H N _ f

theorem periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_ofReal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_ofReal H N _ f

noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector_norm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector
      H N hN beta hbeta‖ = 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector,
    periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
    H N hN beta hbeta

theorem periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector,
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_ofReal,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed]

structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  realIntertwining :
    ∀ f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransferOperator
          H N hN beta hbeta (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta f)
  normalizedRealIntertwining :
    ∀ f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta f)
  topUnit :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector
      H N hN beta hbeta‖ = 1
  topFixed :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector
        H N hN beta hbeta

theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferPackage
      H N hN beta hbeta :=
  { realIntertwining :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTransferOperator_ofReal
        H N hN beta hbeta
    normalizedRealIntertwining :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_ofReal
        H N hN beta hbeta
    topUnit :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector_norm
        H N hN beta hbeta
    topFixed :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D

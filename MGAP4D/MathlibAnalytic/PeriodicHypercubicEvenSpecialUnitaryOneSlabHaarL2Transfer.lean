import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernel
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSymmetricKernel
import MGAP4D.MathlibAnalytic.SpecialUnitaryTopologicalCompactReceipts
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureMeasurability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance oneSlabHaarL2SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabHaarL2SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabHaarL2SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabHaarL2SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabHaarL2SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabHaarL2SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Product normalized Haar probability measure on the actual modern
three-dimensional spatial-slice link carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    (H N : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

instance periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_sFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Product Haar probability on two adjacent spatial boundaries. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    (H N : ℕ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- The intrinsic spatial Wilson action is continuous on the finite product
of compact `SU(N)` link variables. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous
    (H N : ℕ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  generalize periodicHypercubicEvenSpatialSlicePlaquetteList H = ps
  induction ps with
  | nil =>
      simpa using
        (continuous_const : Continuous
          (fun _ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            (0 : ℝ)))
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhol : Continuous
          (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        fun_prop
      exact ((continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hhol).add ih

/-- Each spatial half-Boltzmann amplitude is continuous. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous
    (H N : ℕ)
    (beta : ℝ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  exact Real.continuous_exp.comp
    (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H N))

/-- The temporal crossing kernel is jointly continuous in the two adjacent
spatial boundary configurations. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
    (H N : ℕ)
    (beta : ℝ) :
    Continuous
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
          H N beta p.1 p.2) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil =>
      simpa using
        (continuous_const : Continuous
          (fun _ :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            (1 : ℝ)))
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons]
      have hleft : Continuous
          (fun p :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => p.1 e) :=
        (continuous_apply e).comp continuous_fst
      have hright : Continuous
          (fun p :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => p.2 e) :=
        (continuous_apply e).comp continuous_snd
      have hlocal : Continuous
          (fun p :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            specialUnitaryWilsonRelativeKernel N beta (p.1 e) (p.2 e)) :=
        (continuous_specialUnitaryWilsonRelativeKernel N beta).comp₂ hleft hright
      exact hlocal.mul ih

/-- The complete actual one-slab Wilson kernel is jointly continuous. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
    (H N : ℕ)
    (beta : ℝ) :
    Continuous
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  have hw :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous
      H N beta
  exact
    ((hw.comp continuous_fst).mul
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
        H N beta)).mul
      (hw.comp continuous_snd)

/-- The spatial Wilson action is nonnegative at positive matrix rank. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤ periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  generalize periodicHypercubicEvenSpatialSlicePlaquetteList H = ps
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg
        (specialUnitaryWilsonPlaquetteEnergy_nonneg hN
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)) ih

/-- The temporal crossing action is nonnegative at positive matrix rank. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg
        (specialUnitaryWilsonPlaquetteEnergy_nonneg hN ((A e)⁻¹ * B e)) ih

/-- The symmetric one-slab Wilson action is nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  have hA :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg H N hN A
  have hB :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg H N hN B
  have hcross :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_nonneg
      H N hN A B
  positivity

/-- For nonnegative coupling the complete one-slab Boltzmann kernel is at most
one.  Together with strict positivity from #2028 this gives a uniform pointwise
`[0,1]` bound on every finite slice. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B ≤ 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  have haction :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H N hN A B
  have hnonpos :
      -beta * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
        H N A B ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta) haction
  calc
    Real.exp
        (-beta * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
          H N A B) ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
    _ = 1 := Real.exp_zero

/-- Uniform absolute bound by one for the actual one-slab kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B| ≤ 1 := by
  rw [abs_of_pos
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta A B)]
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
    H N hN beta hbeta A B

/-- The squared one-slab kernel is integrable on the normalized product Haar
probability measure. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_norm_sq_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2‖ ^ 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let pairMeasure :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  letI : IsFiniteMeasure pairMeasure := by
    dsimp [pairMeasure,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hm :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable
  have hsqMeasurable : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2‖ ^ 2) :=
    hm.norm.pow_const 2
  exact Integrable.of_bound hsqMeasurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun p => by
      let k := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2
      have hkpos : 0 < k := by
        simpa [k] using
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
            H N beta p.1 p.2
      have hkle : k ≤ 1 := by
        simpa [k] using
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
            H N hN beta hbeta p.1 p.2
      change |‖k‖ ^ 2| ≤ (1 : ℝ)
      rw [abs_of_nonneg (sq_nonneg ‖k‖), Real.norm_eq_abs, abs_of_pos hkpos]
      nlinarith)

/-- The actual one-slab Wilson kernel belongs to product-Haar `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MemLp
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
  (memLp_two_iff_integrable_sq_norm
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable.aestronglyMeasurable).2
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_norm_sq_integrable
      H N hN beta hbeta)

/-- Complete product-Haar `L²` vector of the actual one-slab Wilson kernel. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_memLp_two
    H N hN beta hbeta).toLp
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2)

/-- The `L²` kernel vector is represented almost everywhere by the literal
one-slab Wilson Boltzmann kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta p) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_memLp_two
    H N hN beta hbeta).coeFn_toLp

/-- The actual bounded one-slab transfer operator on spatial-slice Haar `L²`,
constructed canonically from the Hilbert--Schmidt kernel by Fréchet--Riesz. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  realL2HilbertSchmidtKernelOperator
    (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta)

/-- Exact matrix coefficient of the actual one-slab Haar `L²` transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta) f g := by
  exact realL2HilbertSchmidtKernelOperator_inner
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta) f g

/-- Hilbert--Schmidt control of the actual one-slab transfer operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta‖ := by
  exact realL2HilbertSchmidtKernelOperator_norm_le
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta)

/-- The literal one-slab scalar representative is symmetric under swapping the
adjacent spatial boundaries. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_representative_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealL2KernelRepresentativeSymmetric
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2) := by
  intro p
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H N hN beta hbeta p.2 p.1

/-- The actual one-slab Haar `L²` transfer operator is symmetric. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isSymmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).IsSymmetric := by
  exact realL2HilbertSchmidtKernelOperator_isSymmetric_of_ae_symmetric_rep
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta)
    (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_representative_symmetric
      H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D
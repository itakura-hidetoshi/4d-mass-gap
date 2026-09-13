import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkFiber
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumDoobVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkRawDoobSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Successive normalized Doob tilts compose exactly to the normalized product
weight once the first normalizing mass is nonzero and finite. -/
private theorem doobWeightedMeasure_doobWeightedMeasure_eq_mul
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (q omega : α → ℝ≥0∞)
    (hq : AEMeasurable q μ)
    (homega : AEMeasurable omega μ)
    (hMassZero : doobWeightMass μ q ≠ 0)
    (hMassTop : doobWeightMass μ q ≠ ∞) :
    doobWeightedMeasure (doobWeightedMeasure μ q) omega =
      doobWeightedMeasure μ (q * omega) := by
  have hMass :
      doobWeightMass μ q *
          doobWeightMass (doobWeightedMeasure μ q) omega =
        doobWeightMass μ (q * omega) := by
    simpa [doobWeightMass] using
      doobWeightMass_mul_lintegral_doobWeightedMeasure
        μ q omega hq homega hMassZero hMassTop
  change
    (μ.withDensity (doobWeightedDensity μ q)).withDensity
        (doobWeightedDensity (doobWeightedMeasure μ q) omega) =
      μ.withDensity (doobWeightedDensity μ (q * omega))
  unfold doobWeightedDensity
  rw [← withDensity_mul₀
    (hq.div_const (doobWeightMass μ q))
    (homega.div_const (doobWeightMass (doobWeightedMeasure μ q) omega))]
  apply withDensity_congr_ae
  filter_upwards with x
  change
    (q x / doobWeightMass μ q) *
        (omega x / doobWeightMass (doobWeightedMeasure μ q) omega) =
      (q x * omega x) / doobWeightMass μ (q * omega)
  rw [← hMass]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hMassZero) (Or.inl hMassTop)]
  ac_rfl

/-- The one-slab part of the C5 reference weight before the continuous-vacuum
factor is inserted.  This is not the full four-dimensional Wilson Gibbs weight. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRawWeight
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g₂ *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A (Function.update B source k)

/-- Restriction of the one-slab raw reference weight to the selected spatial
link fiber. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRawWeight
    H N beta B target source k g₂
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N A fiber g)

/-- The C5 raw one-link weight is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight_pos
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
        H N beta B target source fiber k g₂ A g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRawWeight
  exact mul_pos
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta _ B target g₂)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta _ (Function.update B source k))

/-- Normalized C5 raw one-link law obtained from `local × kernel` before the
continuous-vacuum Doob factor is inserted. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawProbabilityMeasure
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  realIntegralWeightedProbabilityMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
      H N beta B target source fiber k g₂ A)

/-- The literal C5 reference fiber weight is exactly the continuous vacuum
factor times the normalized-law precursor `local × kernel`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_vacuum_mul_rawWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A =
      fun g =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
              H N A fiber g) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
            H N beta B target source fiber k g₂ A g := by
  funext g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRawWeight
  ring

/-- After normalizing `local × kernel`, inserting only the continuous-vacuum
fiber weight reproduces the literal C5 reference fiber probability law exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_rawDoob
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawProbabilityMeasure
          H N beta B target source fiber k g₂ A)
        A fiber := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let replace : Matrix.specialUnitaryGroup (Fin N) ℂ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A fiber g
  let Local : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta (replace g) B target g₂
  let K : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta (replace g) (Function.update B source k)
  let q : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    fun g => ENNReal.ofReal (Local g * K g)
  let omega : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta A fiber
  let full : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    fun g => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A g)
  let C : ℝ := Real.exp (8 * beta)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hReplace : Continuous replace := by
    simpa [replace] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N A fiber
  have hLocalMeas : Measurable Local := by
    exact
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
        H N beta B target g₂).comp hReplace).measurable
  have hKernelMeas : Measurable K := by
    exact
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).comp (hReplace.prodMk continuous_const)).measurable
  have hqMeas : Measurable q :=
    ENNReal.measurable_ofReal.comp (hLocalMeas.mul hKernelMeas)
  have homegaMeas : Measurable omega := by
    simpa [omega] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight_continuous
        H N hN beta hbeta A fiber).measurable
  have hqPos : ∀ g, 0 < q g := by
    intro g
    exact ENNReal.ofReal_pos.mpr
      (mul_pos
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
          H N beta (replace g) B target g₂)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
          H N beta (replace g) (Function.update B source k)))
  have hqUpper : ∀ g, q g ≤ ENNReal.ofReal C := by
    intro g
    apply ENNReal.ofReal_le_ofReal
    have hLocalNonneg : 0 ≤ Local g :=
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta (replace g) B target g₂).le
    have hKernelBound : K g ≤ 1 := by
      simpa [K] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
          H N hN beta hbeta (replace g) (Function.update B source k)
    have hLocalBound : Local g ≤ C := by
      simpa [Local, C] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
          H N hN beta hbeta (replace g) B target g₂
    calc
      Local g * K g ≤ Local g * 1 :=
        mul_le_mul_of_nonneg_left hKernelBound hLocalNonneg
      _ = Local g := mul_one _
      _ ≤ C := hLocalBound
  have hMassPos : 0 < doobWeightMass μ q := by
    unfold doobWeightMass
    rw [lintegral_pos_iff_support hqMeas]
    have hsupp : Function.support q = Set.univ := by
      ext g
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hqPos g).ne'
    rw [hsupp]
    simp [μ]
  have hMassUpper : doobWeightMass μ q ≤ ENNReal.ofReal C :=
    doobWeightMass_upper_bound μ q (ENNReal.ofReal C) hqUpper
  have hMassTop : doobWeightMass μ q ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hMassUpper ENNReal.ofReal_lt_top)
  have hCompose :
      doobWeightedMeasure (doobWeightedMeasure μ q) omega =
        doobWeightedMeasure μ (q * omega) :=
    doobWeightedMeasure_doobWeightedMeasure_eq_mul
      μ q omega hqMeas.aemeasurable homegaMeas.aemeasurable
      (ne_of_gt hMassPos) hMassTop
  have hRawMeasure :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawProbabilityMeasure
          H N beta B target source fiber k g₂ A =
        doobWeightedMeasure μ q := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawProbabilityMeasure
      realIntegralWeightedProbabilityMeasure
    change doobWeightedMeasure μ
        (fun g => ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
            H N beta B target source fiber k g₂ A g)) =
      doobWeightedMeasure μ q
    apply congrArg (doobWeightedMeasure μ)
    funext g
    rfl
  have hFull : full = q * omega := by
    funext g
    have hReal := congrFun
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_vacuum_mul_rawWeight
        H N hN beta hbeta B target source fiber k g₂ A) g
    have hOmegaNonneg :
        0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (replace g) :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta (replace g)).le
    dsimp [full]
    rw [hReal, ENNReal.ofReal_mul hOmegaNonneg]
    change omega g * q g = q g * omega g
    exact mul_comm _ _
  have hFullMeasure :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂ A =
        doobWeightedMeasure μ (q * omega) := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      realIntegralWeightedProbabilityMeasure
    change doobWeightedMeasure μ full = doobWeightedMeasure μ (q * omega)
    rw [hFull]
  rw [hFullMeasure, hRawMeasure]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
  exact hCompose.symm

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkOffFiberMeasurable
import Mathlib.Probability.Kernel.Proper
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance continuousVacuumReferenceOneLinkHeatBathProperSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkHeatBathProperSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkHeatBathProperSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkHeatBathProperSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkHeatBathProperSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkHeatBathProperSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Canonical measure-valued representative of the reference heat-bath kernel
on the off-fiber configuration space. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernelOffFiberRepresentative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberConfiguration H N fiber →
      Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  fun Aoff =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
      (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberAssemble H N fiber 1 Aoff)

/-- The measure-valued off-fiber representative is measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernelOffFiberRepresentative_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernelOffFiberRepresentative
        H N hN beta hbeta B target source fiber k g₂) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernelOffFiberRepresentative
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂).measurable.comp
      (measurable_periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberAssemble
        H N fiber 1)

/-- The ambient-source heat-bath kernel factors pointwise through off-fiber
restriction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_eq_offFiberRepresentative_comp_restriction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernelOffFiberRepresentative
          H N hN beta hbeta B target source fiber k g₂ ∘
        periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberRestriction H N fiber := by
  funext A
  simp only [Function.comp_apply]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernelOffFiberRepresentative
  rw [
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberAssemble_restriction
      H N fiber 1 A]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_update_fiber
      H N hN beta hbeta B target source fiber k g₂ A 1).symm

/-- The exact reference heat-bath transition measure is measurable already with
respect to the off-fiber sigma algebra in its input configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_offFiberMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    @Measurable
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
      (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
      inferInstance
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_eq_offFiberRepresentative_comp_restriction
      H N hN beta hbeta B target source fiber k g₂]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernelOffFiberRepresentative_measurable
      H N hN beta hbeta B target source fiber k g₂).comp
      (comap_measurable
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberRestriction H N fiber))

/-- The same exact transition measures, now typed canonically as a kernel from
the off-fiber sigma algebra to the ambient configuration sigma algebra. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    @Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
      (inferInstance : MeasurableSpace
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)) :=
  @Kernel.mk
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
    (inferInstance : MeasurableSpace
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (fun A =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_offFiberMeasurable
      H N hN beta hbeta B target source fiber k g₂)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A := by
  rfl

instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂) := by
  refine ⟨fun A => ?_⟩
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_apply]
  infer_instance

/-- Membership in an off-fiber measurable event is unchanged by replacing the
selected fiber coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitary_mem_offFiberMeasurableSet_iff_update_fiber
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (s : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hs : MeasurableSet[
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber] s)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    A ∈ s ↔ Function.update A fiber g ∈ s := by
  rw [MeasurableSpace.measurableSet_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  change
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberRestriction H N fiber A ∈ t ↔
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberRestriction H N fiber
        (Function.update A fiber g) ∈ t
  have hRestriction :
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberRestriction H N fiber
          (Function.update A fiber g) =
        periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberRestriction H N fiber A := by
    funext e
    simp [periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberRestriction,
      Function.update, e.2]
  rw [hRestriction]

/-- The off-fiber-typed reference heat-bath kernel is proper. This is the
kernel-level statement that an update at the selected fiber preserves every
off-fiber measurable event. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_isProper
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Kernel.IsProper
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂) := by
  let hle :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le
      H N fiber
  apply Kernel.IsProper.of_inter_eq_indicator_mul hle
  intro Aset hA Bset hB A
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g₂ A
  let FInter :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    (Aset ∩ Bset).indicator (fun _ => 1)
  have hBambient : MeasurableSet Bset := hle Bset hB
  have hInter : MeasurableSet (Aset ∩ Bset) := hA.inter hBambient
  have hFInter : Measurable FInter := measurable_const.indicator hInter
  by_cases hAB : A ∈ Bset
  · simp only [Set.indicator_of_mem hAB, Pi.one_apply, one_mul]
    let FA :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
      Aset.indicator (fun _ => 1)
    have hFA : Measurable FA := measurable_const.indicator hA
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A (Aset ∩ Bset) =
        ∫⁻ C, FInter C ∂K A := by
          simp [K, FInter, hInter]
      _ = ∫⁻ g, FInter (Function.update A fiber g) ∂ν := by
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_lintegral
              H N hN beta hbeta B target source fiber k g₂ A FInter hFInter
      _ = ∫⁻ g, FA (Function.update A fiber g) ∂ν := by
          apply lintegral_congr
          intro g
          have hBg : Function.update A fiber g ∈ Bset :=
            (periodicHypercubicEvenSpecialUnitary_mem_offFiberMeasurableSet_iff_update_fiber
              H N fiber Bset hB A g).mp hAB
          by_cases hAg : Function.update A fiber g ∈ Aset
          · simp [FInter, FA, hAg, hBg]
          · simp [FInter, FA, hAg]
      _ = ∫⁻ C, FA C ∂K A := by
          exact
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_lintegral
              H N hN beta hbeta B target source fiber k g₂ A FA hFA).symm
      _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A Aset := by
          simp [K, FA, hA]
  · simp only [Set.indicator_of_not_mem' hAB, zero_mul]
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A (Aset ∩ Bset) =
        ∫⁻ C, FInter C ∂K A := by
          simp [K, FInter, hInter]
      _ = ∫⁻ g, FInter (Function.update A fiber g) ∂ν := by
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_lintegral
              H N hN beta hbeta B target source fiber k g₂ A FInter hFInter
      _ = 0 := by
          apply lintegral_eq_zero.mpr
          filter_upwards [] with g
          have hBg : Function.update A fiber g ∉ Bset := by
            intro hg
            exact hAB
              ((periodicHypercubicEvenSpecialUnitary_mem_offFiberMeasurableSet_iff_update_fiber
                H N fiber Bset hB A g).mpr hg)
          simp [FInter, hBg]

end

end MathlibAnalytic
end MGAP4D

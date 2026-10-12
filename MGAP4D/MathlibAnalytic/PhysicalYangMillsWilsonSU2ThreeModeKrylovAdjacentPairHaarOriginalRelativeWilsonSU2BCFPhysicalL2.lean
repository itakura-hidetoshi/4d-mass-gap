import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaugeInvariantLocalSupport
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalBoundedCoreKernelExactFrontier
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairObservableInsertion
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# P4-Q2-EE: genuine SU(2) relative Wilson class observable in both true joint L² spaces

ED proved on the actual spatial-slice SU(N) gauge carrier that one-boundary
one-link real observables invariant under all vertex gauges are constant.
In contrast, the true two-boundary relative link A_e^-1 B_e transforms
by conjugation, and the SU(2) Wilson energy is a nonconstant class function
taking values 0 and 2 at concrete configurations.

Here this exact pointwise observable is built as a BOUNDED CONTINUOUS
function on the true two-boundary compact SU(2) pair configuration space,
then inserted into the exact ORIGINAL Wilson ground-state bounded strongly
measurable core and its actual physical joint L² quotient. Independently
the SAME observable gives an L² class under the ACTUAL independent pair-Haar
joint probability measure. The respective quotient representatives have
their honest almost-everywhere equalities under the two DIFFERENT measures.
The genuine original Wilson full joint Riesz quadratic then evaluates to
the literal ORIGINAL unnormalized physical Haar-reference core energy
on exactly this physical representative.

No invented probability distribution, synthetic quotient, Wilson/Haar
projection equality, beta-zero assumption, arbitrary gauge-fixing or
volume-uniform estimate. A nonconstant POINTWISE bounded continuous
function need not be claimed nonzero in L² without a support/equivalence
proof; the latter and exact left/right coordinate defect support are the
next independent tasks. No sorry/admit/new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section ActualSU2RelativeJointL2

variable (H : ℕ)
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "Core" => p4Q2BP_originalBoundedStronglyMeasurableCore H 2
local notation "Obs" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H 2

/-- ACTUAL bounded continuous two-boundary SU(2) relative-link Wilson
energy on the original spatial-slice compact pair carrier. -/
noncomputable def p4Q2EE_SU2_relativeWilsonEnergyBCF (e : Link) : Obs :=
  BoundedContinuousFunction.mkOfCompact
    ⟨(fun z : Joint =>
      specialUnitaryWilsonPlaquetteEnergy 2 ((z.1 e)⁻¹ * z.2 e)), by fun_prop⟩

theorem p4Q2EE_SU2_relativeWilsonEnergyBCF_apply
    (e : Link) (z : Joint) :
    p4Q2EE_SU2_relativeWilsonEnergyBCF H e z =
      specialUnitaryWilsonPlaquetteEnergy 2 ((z.1 e)⁻¹ * z.2 e) := rfl

/-- The actual observable lies in [0,2], not merely abstractly bounded. -/
theorem p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc
    (e : Link) (z : Joint) :
    p4Q2EE_SU2_relativeWilsonEnergyBCF H e z ∈ Set.Icc (0 : ℝ) 2 := by
  rw [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply]
  exact specialUnitaryWilsonPlaquetteEnergy_mem_Icc (by norm_num) _

/-- The TRUE gauge-invariant BCF property uses simultaneous original
spatial vertex gauge action on BOTH actual boundary configurations. -/
theorem p4Q2EE_SU2_relativeWilsonEnergyBCF_gaugeInvariant
    (e : Link) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant
      H 2 (p4Q2EE_SU2_relativeWilsonEnergyBCF H e) := by
  intro γ A B
  change specialUnitaryWilsonPlaquetteEnergy 2
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) e)⁻¹ *
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ B) e)) =
    specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e)
  exact p4Q2ED_SU2_relativeWilsonEnergy_gaugeInvariant H e γ A B

/-- ED's concrete 0/2 configurations give a genuine nonconstant
BOUNDED CONTINUOUS original two-boundary observable. -/
theorem p4Q2EE_SU2_relativeWilsonEnergyBCF_nonconstant (e : Link) :
    ∃ z w : Joint,
      p4Q2EE_SU2_relativeWilsonEnergyBCF H e z = 0 ∧
      p4Q2EE_SU2_relativeWilsonEnergyBCF H e w = 2 := by
  obtain ⟨A, B, C, D, hZero, hTwo⟩ :=
    p4Q2ED_SU2_relativeWilsonEnergy_zero_two H e
  refine ⟨(A, B), (C, D), ?_, ?_⟩
  · simpa only [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply] using hZero
  · simpa only [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply] using hTwo

/-- A global pointwise bound also supplies the exact ORIGINAL Wilson
strongly-measurable bounded real concrete core predicate. -/
noncomputable def p4Q2EE_SU2_originalWilsonPhysicalCore (e : Link) : Core := by
  let b : Obs := p4Q2EE_SU2_relativeWilsonEnergyBCF H e
  have hMeas : StronglyMeasurable (b : Joint → ℝ) :=
    b.continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖b z‖ ≤ (2 : ℝ) := by
    intro z
    have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
    have hAbs : |b z| ≤ (2 : ℝ) := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    simpa [Real.norm_eq_abs] using hAbs
  exact ⟨b, ⟨hMeas, ⟨2, hBound⟩⟩⟩

theorem p4Q2EE_SU2_originalWilsonPhysicalCore_apply
    (e : Link) (z : Joint) :
    (p4Q2EE_SU2_originalWilsonPhysicalCore H e : Joint → ℝ) z =
      p4Q2EE_SU2_relativeWilsonEnergyBCF H e z := rfl

/-- The actual bounded observable belongs to the original Wilson
physical joint L² through precisely BR's certified canonical core map. -/
noncomputable def p4Q2EE_SU2_physicalWilsonJointL2
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H 2 (by norm_num) beta hbeta :=
  p4Q2BR_originalCorePhysicalL2 H 2 (by norm_num) beta hbeta
    (p4Q2EE_SU2_originalWilsonPhysicalCore H e)

/-- The ACTUAL original Wilson joint-L² quotient has the literal
relative Wilson energy representative, Wilson-a.e., not pointwise. -/
theorem p4Q2EE_SU2_physicalWilsonJointL2_ae_eq
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ((p4Q2EE_SU2_physicalWilsonJointL2 H beta hbeta e :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (by norm_num) beta hbeta) : Joint → ℝ) =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H 2 (by norm_num) beta hbeta]
      (fun z : Joint => p4Q2EE_SU2_relativeWilsonEnergyBCF H e z) := by
  exact (p4Q2CL_originalBoundedCoreToPhysical_coeFn
    H 2 (by norm_num) beta hbeta
    (p4Q2EE_SU2_originalWilsonPhysicalCore H e))

/-- An independent construction in the actual product pair-Haar
probability L², without identifying the physical Wilson and pair-Haar laws. -/
theorem p4Q2EE_SU2_pairHaar_memLp
    (e : Link) :
    MemLp (fun z : Joint => p4Q2EE_SU2_relativeWilsonEnergyBCF H e z) 2 muPair := by
  let b : Obs := p4Q2EE_SU2_relativeWilsonEnergyBCF H e
  have hBound : ∀ z : Joint, ‖b z‖ ≤ ‖b‖ := fun z => b.norm_coe_le_norm z
  exact MemLp.of_bound b.continuous.aestronglyMeasurable ‖b‖
    (Filter.Eventually.of_forall hBound)

/-- Genuine, distinct, independent pair-Haar joint-L² class of the SAME
bounded continuous original SU(2) two-boundary observable. -/
noncomputable def p4Q2EE_SU2_pairHaarJointL2 (e : Link) : Lp ℝ 2 muPair :=
  (p4Q2EE_SU2_pairHaar_memLp H e).toLp
    (fun z => p4Q2EE_SU2_relativeWilsonEnergyBCF H e z)

theorem p4Q2EE_SU2_pairHaarJointL2_ae_eq (e : Link) :
    ((p4Q2EE_SU2_pairHaarJointL2 H e : Lp ℝ 2 muPair) : Joint → ℝ) =ᵐ[muPair]
      (fun z : Joint => p4Q2EE_SU2_relativeWilsonEnergyBCF H e z) := by
  exact MemLp.coeFn_toLp (p4Q2EE_SU2_pairHaar_memLp H e)

/-- The ORIGINAL Wilson full-physical-joint-L² Riesz quadratic of the
actual bounded-continuous relative SU(2) observable agrees with the
LITERAL original mass-weighted UNNORMALIZED twelve-color Haar-reference
quadratic of the SAME bounded concrete Wilson observable. -/
theorem p4Q2EE_SU2_originalWilsonRieszQuadratic_eq_literal
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    p4Q2BX_originalFullJointQuadratic H 2 (by norm_num) beta hbeta
      (p4Q2EE_SU2_physicalWilsonJointL2 H beta hbeta e) =
        p4Q2BP_originalCoreReference H 2 (by norm_num) beta hbeta
          (p4Q2EE_SU2_originalWilsonPhysicalCore H e) :=
  p4Q2CL_originalFullQuadratic_eq_literalCore H 2
    (by norm_num) beta hbeta
    (p4Q2EE_SU2_originalWilsonPhysicalCore H e)

end ActualSU2RelativeJointL2
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EE_SU2_relativeWilsonEnergyBCF_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.p4Q2EE_SU2_relativeWilsonEnergyBCF_nonconstant
#print axioms MGAP4D.MathlibAnalytic.p4Q2EE_SU2_physicalWilsonJointL2_ae_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2EE_SU2_pairHaarJointL2_ae_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2EE_SU2_originalWilsonRieszQuadratic_eq_literal

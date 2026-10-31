import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferRegressionV5_PZ37ACA
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredGIReceiverTranslationV5_PZ37AAU2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPhysicalGaugeContinuousRangeV5_OV
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaugeNormalizedCenteredTransferV5_LK

/-!
# P4-Q2-PZ37ACB — genuine gauge symmetry of the centered physical receiver

The SAME centered Gauss-law source has its existing continuous spatial
Wilson representative. The genuine Perron vacuum is itself a physical
vector with its original continuous representative. OV therefore gives
pointwise gauge invariance for both representatives, and LK transports the
actual source through the original one-slab Wilson kernel.

Apply one and the same spatial gauge transformation to both outer boundary
configurations. This preserves the true joint square-root density; no
independent left/right gauge invariance is used. A central minus identity
at the source vertex of a chosen link turns its inserted value g into c*g.
Both original link endpoints are distinct even at H=0. The original FF
receiver and Perron transfer section therefore obey exact antipodal
transport under this genuine transformation of the outer context.

The fixed left anchors of the two posterior laws are NOT transported by
these statements. No GI-gap sign symmetry, tail smallness, or uniform
physical coercivity is asserted.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "c" => p4Q2PZ35D4_centralMinusOne
local instance p4Q2PZ37ACB_gaugeGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACB_gaugeCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACB_gaugeCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACB_gaugeMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACB_gaugeBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "GT" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "GA" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Ω" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
  H 2 (by norm_num)
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "sqrtD" => continuousJointSqrtDensity H 2 (by norm_num)
local notation "I" => decomposableOneSliceTransferIntegral H 2
local notation "fH" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local instance p4Q2PZ37ACB_gaugeLinks : Fintype Link := Fintype.ofFinite _

/-- Pointwise gauge invariance of the SAME positive Perron representative,
deduced from its actual Gauss-law Hilbert vector and continuous representative. -/
theorem p4Q2PZ37ACB_originalPerron_gaugeInvariant
    (b : ℝ) (hb : 0 ≤ b) (gamma : GT) (B : Cfg) :
    Ω b hb (GA gamma B) = Ω b hb B := by
  let v : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H 2 (by norm_num) b hb
  let omega : C(Cfg, ℝ) :=
    ⟨Ω b hb,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
        H 2 (by norm_num) b hb⟩
  have hRep : (fun A : Cfg => (v : Lp ℝ 2 haar) A) =ᵐ[haar] omega :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 (by norm_num) b hb).symm
  exact p4Q2OV_originalPhysicalContinuousRepresentative_gaugeInvariant
    H v omega hRep gamma B

/-- The actual normalized joint density is invariant under the SAME
gauge transformation of both outer boundaries. -/
theorem p4Q2PZ37ACB_originalJointWeight_gaugeInvariant
    (b : ℝ) (hb : 0 ≤ b) (gamma : GT) (z : Cfg × Cfg) :
    continuousJointWeight H 2 (by norm_num) b hb (GA gamma z.1, GA gamma z.2) =
      continuousJointWeight H 2 (by norm_num) b hb z := by
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ *
      (Ω b hb (GA gamma z.1) * K b (GA gamma z.1) (GA gamma z.2) *
        Ω b hb (GA gamma z.2)) =
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ *
      (Ω b hb z.1 * K b z.1 z.2 * Ω b hb z.2)
  rw [p4Q2PZ37ACB_originalPerron_gaugeInvariant H b hb gamma z.1,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_gaugeInvariant
      H 2 b gamma z.1 z.2,
    p4Q2PZ37ACB_originalPerron_gaugeInvariant H b hb gamma z.2]

/-- The original square-root joint density, including both true Perron
factors, inherits simultaneous gauge invariance without approximation. -/
theorem p4Q2PZ37ACB_originalJointSqrtDensity_gaugeInvariant
    (b : ℝ) (hb : 0 ≤ b) (gamma : GT) (z : Cfg × Cfg) :
    sqrtD b hb (GA gamma z.1, GA gamma z.2) = sqrtD b hb z := by
  unfold continuousJointSqrtDensity
  rw [p4Q2PZ37ACB_originalJointWeight_gaugeInvariant H b hb gamma z]

private theorem p4Q2PZ37ACB_centeredRepresentative_ae :
    (fun A : Cfg => (fH : Lp ℝ 2 haar) A) =ᵐ[haar]
      p4Q2PZ37AAU_originalCenteredWilsonContinuous H := by
  rw [p4Q2PZ37AAU_originalCenteredWilsonPhysical_eq_continuousLp H]
  exact (p4Q2PZ37AAU_originalCenteredWilsonContinuous H).coeFn_toLp
    (p := 2) (𝕜 := ℝ) haar

/-- The unchanged centered physical source has gauge-invariant genuine
one-slab transfer values. Its spatial Haar centering scalar is retained. -/
theorem p4Q2PZ37ACB_centeredPhysicalTransfer_gaugeInvariant
    (b : ℝ) (gamma : GT) (B : Cfg) :
    I b fH (GA gamma B) = I b fH B := by
  let psi : C(Cfg, ℝ) := p4Q2PZ37AAU_originalCenteredWilsonContinuous H
  have hRep : (fun A : Cfg => (fH : Lp ℝ 2 haar) A) =ᵐ[haar] psi :=
    p4Q2PZ37ACB_centeredRepresentative_ae H
  have hPsi : ∀ delta : GT, ∀ A : Cfg, psi (GA delta A) = psi A :=
    fun delta A => p4Q2OV_originalPhysicalContinuousRepresentative_gaugeInvariant
      H fH psi hRep delta A
  exact p4Q2LK_originalPhysicalTransfer_gaugeInvariant_of_continuousRepresentative
    H b fH psi hRep hPsi gamma B

/-- A genuine lattice gauge transformation, with the actual SU(2)
central minus identity only at the chosen link's source vertex. -/
noncomputable def p4Q2PZ37ACB_originalCenterGauge (e : Link) : GT :=
  Function.update (fun _ : PeriodicHypercubicEvenSpatialSliceVertex H => (1 : G)) e.1 c

/-- The SAME gauge transformation acts on both original outer contexts. -/
noncomputable def p4Q2PZ37ACB_originalCenterGaugePair
    (e : Link) (z : Cfg × Cfg) : Cfg × Cfg :=
  (GA (p4Q2PZ37ACB_originalCenterGauge H e) z.1,
    GA (p4Q2PZ37ACB_originalCenterGauge H e) z.2)
local notation "gamma" => p4Q2PZ37ACB_originalCenterGauge H
local notation "Γ" => p4Q2PZ37ACB_originalCenterGaugePair H

private theorem p4Q2PZ37ACB_gauge_update
    (delta : GT) (B : Cfg) (e : Link) (g : G) :
    GA delta (Function.update B e g) =
      Function.update (GA delta B) e
        (delta e.1 * g * (delta (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹) := by
  funext k
  change delta k.1 * (Function.update B e g) k *
      (delta (periodicHypercubicEvenSpatialSliceShift H k.1 k.2))⁻¹ = _
  by_cases hk : k = e
  · subst k
    simp only [Function.update_same]
  · simp only [Function.update_of_ne hk]

/-- Actual right-link replacement commutes with the central gauge action
with insertion c*g. This is literal Function.update, not relative multiplication. -/
theorem p4Q2PZ37ACB_originalCenterGauge_update
    (e : Link) (B : Cfg) (g : G) :
    GA (gamma e) (Function.update B e g) =
      Function.update (GA (gamma e) B) e (c * g) := by
  have hSource : gamma e e.1 = c := by
    simp [p4Q2PZ37ACB_originalCenterGauge]
  have hTarget : gamma e (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) = 1 := by
    simp [p4Q2PZ37ACB_originalCenterGauge,
      p4Q2LK_originalSpatialLink_target_ne_source H e]
  rw [p4Q2PZ37ACB_gauge_update H (gamma e) B e g, hSource, hTarget]
  simp only [inv_one, mul_one]

/-- The original positive Perron/transfer prefactor is unchanged. -/
theorem p4Q2PZ37ACB_originalPrefactor_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    P b hb (Γ e z) = P b hb z := by
  unfold p4Q2PZ37ABZ_originalTransferSectionPrefactor
  exact congrArg (fun x : ℝ =>
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ * x)
    (p4Q2PZ37ACB_originalJointSqrtDensity_gaugeInvariant H b hb (gamma e) z)

private theorem p4Q2PZ37ACB_centeredTransferSection_equivariant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (g : G) :
    U b hb fH e (Γ e z) (c * g) = U b hb fH e z g := by
  change
    I b fH (Function.update (GA (gamma e) z.2) e (c * g)) /
        sqrtD b hb (GA (gamma e) z.1, Function.update (GA (gamma e) z.2) e (c * g)) =
      I b fH (Function.update z.2 e g) / sqrtD b hb (z.1, Function.update z.2 e g)
  rw [← p4Q2PZ37ACB_originalCenterGauge_update H e z.2 g,
    p4Q2PZ37ACB_centeredPhysicalTransfer_gaugeInvariant
      H b (gamma e) (Function.update z.2 e g),
    p4Q2PZ37ACB_originalJointSqrtDensity_gaugeInvariant
      H b hb (gamma e) (z.1, Function.update z.2 e g)]

/-- Exact antipodal transport of the SAME centered-source transfer section,
with the updated genuine joint Perron half-density still in its denominator. -/
theorem p4Q2PZ37ACB_centeredTransferSection_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (g : G) :
    U b hb fH e (Γ e z) g = U b hb fH e z (c * g) := by
  have h := p4Q2PZ37ACB_centeredTransferSection_equivariant H b hb e z (c * g)
  simpa only [← mul_assoc, p4Q2PZ37ABV_centralMinusOne_mul_self, one_mul] using h

/-- The original FF receiver of the actual centered Gauss-law source obeys
the same antipodal transport; both its constant term and true prefactor agree. -/
theorem p4Q2PZ37ACB_centeredReceiver_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (g : G) :
    F b hb fH e (Γ e z) g = F b hb fH e z (c * g) := by
  unfold p4Q2PZ37ABZ_originalReceiverSection
  rw [p4Q2PZ37ABZ_originalResponse_eq_transferSection,
    p4Q2PZ37ABZ_originalResponse_eq_transferSection,
    p4Q2PZ37ACB_originalPrefactor_centerGauge H b hb e z,
    p4Q2PZ37ACB_centeredTransferSection_centerGauge H b hb e z g]
  have hI := p4Q2PZ37ACB_centeredPhysicalTransfer_gaugeInvariant H b (gamma e) z.2
  change I b fH (Γ e z).2 = I b fH z.2 at hI
  rw [hI]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalPerron_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalJointWeight_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalJointSqrtDensity_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredPhysicalTransfer_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalCenterGauge_update
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalPrefactor_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredTransferSection_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredReceiver_centerGauge

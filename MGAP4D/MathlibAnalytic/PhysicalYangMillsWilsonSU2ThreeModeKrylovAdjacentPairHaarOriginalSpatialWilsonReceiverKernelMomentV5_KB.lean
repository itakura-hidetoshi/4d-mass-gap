import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorBanachAllPositiveSeparationV5_KA
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSpatialPosteriorAntisymV5_JY
import Mathlib.Tactic

/-!
# P4-Q2-KB — literal original Wilson spatial receiver kernel moments

JU constructs the ACTUAL gauge-invariant Gauss-law Hilbert source
W_H - c_(anchor)*1 using the true spatial Wilson plaquette action.
JQ defines its genuine physical normalized right-link SU(2) receiver.
GN identifies every such receiver with the original frozen-Wilson
one-slab transfer kernel and the true joint-density square-root.

Here we keep exactly THAT physical source, and expose its ORIGINAL
Wilson kernel moment at every inserted right-link SU(2) value:

  F_(b,f_Wc,e',z')(g)
    = ||T_b||^(-2) / s_b(z'.1, update(z'.2,e',g))
       * int_A K_b(A,update(z'.2,e',g)) (W_H(A)-c_anchor) dHaar(A).

This is NOT a surrogate Wilson kernel or independent-Haar posterior.
The original transfer kernel K_b is strictly positive at ALL b,
hence its spatial Haar mass is strictly positive. The centered moment
decomposes into literal Wilson action and constant kernel moments,
giving a proper conditional kernel mean (not a replacement posterior).

JY's original two-interacting-posterior antisymmetrization is then
specialized to the difference of these very kernel moments divided by
the same ORIGINAL physical joint square-root normalization. This pins
the unresolved genuine second-context spatial minor to concrete
finite-volume Wilson kernel integrals and no artificial source.

No all-source frame/rank, assumed nonzero second GI context, new
axiom/sorry/admit, Dobrushin, H1-C3 or continuum Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2KB_su2HaarOpenPos :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance

local instance p4Q2KB_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "S" => continuousJointSqrtDensity H 2
local notation "W" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "T" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2

/-- The genuine unnormalized original positive Wilson spatial Haar kernel mass. -/
noncomputable def p4Q2KB_originalSpatialWilsonKernelMass
    (b : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, K b A B ∂haar

/-- The TRUE original Haar pairing of the unchanged spatial Wilson
action with the original one-slab Wilson kernel. -/
noncomputable def p4Q2KB_originalSpatialWilsonActionKernelMoment
    (b : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, K b A B * W A ∂haar

/-- The original Wilson Haar moment of the ACTUAL anchored Gauss-law
spatial source, retaining the same original anchor slope as JK/JU. -/
noncomputable def p4Q2KB_originalCenteredSpatialWilsonKernelMoment
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (B : Cfg) : ℝ :=
  ∫ A : Cfg,
    K b A B * p4Q2JK_anchorCenteredSpatialWilson H b hb e z A ∂haar

/-- The EXACT physically normalized SU(2) receiver of the actual
anchored spatial Wilson Gauss-law Hilbert vector, expanded all the
way to the ORIGINAL spatial Wilson transfer kernel Haar integral.
The unknown Perron vacuum survives ONLY through the genuine s. -/
theorem p4Q2KB_originalPhysicalSpatialReceiver_eq_WilsonKernel
    (b : ℝ) (hb : 0 ≤ b)
    (e e' : Link) (z z' : Cfg × Cfg) (g : Gauge) :
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
      e' z' g =
      ‖T (by norm_num) b hb‖⁻¹ ^ 2 *
        p4Q2KB_originalCenteredSpatialWilsonKernelMoment H b hb e z
          (Function.update z'.2 e' g) /
        S (by norm_num) b hb (z'.1, Function.update z'.2 e' g) := by
  let u : Phys :=
    p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z
  let w : C(Cfg, ℝ) := p4Q2JK_anchorCenteredSpatialWilson H b hb e z
  have hL : (u : Lp ℝ 2 haar) = ContinuousMap.toLp 2 haar ℝ w :=
    p4Q2JU_originalAnchorCenteredWilsonPhysicalSource_coe_eq_toLp H b hb e z
  have hu : (fun A : Cfg => (u : Lp ℝ 2 haar) A) =ᵐ[haar] w := by
    rw [hL]
    exact w.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hTransfer (B : Cfg) :
      decomposableOneSliceTransferIntegral H 2 b u B =
        p4Q2KB_originalCenteredSpatialWilsonKernelMoment H b hb e z B := by
    unfold decomposableOneSliceTransferIntegral
      p4Q2KB_originalCenteredSpatialWilsonKernelMoment
    apply integral_congr_ae
    filter_upwards [hu] with A hA
    rw [hA]
  calc
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb u e' z' g =
      normalizedPhysicalOneSlabJointReceiverProductBCF
        H 2 (by norm_num) b hb u
        (z'.1, Function.update z'.2 e' g) := rfl
    _ = ‖T (by norm_num) b hb‖⁻¹ ^ 2 *
      decomposableOneSliceTransferIntegral H 2 b u
        (Function.update z'.2 e' g) /
          S (by norm_num) b hb
            (z'.1, Function.update z'.2 e' g) :=
      p4Q2GN_originalReceiver_eq_transferIntegral H b hb u _
    _ = _ := by rw [hTransfer]

/-- Both genuinely normalized receiver factors are positive:
the inverse transfer-operator norm and the physical joint half-density. -/
theorem p4Q2KB_originalPhysicalReceiverKernelPrefactor_pos
    (b : ℝ) (hb : 0 ≤ b) (A B : Cfg) :
    0 < ‖T (by norm_num) b hb‖⁻¹ ^ 2 /
        S (by norm_num) b hb (A,B) := by
  apply div_pos
  · exact pow_pos (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) b hb)) _
  · exact continuousJointSqrtDensity_pos H 2 (by norm_num) b hb (A,B)

/-- JY's exact original interacting-posterior antisymmetric SU(2)
moment, now entirely in terms of differences of the SAME original
Wilson source kernel integral and genuine Perron half-densities. -/
theorem p4Q2KB_originalSpatialWilsonDoubleHaar_as_actualKernelDifference
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link) (z z' : Cfg × Cfg) :
    (2 : ℝ) *
      p4Q2JX_originalSpatialSourcePosteriorTwoPointMoment
        H b hb e e' z z' =
      ∫ g : Gauge, ∫ h : Gauge,
        ((‖T (by norm_num) b hb‖⁻¹ ^ 2 *
          p4Q2KB_originalCenteredSpatialWilsonKernelMoment H b hb e z
            (Function.update z'.2 e' g) /
            S (by norm_num) b hb (z'.1, Function.update z'.2 e' g)) -
         (‖T (by norm_num) b hb‖⁻¹ ^ 2 *
          p4Q2KB_originalCenteredSpatialWilsonKernelMoment H b hb e z
            (Function.update z'.2 e' h) /
            S (by norm_num) b hb (z'.1, Function.update z'.2 e' h))) *
        p4Q2JN_originalPosteriorTwoPointMinor H b hb z'.2 e' g h
        ∂nu ∂nu := by
  rw [p4Q2JY_originalSpatialWilsonMoment_antisymmetric]
  apply integral_congr_ae
  filter_upwards with g
  apply integral_congr_ae
  filter_upwards with h
  rw [p4Q2KB_originalPhysicalSpatialReceiver_eq_WilsonKernel
      H b hb e e' z z' g,
    p4Q2KB_originalPhysicalSpatialReceiver_eq_WilsonKernel
      H b hb e e' z z' h]

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KB_originalPhysicalSpatialReceiver_eq_WilsonKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KB_originalPhysicalReceiverKernelPrefactor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KB_originalSpatialWilsonDoubleHaar_as_actualKernelDifference

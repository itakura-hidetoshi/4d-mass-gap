import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullOneSlabStrictTransferV5_LJ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import Mathlib.Tactic

/-!
# P4-Q2-LK — gauge-normalize a genuine nonzero centered Wilson transfer witness

LJ proves, from the LITERAL original full finite-volume SU(2) one-slab
Wilson Haar kernel strict positivity, that the ACTUAL original centered
spatial Wilson Gauss-law Hilbert source has nonzero original transfer
at some real right boundary B.

LC needs the transfer at a right SU(2)-link insertion equal to the
identity. We close this gap using an ACTUAL spatial lattice gauge
transformation, without changing the physical source.

Every genuine spatial link e has DISTINCT endpoints for the actual
even periodic side length 2*(H+1) >= 2, by the established lattice
nondegenerate-shift theorem. Set the spatial gauge transformation
to (B e)^(-1) at the source vertex and 1 at every other vertex.
The actual SU(2) transformed right boundary has link e equal to 1.

The ORIGINAL centered spatial Wilson source is gauge invariant as a
continuous function because its Wilson action is, and its centering
scalar is constant. The complete original one-slab Wilson kernel is
simultaneously gauge invariant. The genuine spatial product Haar
is measure preserving under the SAME gauge transformation. Using the
existing measurable equivalence, the literal original continuous
Wilson transfer integral is therefore gauge invariant at the right
boundary. The physical Gauss-law L2 transfer agrees with this same
genuine integral via LJ's verified original continuous representative.

Thus LJ's arbitrary nonzero transfer witness can be gauge-fixed to
a nonzero transfer with a specified right link equal to SU(2) 1,
which is precisely the original LC frozen-right identity witness.

No rank/frame hypothesis, posterior substitution, synthetic source,
new axiom, sorry/admit, H1-C3 or continuum Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GT" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "GaugeAct" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2

/-- The two endpoints of ANY original physical spatial link in the
finite even-periodic H-lattice are genuinely distinct, also at H=0. -/
theorem p4Q2LK_originalSpatialLink_target_ne_source
    (e : Link) :
    periodicHypercubicEvenSpatialSliceShift H e.1 e.2 ≠ e.1 := by
  have hn : 2 ≤ PeriodicHypercubicEvenSideLength H := by
    dsimp [PeriodicHypercubicEvenSideLength]
    omega
  intro hs
  have hbase :
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
          e.1.1 e.2.1 = e.1.1 := by
    simpa only [periodicHypercubicEvenSpatialSliceShift_coe] using
      congrArg Subtype.val hs
  exact (periodicHypercubicShift_ne_self
    (PeriodicHypercubicEvenSideLength H) hn e.1.1 e.2.1) hbase

/-- A named ACTUAL lattice gauge transformation which sends the
original value B(e) at the chosen right link e to SU(2) identity.
The only changed gauge vertex is e's original source vertex. -/
noncomputable def p4Q2LK_originalSpatialRightLinkGaugeNormalizer
    (B : Cfg) (e : Link) : GT :=
  Function.update (fun _ : PeriodicHypercubicEvenSpatialSliceVertex H =>
    (1 : Gauge)) e.1 (B e)⁻¹

/-- Normalization is exact, on the REAL original spatial-link
gauge action, not an artificial unit-link slice. -/
theorem p4Q2LK_originalSpatialRightLinkGaugeNormalizer_apply
    (B : Cfg) (e : Link) :
    GaugeAct (p4Q2LK_originalSpatialRightLinkGaugeNormalizer H B e) B e =
      (1 : Gauge) := by
  let gamma : GT := p4Q2LK_originalSpatialRightLinkGaugeNormalizer H B e
  have hSource : gamma e.1 = (B e)⁻¹ := by
    simp [gamma, p4Q2LK_originalSpatialRightLinkGaugeNormalizer]
  have hTarget : gamma
      (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) = 1 := by
    simp [gamma, p4Q2LK_originalSpatialRightLinkGaugeNormalizer,
      (p4Q2LK_originalSpatialLink_target_ne_source H e).symm]
  change gamma e.1 * B e *
    (gamma (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹ = 1
  rw [hSource, hTarget]
  simp

/-- The actual original anchor-centered spatial Wilson action is
POINTWISE gauge invariant for every genuine spatial lattice
gauge transformation, because the original Wilson action is and
the anchor-center scalar is constant. -/
theorem p4Q2LK_originalCenteredSpatialWilson_gaugeInvariant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (gamma : GT) (A : Cfg) :
    p4Q2JK_anchorCenteredSpatialWilson H b hb e z (GaugeAct gamma A) =
      p4Q2JK_anchorCenteredSpatialWilson H b hb e z A := by
  unfold p4Q2JK_anchorCenteredSpatialWilson
  change
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
        (GaugeAct gamma A) -
      p4Q2JK_originalWilsonAnchorSlope H b hb e z * (1 : ℝ) =
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A -
      p4Q2JK_originalWilsonAnchorSlope H b hb e z * (1 : ℝ)
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant]

/-- Any ACTUAL Gauss-law physical Hilbert source with a genuine
pointwise gauge-invariant continuous original spatial
representative has gauge-invariant literal one-slab transfer values.
The proof changes variable by the true Haar-preserving spatial
gauge measurable equivalence and uses the ORIGINAL full Wilson
kernel's simultaneous gauge invariance. -/
theorem p4Q2LK_originalPhysicalTransfer_gaugeInvariant_of_continuousRepresentative
    (b : ℝ) (f : Phys) (psi : C(Cfg, ℝ))
    (hRep : (fun A : Cfg => (f : Lp ℝ 2 haar) A) =ᵐ[haar] psi)
    (hPsi : ∀ gamma : GT, ∀ A : Cfg, psi (GaugeAct gamma A) = psi A)
    (gamma : GT) (B : Cfg) :
    decomposableOneSliceTransferIntegral H 2 b f (GaugeAct gamma B) =
      decomposableOneSliceTransferIntegral H 2 b f B := by
  let T : Cfg → Cfg := GaugeAct gamma
  let F : Cfg → ℝ := fun A => K b A (T B) * psi A
  have hMP : MeasurePreserving T haar haar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
      H 2 gamma
  have hME : MeasurableEmbedding T := by
    simpa only [T, periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeMeasurableEquiv] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeMeasurableEquiv
        H 2 gamma).measurableEmbedding
  calc
    decomposableOneSliceTransferIntegral H 2 b f (T B) =
        ∫ A : Cfg, K b A (T B) * psi A ∂haar :=
      p4Q2LJ_originalPhysicalTransfer_eq_continuousWilsonKernelIntegral
        H b f psi hRep (T B)
    _ = ∫ A : Cfg, K b (T A) (T B) * psi (T A) ∂haar := by
      exact (hMP.integral_comp hME F).symm
    _ = ∫ A : Cfg, K b A B * psi A ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_gaugeInvariant
        H 2 b gamma A B, hPsi gamma A]
    _ = decomposableOneSliceTransferIntegral H 2 b f B :=
      (p4Q2LJ_originalPhysicalTransfer_eq_continuousWilsonKernelIntegral
        H b f psi hRep B).symm

/-- The actual anchor-centered Gauss-law physical Wilson source's
ORIGINAL transfer is unchanged by every genuine full spatial
lattice gauge transformation of its right boundary. -/
theorem p4Q2LK_originalCenteredSpatialWilsonPhysicalTransfer_gaugeInvariant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (gamma : GT) (B : Cfg) :
    decomposableOneSliceTransferIntegral H 2 b
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
      (GaugeAct gamma B) =
    decomposableOneSliceTransferIntegral H 2 b
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z) B := by
  let psi : C(Cfg, ℝ) := p4Q2JK_anchorCenteredSpatialWilson H b hb e z
  have hLp :
      ((p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
            H b hb e z : Phys) : Lp ℝ 2 haar) =
        ContinuousMap.toLp 2 haar ℝ psi :=
    p4Q2JU_originalAnchorCenteredWilsonPhysicalSource_coe_eq_toLp
      H b hb e z
  have hRep :
      (fun A : Cfg =>
        ((p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
          H b hb e z : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] psi := by
    rw [hLp]
    exact psi.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  exact
    p4Q2LK_originalPhysicalTransfer_gaugeInvariant_of_continuousRepresentative
      H b
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
      psi hRep
      (fun gamma A =>
        p4Q2LK_originalCenteredSpatialWilson_gaugeInvariant
          H b hb e z gamma A)
      gamma B

/-- Core LC identity-fiber witness WITHOUT rank hypotheses:
for any actual physical right link e' and positive coupling,
the ACTUAL centered Wilson Gauss-law source has NONZERO original
one-slab transfer at some actual right boundary with e' exactly
SU(2) identity. Derived from LJ nonzero transfer, true lattice
gauge normalization, and verified original transfer covariance. -/
theorem p4Q2LK_originalCenteredSpatialWilsonPhysicalTransfer_nonzero_at_identityFiber
    (b : ℝ) (hb : 0 < b)
    (e e' : Link) (z : Cfg × Cfg) :
    ∃ R : Cfg,
      decomposableOneSliceTransferIntegral H 2 b
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
        (Function.update R e' (1 : Gauge)) ≠ 0 := by
  obtain ⟨B, hB⟩ :=
    p4Q2LJ_originalCenteredSpatialWilsonPhysicalTransfer_exists_nonzero
      H b hb e z
  let gamma : GT :=
    p4Q2LK_originalSpatialRightLinkGaugeNormalizer H B e'
  let R : Cfg := GaugeAct gamma B
  have hIdentity : R e' = (1 : Gauge) :=
    p4Q2LK_originalSpatialRightLinkGaugeNormalizer_apply H B e'
  have hUpd : Function.update R e' (1 : Gauge) = R := by
    funext k
    by_cases hk : k = e'
    · subst k
      simp [hIdentity]
    · simp [Function.update, hk]
  have hCov :
      decomposableOneSliceTransferIntegral H 2 b
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z) R =
      decomposableOneSliceTransferIntegral H 2 b
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z) B :=
    p4Q2LK_originalCenteredSpatialWilsonPhysicalTransfer_gaugeInvariant
      H b hb.le e z gamma B
  refine ⟨R, ?_⟩
  rw [hUpd, hCov]
  exact hB

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LK_originalSpatialLink_target_ne_source
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LK_originalSpatialRightLinkGaugeNormalizer_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LK_originalCenteredSpatialWilson_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LK_originalPhysicalTransfer_gaugeInvariant_of_continuousRepresentative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LK_originalCenteredSpatialWilsonPhysicalTransfer_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LK_originalCenteredSpatialWilsonPhysicalTransfer_nonzero_at_identityFiber

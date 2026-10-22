import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPhysicalTransferContinuousRangeV5_OU
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

/-!
# P4-Q2-OV — genuine continuous Gauss-law Wilson range is gauge invariant

OU proves that the actual normalized original Wilson physical one-slab
transfer maps every true Gauss-law Hilbert L² input to a genuine continuous
spatial Haar-L² representative. The physical codomain is the ACTUAL
Gauss-law fixed submodule, but an arbitrary continuous representative
must still be shown invariant POINTWISE, not merely almost everywhere.

This module removes that obstruction using the original SU(2) spatial
lattice gauge action, genuine product Haar measure with full topological
support, exact Lp gauge pullback equality and mathlib's injectivity
of continuous-to-Lp. Hence EVERY continuous representative of a true
Gauss-law source is pointwise lattice gauge invariant.

Consequently every output of the ORIGINAL normalized positive-fine
physical Wilson transfer has an invariant continuous representative
and is nontrivially detected by the ORIGINAL two-interacting-posterior
signed GI receiver, whenever that same actual physical output is nonzero.
This last clause does NOT assume Wilson transfer injectivity, nor
does it establish the original depth-two Schur physical source nonzero.

No alternative kernel, independent Haar posterior, Dobrushin,
arbitrary rank axiom, sorry/admit, uniform U0, endpoint or mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2OV_specialUnitaryNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance p4Q2OV_specialUnitaryHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4Q2OV_spatialFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2OV_spatialProductHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section PhysicalGaugeContinuous
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "GT" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "GaugeAct" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "NTransfer" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive

/-- The ACTUAL full lattice gauge action is continuous on the
compact SU(2) spatial-link configuration carrier. -/
theorem p4Q2OV_originalSpatialGaugeAction_continuous (gamma : GT) :
    Continuous (GaugeAct gamma) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
  fun_prop

/-- Every CONTINUOUS Haar-L² representative of a genuine physical
Gauss-law source is invariant pointwise under all original spatial
lattice SU(2) gauge transformations. Equality a.e. becomes equality
EVERYWHERE by full-support original product Haar and the standard
continuous-to-L² injectivity theorem of mathlib. -/
theorem p4Q2OV_originalPhysicalContinuousRepresentative_gaugeInvariant
    (f : Phys) (psi : C(Cfg, ℝ))
    (hRep : (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] psi)
    (gamma : GT) (B : Cfg) :
    psi (GaugeAct gamma B) = psi B := by
  let phi : C(Cfg, ℝ) :=
    ⟨fun A => psi (GaugeAct gamma A),
      psi.continuous.comp (p4Q2OV_originalSpatialGaugeAction_continuous H gamma)⟩
  let fLp : Lp ℝ 2 haar := (f : Lp ℝ 2 haar)
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar :=
    ContinuousMap.toLp 2 haar ℝ
  let gaugePull :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
      H 2 gamma
  have hFLp : fLp = L psi := by
    apply Lp.ext
    exact hRep.trans (psi.coeFn_toLp (p := 2) (𝕜 := ℝ) haar).symm
  have hGaugeLp : gaugePull fLp = fLp := f.property gamma
  have hCompAE :
      (fun A : Cfg => (L psi) (GaugeAct gamma A)) =ᵐ[haar]
        (fun A : Cfg => psi (GaugeAct gamma A)) := by
    have hMP :=
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving
        H 2 gamma).quasiMeasurePreserving
    simpa only [Function.comp_def] using
      (hMP.ae_eq (psi.coeFn_toLp (p := 2) (𝕜 := ℝ) haar))
  have hGaugeToLp : gaugePull (L psi) = L phi := by
    apply Lp.ext
    have hPull :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
        H 2 gamma (L psi)
    have hPhi := phi.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
    exact (hPull.trans hCompAE).trans hPhi.symm
  have hEqualToLp : L phi = L psi := by
    calc
      L phi = gaugePull (L psi) := hGaugeToLp.symm
      _ = gaugePull fLp := by rw [hFLp]
      _ = fLp := hGaugeLp
      _ = L psi := hFLp
  have hContinuousEqual : phi = psi :=
    (ContinuousMap.toLp_injective
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (μ := haar)) hEqualToLp
  exact congrArg (fun g : C(Cfg, ℝ) => g B) hContinuousEqual

/-- OU's genuine continuous representative now satisfies ALL of OT's
true lattice-gauge invariance requirements, for EVERY original
normalized one-slab physical Wilson transfer output. -/
theorem p4Q2OV_originalNormalizedPhysicalTransfer_hasGaugeContinuousRepresentative
    (t : ℝ) (ht : 0 ≤ t) (f : Phys) :
    p4Q2OT_hasGaugeContinuousRepresentative H (NTransfer t ht f) := by
  obtain ⟨psi, hRep⟩ :=
    p4Q2OU_originalNormalizedPhysicalTransfer_hasContinuousRepresentative
      H t ht f
  exact ⟨psi, hRep, fun gamma A =>
    p4Q2OV_originalPhysicalContinuousRepresentative_gaugeInvariant
      H (NTransfer t ht f) psi hRep gamma A⟩

/-- For any positive genuine frozen coupling b, nonnegative fine
coupling t, actual Gauss-law input f and any chosen original spatial
link, a NONZERO actual normalized fine Wilson physical OUTPUT is
detected by some genuine original interacting-two-posterior GI
receiver context. Nonzero output is required, not postulated from
the nonzero input. -/
theorem p4Q2OV_originalNormalizedPhysicalTransfer_nonzero_trueGI
    (b : ℝ) (hb : 0 < b) (t : ℝ) (ht : 0 ≤ t)
    (f : Phys) (hTf : NTransfer t ht f ≠ 0)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) (left₀ : Cfg) :
    ∃ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (NTransfer t ht f) e z ≠ 0 := by
  exact p4Q2OT_originalContinuousPhysical_nonzero_genuineGI
    H b hb (NTransfer t ht f) hTf
    (p4Q2OV_originalNormalizedPhysicalTransfer_hasGaugeContinuousRepresentative
      H t ht f) e left₀

end PhysicalGaugeContinuous
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OV_originalSpatialGaugeAction_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OV_originalPhysicalContinuousRepresentative_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OV_originalNormalizedPhysicalTransfer_hasGaugeContinuousRepresentative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OV_originalNormalizedPhysicalTransfer_nonzero_trueGI

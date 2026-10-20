import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedScoreVarianceNoGoV5_MW
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

/-!
# P4-Q2-MX — real Gauss-law physical Wilson plaquette sources remain faithful
# even when the original signed interacting-posterior receiver is blind

MV proves that every genuine SU(2) spatial plaquette Wilson observable
takes distinct values 0 and 2 on two true configurations and that its
positive-original-Wilson-kernel conditional variance is strictly positive.

MW proves the ORIGINAL signed two-interacting-Wilson posterior detector
can nevertheless annihilate all centered physical sources: at frozen
beta=0 its authentic signed score is identically zero.

MX separates *source Hilbert geometry* from *signed detector response*
on the SAME authentic SU(2) periodic Wilson model. Because the
original product spatial Haar has FULL support, pinned mathlib's
ContinuousMap.toLp_injective identifies continuous spatial observable
equalities from actual ambient Haar-L² source equalities.

For EVERY spatial SU(2) plaquette p, the true Gauss-law physical
two-source map
       (x,y) ↦ x U + y W_(H,p) U
is injective (hence U and W_(H,p)U are real linearly independent) on
the actual original gauge-invariant Hilbert submodule, at ALL finite
H, using MV's *true* two-configuration nonconstancy. There is NO
formal rank assumption or postulated independent source.

For EVERY actual frozen right-boundary z and beta>=0, MS's genuine
Wilson-kernel-centered Gauss-law physical plaquette source
       W_(H,p)U - E_{K_b(.,z.right)}[W_(H,p)] U
is also nonzero and has strictly positive physical Hilbert norm.
This is a real physical source, not an arbitrary numerical probe.

At TRUE beta=0 this nonzero centered Gauss-law physical source
nevertheless has exactly ZERO authentic signed GI response, by MW's
proved beta-zero equality of ORIGINAL interacting posterior rows.
Meanwhile MV guarantees strictly positive genuine spatial plaquette
variance. This is a concrete unambiguous intrinsic detector NO-GO:
positive source variance / nonzero physical source cannot establish
positive signed GI response or covariance.

No claim of positive-beta score variance, any uniform source lower
norm, H-uniform original GI coercivity, spatial decay, H1-C3 closure
or continuum Yang-Mills mass gap. No independent-Haar model,
Dobrushin hypothesis, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2MX_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4Q2MX_spatialHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section Sources
variable (H : ℕ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Wp" => p4Q2LO_originalLocalPlaquettePhysicalSource H
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "Src" => p4Q2LO_originalPhysicalLocalTwoSource H

/-- Faithful continuous ambient Haar-L² representative of the ACTUAL
two-dimensional Gauss-law physical source x U + y W_(H,p)U.
Uses existing physical Wilson multiplication and actual Haar carrier,
not a synthetic source plane. -/
theorem p4Q2MX_originalPhysicalTwoSource_coe_eq_toLp
    (p : Plaq) (x y : ℝ) :
    ((Src p x y : Phys) : Lp ℝ 2 haar) =
      L (x • (1 : C(Cfg, ℝ)) + y • w p) := by
  change ((x • U + y • Wp p : Phys) : Lp ℝ 2 haar) =
    L (x • (1 : C(Cfg, ℝ)) + y • w p)
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp,
    p4Q2LO_originalLocalPlaquettePhysicalSource_coe_eq_toLp,
    map_add, map_smul, map_smul]

/-- The REAL ORIGINAL two-source physical Wilson map has trivial
kernel for EVERY genuine SU(2) spatial plaquette, because its
continuous representatives are distinguished by MV's two actual
physical configurations. Full-support Haar injectivity is from
pinned mathlib; no rank or coercivity hypothesis is inserted. -/
theorem p4Q2MX_originalPhysicalTwoSource_coefficients_zero
    (p : Plaq) (x y : ℝ) (hz : Src p x y = 0) :
    x = 0 ∧ y = 0 := by
  have hLpZero :
      L (x • (1 : C(Cfg, ℝ)) + y • w p) = 0 := by
    rw [← p4Q2MX_originalPhysicalTwoSource_coe_eq_toLp H p x y]
    simp [hz]
  have hFn :
      x • (1 : C(Cfg, ℝ)) + y • w p = 0 := by
    apply (ContinuousMap.toLp_injective (𝕜 := ℝ)
      (p := (2 : ENNReal)) (μ := haar))
    simpa using hLpZero
  have hAt (A : Cfg) : x + y * w p A = 0 := by
    have h := congrArg (fun f : C(Cfg, ℝ) => f A) hFn
    simpa only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, ContinuousMap.zero_apply,
      smul_eq_mul, mul_one] using h
  obtain ⟨A₀,A₁,hDiff⟩ :=
    p4Q2MV_originalSpatialPlaquette_nonconstant H p
  have h0 := hAt A₀
  have h1 := hAt A₁
  have hy : y = 0 := by
    have hProd : y * (w p A₀ - w p A₁) = 0 := by
      nlinarith [h0, h1]
    rcases mul_eq_zero.mp hProd with hY | hW
    · exact hY
    · exact False.elim (hDiff (sub_eq_zero.mp hW))
  have hx : x = 0 := by
    simpa [hy] using h0
  exact ⟨hx,hy⟩

/-- No nontrivial real combination of the ACTUAL unit Gauss-law
physical source and a genuine Wilson local plaquette physical source
can vanish. Stronger than merely positivity of a scalar variance. -/
theorem p4Q2MX_originalPhysicalTwoSource_ne_zero
    (p : Plaq) (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    Src p x y ≠ 0 := by
  intro hzero
  obtain ⟨hx, hy⟩ :=
    p4Q2MX_originalPhysicalTwoSource_coefficients_zero H p x y hzero
  exact hxy.elim (fun h => h hx) (fun h => h hy)

/-- The genuine original constant Gauss-law state and EVERY actual
SU(2) Wilson p-local Gauss-law state are linearly independent inside
the EXISTING physical Hilbert space (not just in a surrogate L²). -/
theorem p4Q2MX_originalPhysicalUnitPlaquette_linearIndependent
    (p : Plaq) :
    LinearIndependent ℝ ![U, Wp p] := by
  apply (linearIndependent_fin2).2
  constructor
  · change Wp p ≠ 0
    intro hW
    have hSrc : Src p 0 1 = 0 := by
      simpa [p4Q2LO_originalPhysicalLocalTwoSource] using hW
    have hCoe :=
      p4Q2MX_originalPhysicalTwoSource_coefficients_zero H p 0 1 hSrc
    norm_num at hCoe
  · intro a h
    have hRel : a • Wp p = U := by
      simpa using h
    have hSrc : Src p (-1) a = 0 := by
      change (-1 : ℝ) • U + a • Wp p = 0
      rw [neg_one_smul, hRel]
      simp
    have hCoe :=
      p4Q2MX_originalPhysicalTwoSource_coefficients_zero H p (-1) a hSrc
    norm_num at hCoe

end Sources

section SourceCentering
variable (H : ℕ) (b : ℝ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Mean" => p4Q2MS_originalWilsonKernelConditionalMean H b
local notation "Var" => p4Q2MS_originalWilsonKernelConditionalVariance H b
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "Centered" => p4Q2MS_originalPhysicalCenteredWilsonPlaquetteSource H b

/-- For every finite genuine SU(2) Wilson spatial plaquette and every
actual positive original kernel section B, its genuinely centered
Gauss-law physical Hilbert source is NONZERO. This holds at beta=0 too.
It is a statement on physical source rank, not detector rank. -/
theorem p4Q2MX_originalPhysicalCenteredPlaquetteSource_ne_zero
    (z : Cfg × Cfg) (p : Plaq) :
    Centered z p ≠ 0 := by
  change p4Q2LO_originalPhysicalLocalTwoSource H p (-(Mean z (w p))) 1 ≠ 0
  exact p4Q2MX_originalPhysicalTwoSource_ne_zero
    H p (-(Mean z (w p))) 1 (Or.inr one_ne_zero)

/-- Thus EVERY genuine kernel-centered Gauss-law plaquette source has
STRICTLY POSITIVE physical Hilbert norm, without inventing any source
or requiring a receiver nondegeneracy hypothesis. -/
theorem p4Q2MX_originalPhysicalCenteredPlaquetteSource_norm_pos
    (z : Cfg × Cfg) (p : Plaq) :
    0 < ‖Centered z p‖ := by
  exact norm_pos_iff.mpr
    (p4Q2MX_originalPhysicalCenteredPlaquetteSource_ne_zero H b z p)

end SourceCentering

/-- Intrinsic, fully genuine beta=0 NO-GO:
EVERY SU(2) spatial plaquette has strictly POSITIVE Wilson
conditional variance, and its actual centered Gauss-law physical
state is NONZERO, yet that SAME state's ORIGINAL
two-interacting-Wilson-posterior signed GI detector output is ZERO.

At positive beta this counterexample does not give a sign/nonzero
certificate. It isolates physical source faithfulness from signed
receiver degeneracy, with no independent-Haar posterior substitution. -/
theorem p4Q2MX_originalBetaZero_faithfulPlaquette_blindSignedReceiver
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    0 < p4Q2MS_originalWilsonKernelConditionalVariance H 0 z
        (p4Q2LO_originalLocalPlaquetteContinuous H p) ∧
    p4Q2MS_originalPhysicalCenteredWilsonPlaquetteSource H 0 z p ≠ 0 ∧
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H 0 (le_refl (0 : ℝ))
      (p4Q2MS_originalPhysicalCenteredWilsonPlaquetteSource H 0 z p)
      e z = 0 := by
  refine ⟨p4Q2MV_originalSpatialPlaquette_kernelVariance_pos H 0 z p,
    p4Q2MX_originalPhysicalCenteredPlaquetteSource_ne_zero H 0 z p, ?_⟩
  have hZero :=
    p4Q2MW_originalSignedScoreVariance_zero_at_frozen_zero H e z
  exact p4Q2MW_originalSignedScoreVariance_zero_forces_centeredPhysicalGI_zero
    H 0 (le_refl (0 : ℝ)) e z p hZero

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MX_originalPhysicalTwoSource_coe_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MX_originalPhysicalTwoSource_coefficients_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MX_originalPhysicalTwoSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MX_originalPhysicalUnitPlaquette_linearIndependent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MX_originalPhysicalCenteredPlaquetteSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MX_originalPhysicalCenteredPlaquetteSource_norm_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MX_originalBetaZero_faithfulPlaquette_blindSignedReceiver

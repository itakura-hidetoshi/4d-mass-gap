import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonThirdMomentPosteriorMassCriterionV5_PE
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-PF — true original Wilson third Schur as a spatial point witness

PE identified D3>0 with positive ORIGINAL two-interacting-posterior
GL mass and genuine signed receiver nonzero on the actual canonical
third physical Schur source. Here supply a more DIRECT ORIGINAL WILSON
configuration-side criterion for checking that outstanding nonzero.

The unmodified normalized fine one-slab Wilson physical transfer
has by OU an ACTUAL continuous spatial-Haar representative. Define
  phi1(A) = ||T_raw||^-1 * OU_continuous(U)(A)
  phi2(A) = ||T_raw||^-1 * OU_continuous(T_fine U)(A).
In the SAME SU(2) Gauss-law physical Haar-L² carrier these are
exactly T_fine U and T_fine² U, not spectral-model surrogates.

The continuous concrete third Schur profile
  psi_R(A) = D2*phi2(A) - (m2²-m1*m3)
             - (m0*m3-m1*m2)*phi1(A)
represents PD's exact physical Schur innovation R2 in Haar-L².
Full support of ORIGINAL compact SU(2) spatial Haar implies:
  R2 != 0  <->  EXISTS actual spatial configuration A, psi_R(A) != 0.
Consequently, wherever the true D2>0, the unproved D3>0 is
equivalent to THAT concrete original Wilson spatial point witness.
Any such witness at frozen b>0 automatically gives a genuine
two-interacting-posterior signed GI receiver by OT/OV.

This isolates what must be checked on the actual one/two-slab
Wilson function values. Does NOT assert that a witness exists.
No third-rank assumption, invented spectrum, replacement posterior,
Dobrushin, sorry/admit or new axiom; no U0 or continuum claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PF_specialUnitaryNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance p4Q2PF_specialUnitaryHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4Q2PF_spatialFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PF_spatialProductHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section ActualWilsonOneTwoSlabContinuousProfiles
variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
local notation "Raw" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
local notation "m" => p4Q2PB_originalWilsonPhysicalMoment H t ht
local notation "D2" => p4Q2PD_originalWilsonTwoMomentDet H t ht
local notation "D3" => p4Q2PD_originalWilsonThirdMomentGap H t ht
local notation "R" => p4Q2PD_originalWilsonThirdSchurPhysical H t ht
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- The authentic normalized one-slab physical Wilson output on the
actual Gauss-law constant unit as a continuous boundary function. -/
noncomputable def p4Q2PF_originalWilsonOneSlabContinuous : C(Cfg, ℝ) :=
  ‖Raw‖⁻¹ • p4Q2OU_originalPhysicalTransferContinuous H t ht U

/-- The authentic original two-slab normalized physical Wilson
output, not a model substituted Markov or independent-Haar kernel. -/
noncomputable def p4Q2PF_originalWilsonTwoSlabContinuous : C(Cfg, ℝ) :=
  ‖Raw‖⁻¹ • p4Q2OU_originalPhysicalTransferContinuous H t ht (Fine U)

/-- Explicit genuine spatial configuration function whose Haar-L²
class is exactly the original PD third moment physical Schur source. -/
noncomputable def p4Q2PF_originalWilsonThirdSchurContinuous : C(Cfg, ℝ) :=
  D2 • p4Q2PF_originalWilsonTwoSlabContinuous H t ht -
    ((m 2) ^ 2 - m 1 * m 3) • (1 : C(Cfg, ℝ)) -
    (m 0 * m 3 - m 1 * m 2) •
      p4Q2PF_originalWilsonOneSlabContinuous H t ht

/-- Exact original normalized physical one-slab/Haar-L² match. -/
theorem p4Q2PF_originalOneSlabContinuous_toLp :
    ((Fine U : Phys) : Lp ℝ 2 haar) =
      L (p4Q2PF_originalWilsonOneSlabContinuous H t ht) := by
  simpa only [p4Q2PF_originalWilsonOneSlabContinuous] using
    (p4Q2OU_originalNormalizedPhysicalTransferContinuous_toLp H t ht U)

/-- Exact original normalized physical two-slab/Haar-L² match,
using a SECOND step of the SAME genuine Wilson normalized transfer. -/
theorem p4Q2PF_originalTwoSlabContinuous_toLp :
    (((Fine ^ 2) U : Phys) : Lp ℝ 2 haar) =
      L (p4Q2PF_originalWilsonTwoSlabContinuous H t ht) := by
  have hPow : (Fine ^ 2) U = Fine (Fine U) := by
    -- Restrict rewriting to the exponent: replacing the numeral 2
    -- globally would also rewrite the SU(2) group index and hN : 0 < 2.
    change (Fine ^ (1 + 1)) U = Fine (Fine U)
    rw [pow_succ']
    simp
  rw [hPow]
  simpa only [p4Q2PF_originalWilsonTwoSlabContinuous] using
    (p4Q2OU_originalNormalizedPhysicalTransferContinuous_toLp
      H t ht (Fine U))

/-- The explicit genuine original Wilson continuous two-slab Schur
profile has precisely the SAME Haar-L² class as PD's physical
Schur residual, including the TRUE normalization and both
Wilson halfweights. This is an operator identity, not a rank axiom. -/
theorem p4Q2PF_originalThirdSchurContinuous_toLp :
    ((R : Phys) : Lp ℝ 2 haar) =
      L (p4Q2PF_originalWilsonThirdSchurContinuous H t ht) := by
  let incl : Phys →ₗ[ℝ] Lp ℝ 2 haar :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      H 2).subtype
  have h0 : ((U : Phys) : Lp ℝ 2 haar) =
      L (1 : C(Cfg, ℝ)) :=
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H
  have h1 := p4Q2PF_originalOneSlabContinuous_toLp H t ht
  have h2 := p4Q2PF_originalTwoSlabContinuous_toLp H t ht
  calc
    ((R : Phys) : Lp ℝ 2 haar) =
        incl (D2 • ((Fine ^ 2) U) -
          ((m 2) ^ 2 - m 1 * m 3) • U -
          (m 0 * m 3 - m 1 * m 2) • (Fine U)) := by rfl
    _ = D2 • (((Fine ^ 2) U : Phys) : Lp ℝ 2 haar) -
          ((m 2) ^ 2 - m 1 * m 3) • ((U : Phys) : Lp ℝ 2 haar) -
          (m 0 * m 3 - m 1 * m 2) • ((Fine U : Phys) : Lp ℝ 2 haar) := by
            rw [map_sub, map_sub, map_smul, map_smul, map_smul]
            rfl
    _ = D2 • L (p4Q2PF_originalWilsonTwoSlabContinuous H t ht) -
          ((m 2) ^ 2 - m 1 * m 3) • L (1 : C(Cfg, ℝ)) -
          (m 0 * m 3 - m 1 * m 2) •
            L (p4Q2PF_originalWilsonOneSlabContinuous H t ht) := by
              rw [h0, h1, h2]
    _ = L (p4Q2PF_originalWilsonThirdSchurContinuous H t ht) := by
          simp only [p4Q2PF_originalWilsonThirdSchurContinuous,
            map_sub, map_smul]

/-- The same authentic original spatial Wilson Schur function is
pointwise gauge invariant, by OV and full-support genuine spatial
Haar; not merely invariant in its Haar-L² equivalence class. -/
theorem p4Q2PF_originalThirdSchurContinuous_gaugeInvariant
    (gamma : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2)
    (A : Cfg) :
    p4Q2PF_originalWilsonThirdSchurContinuous H t ht
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 gamma A) =
    p4Q2PF_originalWilsonThirdSchurContinuous H t ht A := by
  let psi := p4Q2PF_originalWilsonThirdSchurContinuous H t ht
  have hRep :
      (fun B : Cfg => ((R : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar] psi := by
    rw [p4Q2PF_originalThirdSchurContinuous_toLp H t ht]
    exact psi.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  exact p4Q2OV_originalPhysicalContinuousRepresentative_gaugeInvariant
    H R psi hRep gamma A

/-- A single specific original spatial gauge configuration with
nonzero TRUE Wilson two-slab Schur function forces the ACTUAL
Gauss-law Hilbert Schur physical source nonzero, using Mathlib
continuous-to-L² injectivity and original product Haar full support. -/
theorem p4Q2PF_originalThirdSchur_point_ne_zero_implies_physicalNonzero
    (A : Cfg)
    (hPoint : p4Q2PF_originalWilsonThirdSchurContinuous H t ht A ≠ 0) :
    R ≠ 0 := by
  let psi : C(Cfg, ℝ) :=
    p4Q2PF_originalWilsonThirdSchurContinuous H t ht
  intro hR
  have hLp :
      L psi = L (0 : C(Cfg, ℝ)) := by
    rw [← p4Q2PF_originalThirdSchurContinuous_toLp H t ht]
    rw [hR]
    simp
  have hPsi : psi = 0 :=
    (ContinuousMap.toLp_injective
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (μ := haar)) hLp
  have hAt := congrArg (fun g : C(Cfg, ℝ) => g A) hPsi
  exact hPoint (by simpa [psi] using hAt)

/-- If the authentic third physical Schur Hilbert source is nonzero,
the continuous ORIGINAL two-slab Wilson function must differ at
some actual spatial configuration. The witness does not presuppose
a spectral measure with three support points. -/
theorem p4Q2PF_originalThirdSchur_physicalNonzero_implies_exists_point
    (hR : R ≠ 0) :
    ∃ A : Cfg,
      p4Q2PF_originalWilsonThirdSchurContinuous H t ht A ≠ 0 := by
  let psi : C(Cfg, ℝ) :=
    p4Q2PF_originalWilsonThirdSchurContinuous H t ht
  have hPsi : psi ≠ 0 := by
    intro hZero
    have hLp : ((R : Phys) : Lp ℝ 2 haar) = 0 := by
      rw [p4Q2PF_originalThirdSchurContinuous_toLp H t ht]
      change L psi = 0
      rw [hZero]
      simp
    have hRZero : R = 0 := by
      apply Subtype.ext
      simpa using hLp
    exact hR hRZero
  by_contra hNo
  push Not at hNo
  apply hPsi
  ext A
  exact hNo A

/-- The actual **third Wilson Hankel D3>0**, not yet proved, is
precisely equivalent to finding ONE concrete spatial configuration
where the genuine normalized two-slab Schur function differs
from the two-dimensional Wilson span; D2>0 is the proven PC gate. -/
theorem p4Q2PF_originalThirdMoment_pos_iff_exists_trueSpatialPoint
    (hTwo : 0 < D2) :
    0 < D3 ↔
      ∃ A : Cfg,
        p4Q2PF_originalWilsonThirdSchurContinuous H t ht A ≠ 0 := by
  have hCriterion :=
    p4Q2PD_originalWilsonThirdMomentGap_pos_iff_physicalSchur_nonzero
      H t ht hTwo
  constructor
  · intro hD3
    exact p4Q2PF_originalThirdSchur_physicalNonzero_implies_exists_point
      H t ht (hCriterion.mp hD3)
  · rintro ⟨A, hA⟩
    exact hCriterion.mpr
      (p4Q2PF_originalThirdSchur_point_ne_zero_implies_physicalNonzero
        H t ht A hA)

/-- A TRUE original spatial configuration witness also forces an
actual original frozen-b>0 interacting two-posterior signed GI receiver
of the exact same physical Schur source, at any chosen spatial link. -/
theorem p4Q2PF_originalThirdSpatialPoint_implies_trueSignedGI
    (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) (left₀ : Cfg)
    (A : Cfg)
    (hPoint : p4Q2PF_originalWilsonThirdSchurContinuous H t ht A ≠ 0) :
    ∃ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le R e z ≠ 0 := by
  let psi := p4Q2PF_originalWilsonThirdSchurContinuous H t ht
  have hR : R ≠ 0 :=
    p4Q2PF_originalThirdSchur_point_ne_zero_implies_physicalNonzero
      H t ht A hPoint
  have hRep :
      (fun B : Cfg => ((R : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar] psi := by
    rw [p4Q2PF_originalThirdSchurContinuous_toLp H t ht]
    exact psi.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hRegular : p4Q2OT_hasGaugeContinuousRepresentative H R :=
    ⟨psi, hRep, fun gamma B =>
      p4Q2PF_originalThirdSchurContinuous_gaugeInvariant
        H t ht gamma B⟩
  exact p4Q2OT_originalContinuousPhysical_nonzero_genuineGI
    H b hb R hR hRegular e left₀

end ActualWilsonOneTwoSlabContinuousProfiles

section ActualSmallFineSpatialCriterion
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn

/-- The same original ON/PC small-positive fine interval (chosen before
the actual fine coupling) makes the outstanding physical D3>0
equivalent to a pointwise nonzero ORIGINAL Wilson two-slab function.
No point witness or rank-three conclusion is postulated. -/
theorem p4Q2PF_actualSmallFine_thirdMoment_pos_iff_originalSpatialPoint
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (0 < p4Q2PD_originalWilsonThirdMomentGap
            Hn (beta (n + 1)) (hbeta (n + 1)) ↔
          ∃ A : Cfg,
            p4Q2PF_originalWilsonThirdSchurContinuous
              Hn (beta (n + 1)) (hbeta (n + 1)) A ≠ 0)) := by
  obtain ⟨delta, hdelta, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  exact p4Q2PF_originalThirdMoment_pos_iff_exists_trueSpatialPoint
    Hn (beta (n + 1)) (hbeta (n + 1)) (hTwo ht hsmall)

end ActualSmallFineSpatialCriterion

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_originalOneSlabContinuous_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_originalTwoSlabContinuous_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_originalThirdSchurContinuous_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_originalThirdSchurContinuous_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_originalThirdSchur_point_ne_zero_implies_physicalNonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_originalThirdSchur_physicalNonzero_implies_exists_point
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_originalThirdMoment_pos_iff_exists_trueSpatialPoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_originalThirdSpatialPoint_implies_trueSignedGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PF_actualSmallFine_thirdMoment_pos_iff_originalSpatialPoint

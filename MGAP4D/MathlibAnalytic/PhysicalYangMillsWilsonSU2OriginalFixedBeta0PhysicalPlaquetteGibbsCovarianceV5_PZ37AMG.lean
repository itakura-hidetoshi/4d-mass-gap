import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0SharedLinkDobrushinInfluenceV5_PZ37AMF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteSupportGibbsCovarianceSpatialGeometric
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPlaquetteLocalTemporalStep
import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedSharedPlaquetteOscillation
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMG — true original beta0 SU2 Wilson Gibbs plaquette covariance decay

AMF establishes that the unchanged original beta0 = log(3/2)/64 lies below the
strict physical compact SU(2) Dobrushin threshold. The CURRENT canonical compact
Wilson random-scan Gibbs covariance theorem ALREADY establishes an explicit
geometric bound for two separated finite link supports, assuming the same
strict coefficient. AMG does not claim to have invented that existing theorem.

AMG connects its exact active-TV majorant to AMF's fixed-beta0 coefficient,
specializes the genuine finite-volume Gibbs bound to original beta0, and
realizes the actual SU(2) four-edge Wilson fundamental-character observable
as a bounded continuous function with a theorem-certified physical edge support.

For H>0, all true periodic SU(2) finite Wilson Gibbs two-plaquette connected
correlations obey a geometric bound whenever their ACTUAL physical link
supports satisfy the existing typed plaquette-local separation predicate.
No independence of plaquettes is assumed. For adjacent plaquettes the supports
overlap, so a positive separation hypothesis CANNOT be inserted silently.

This finite-volume H-independent decay *rate* is NOT a volume-uniform physical
OS transfer norm gap, a continuum factorial scaling result, or a Yang--Mills
mass gap. A Gauss-law-compatible cross-volume physical transfer bridge remains
open. H=0 remains outside the existing n>=3 uniqueness hypothesis.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "beta0" => GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling
local notation "chi" => GroundStatePosteriorJoint.p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AMG_nonzero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance p4Q2PZ37AMG_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMG_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMG_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMG_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMG_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AMG_nontrivial : Nontrivial G := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : G => (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace GroundStatePosteriorJoint

/-- The compact active-TV majorant used by the already-proven full Gibbs
covariance theorem is the SAME exact finite original Wilson influence
coefficient used by AMF, not an independently postulated parameter. -/
theorem p4Q2PZ37AMG_originalFixedBeta0ActiveTVMajorant_eq_eta :
    periodicHypercubicSpecialUnitaryActiveTVMajorant beta0 =
      periodicHypercubicSpecialUnitaryDobrushinEta beta0 := by
  rfl

/-- The exact fixed physical beta0 satisfies the actual compact SU2
random-scan Gibbs covariance high-temperature threshold, without a new
small-beta hypothesis. -/
theorem p4Q2PZ37AMG_originalFixedBeta0ActiveTVMajorant_strict :
    18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0 < 1 := by
  rw [p4Q2PZ37AMG_originalFixedBeta0ActiveTVMajorant_eq_eta]
  exact p4Q2PZ37AMF_originalFixedBeta0_DobrushinCoefficient_lt_one

/-- Genuine original physical Wilson SU2 system, unchanged from AME/AMF. -/
noncomputable def p4Q2PZ37AMG_originalFixedBeta0System (H : ℕ) :
    ContinuousCompactOrientedGaugeWilsonSystem :=
  periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
    beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

/-- The character chi=1-E of one ACTUAL four-edge SU2 plaquette on the
unchanged full Wilson link configuration is bounded continuous. -/
noncomputable def p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    BoundedContinuousFunction (PeriodicHypercubicEvenEdge H → G) ℝ := by
  let C := p4Q2PZ37AMG_originalFixedBeta0System H
  have hHol :
      Continuous (fun A : PeriodicHypercubicEvenEdge H → G =>
        periodicHypercubicPlaquetteHolonomy A p) := by
    simpa [C, p4Q2PZ37AMG_originalFixedBeta0System] using
      (continuous_compact_oriented_plaquetteHolonomy C p)
  exact BoundedContinuousFunction.mkOfCompact
    ⟨(fun A : PeriodicHypercubicEvenEdge H → G =>
        chi (periodicHypercubicPlaquetteHolonomy A p)),
      p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.comp hHol⟩

@[simp] theorem p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_apply
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (A : PeriodicHypercubicEvenEdge H → G) :
    p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p A =
      chi (periodicHypercubicPlaquetteHolonomy A p) := by
  rfl

/-- The actual four-edge SU2 plaquette character depends ONLY on the
theorem-generated positive physical boundary links of that plaquette.
No probabilistic product law is assumed, even for overlapping supports. -/
theorem p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_eq_of_eqOn_edges
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (A B : PeriodicHypercubicEvenEdge H → G)
    (hAB : ∀ e, e ∈ periodicHypercubicEvenPlaquetteEdgeSupport H p →
      A e = B e) :
    p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p A =
      p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p B := by
  simp only [p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_apply]
  congr 1
  let C := p4Q2PZ37AMG_originalFixedBeta0System H
  change C.base.plaquetteHolonomy A p = C.base.plaquetteHolonomy B p
  apply compact_oriented_plaquetteHolonomy_congr C.base A B p
  intro k
  change A ((periodicHypercubicBoundaryStep
    (PeriodicHypercubicEvenSideLength H) p k).edge) =
    B ((periodicHypercubicBoundaryStep
    (PeriodicHypercubicEvenSideLength H) p k).edge)
  apply hAB
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩

/-- Genuine full finite-volume SU2 Wilson Gibbs covariance bound at the
ORIGINAL fixed beta0. Both finite-support variation fields have been
constructed by the canonical finite-support profile theorem; the strict
geometric coefficient is generated by AMF rather than assumed. -/
theorem p4Q2PZ37AMG_originalFixedBeta0GibbsCovariance_geometric_finiteSupport
    (H D : ℕ) (hH : 0 < H)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (F O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → G) ℝ)
    (hFDepends : ∀ A B, (∀ e, e ∈ T → A e = B e) → F A = F B)
    (hODepends : ∀ A B, (∀ e, e ∈ S → A e = B e) → O A = O B) :
    |(p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
       (fun A => F A) (fun A => O A)| ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)) *
        (∑ e ∈ T, 2 * ‖F‖) * ∑ i ∈ S, 2 * ‖O‖ := by
  simpa only [p4Q2PZ37AMG_originalFixedBeta0System] using
    (periodicHypercubicEvenSpecialUnitary_gibbsCovarianceReal_abs_le_geometric_of_finiteSupportsSeparatedBy
      H 2 D hH (by norm_num)
      beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
      p4Q2PZ37AMG_originalFixedBeta0ActiveTVMajorant_strict
      S T hsep F O hFDepends hODepends)

/-- Geometric decay of the TRUE interacting Wilson Gibbs connected
fundamental-character correlation of two ACTUAL physical SU2 plaquettes.
The required separation is a typed hypothesis about their REAL physical
four-link supports; for adjacent plaquettes D=0 is allowed but no positive
distance is inferred. The rate is H-independent at the original beta0. -/
theorem p4Q2PZ37AMG_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_geometric
    (H D : ℕ) (hH : 0 < H)
    (p q : PeriodicHypercubicEvenPlaquette H)
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D
      (periodicHypercubicEvenPlaquetteEdgeSupport H q)
      (periodicHypercubicEvenPlaquetteEdgeSupport H p)) :
    let F := p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p
    let O := p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q
    |(p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
      (fun A => F A) (fun A => O A)| ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)) *
        (∑ e ∈ periodicHypercubicEvenPlaquetteEdgeSupport H p,
          2 * ‖F‖) *
        ∑ e ∈ periodicHypercubicEvenPlaquetteEdgeSupport H q,
          2 * ‖O‖ := by
  dsimp only
  exact p4Q2PZ37AMG_originalFixedBeta0GibbsCovariance_geometric_finiteSupport
    H D hH
    (periodicHypercubicEvenPlaquetteEdgeSupport H q)
    (periodicHypercubicEvenPlaquetteEdgeSupport H p)
    hsep
    (p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p)
    (p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q)
    (fun A B hAB =>
      p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_eq_of_eqOn_edges H p A B hAB)
    (fun A B hAB =>
      p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_eq_of_eqOn_edges H q A B hAB)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMG_originalFixedBeta0ActiveTVMajorant_eq_eta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMG_originalFixedBeta0ActiveTVMajorant_strict
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMG_originalFixedBeta0System
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_eq_of_eqOn_edges
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMG_originalFixedBeta0GibbsCovariance_geometric_finiteSupport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMG_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_geometric

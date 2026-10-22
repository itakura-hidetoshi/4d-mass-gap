import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPhysicalGaugeContinuousRangeV5_OV
import Mathlib.Tactic

/-!
# P4-Q2-OW — actual original Wilson all-finite-depth physical/GI kernel equality

The genuine original SU(2) normalized fine Wilson physical one-slab
operator smooths EVERY Gauss-law Haar-L² source into a continuous
gauge-invariant physical source (OU/OV). The genuine constant unit
already has the continuous constant-one representative.

The actual fine RIGHT Krylov orbit used by the original HF/HJ receiver
is LITERALLY U, T_t U, T_t² U, ... with the unchanged normalized
physical transfer and separate fine/frozen Wilson couplings. Every
orbit member therefore has a genuine continuous Haar-L² spatial
representative, and so does EVERY finite real Krylov synthesis
S_r(a)=Σ_j a_j T_t^j U. Its unique continuous representative is
invariant under the actual spatial SU(2) gauge transformations (OV).

OT proves for each positive frozen coupling b that EVERY nonzero
physical source with such a representative is detected by an ACTUAL
unchanged two-interacting-Wilson-posterior GI signed receiver at some
original link/context.

Thus, without assuming a positive-fine third-mode rank, Schur
source nonzero, or quadratic orbit collapse, at every finite H,
every fixed frozen b>0, every nonnegative fine t and every finite r:

   ker S_r = ker Phi_all,r.

This proves GI faithfulness on every genuine FINITE Krylov source
without claiming source synthesis S_r is injective. In particular,
when the actual depth-two OO Schur physical source is NONZERO, a true
third GI receiver detects that SAME source, without a separate
analytic regularity hypothesis. Physical Schur nonzero itself stays
OPEN, as do U0, same-endpoint transport, H1-C3, and the continuum
4D Yang--Mills mass gap.

No Dobrushin, independent Haar posterior, surrogate detector,
new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section ActualOriginalWilsonKrylov
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "Right" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- The true normalized Wilson right-Krylov mode of ANY natural
depth j has an ACTUAL continuous spatial Haar-L² representative.
At j=0 this is literally the physical constant unit; at j+1
it is the original normalized fine Wilson operator's continuous
Moore--Aronszajn feature synthesis from OU. -/
theorem p4Q2OW_actualRightMode_hasContinuousRepresentative
    (j : ℕ) :
    ∃ psi : C(Cfg, ℝ),
      ((Right n j : Phys) : Lp ℝ 2 haar) = L psi := by
  cases j with
  | zero =>
      refine ⟨(1 : C(Cfg, ℝ)), ?_⟩
      change ((Right n 0 : Phys) : Lp ℝ 2 haar) =
        L (1 : C(Cfg, ℝ))
      rw [fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n]
      exact p4Q2JU_originalPhysicalUnit_coe_eq_toLp Hn
  | succ j =>
      let f : Phys := (Fine ^ j) U
      let psi : C(Cfg, ℝ) :=
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          Hn 2 specialUnitaryTwoWilsonRankPositive
          (beta (n + 1)) (hbeta (n + 1))‖⁻¹ •
          p4Q2OU_originalPhysicalTransferContinuous
            Hn (beta (n + 1)) (hbeta (n + 1)) f
      refine ⟨psi, ?_⟩
      have hRight : Right n (j + 1) = Fine f := by
        change (Fine ^ (j + 1)) U = Fine ((Fine ^ j) U)
        rw [pow_succ']
        rfl
      rw [hRight]
      exact p4Q2OU_originalNormalizedPhysicalTransferContinuous_toLp
        Hn (beta (n + 1)) (hbeta (n + 1)) f

/-- Every signed finite Krylov source S_r(a) in the true Gauss-law
physical Hilbert space possesses a genuine continuous Haar-L²
representative. This uses the ACTUAL HJ synthesis and linearly
combines the individually continuous genuine Wilson modes. -/
theorem p4Q2OW_actualAllDepth_source_hasContinuousRepresentative
    (r : ℕ) (a : Fin (r + 1) → ℝ) :
    ∃ psi : C(Cfg, ℝ),
      ((S r a : Phys) : Lp ℝ 2 haar) = L psi := by
  classical
  have hMode (j : Fin (r + 1)) :
      ∃ psi : C(Cfg, ℝ),
        ((Right n (j : ℕ) : Phys) : Lp ℝ 2 haar) = L psi :=
    p4Q2OW_actualRightMode_hasContinuousRepresentative
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  choose psi hpsi using hMode
  refine ⟨∑ j : Fin (r + 1), a j • psi j, ?_⟩
  let incl : Phys →ₗ[ℝ] Lp ℝ 2 haar :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      Hn 2).subtype
  calc
    ((S r a : Phys) : Lp ℝ 2 haar) =
        incl (∑ j : Fin (r + 1), a j • Right n (j : ℕ)) := by rfl
    _ = ∑ j : Fin (r + 1),
          a j • ((Right n (j : ℕ) : Phys) : Lp ℝ 2 haar) := by
            rw [map_sum]
            simp only [map_smul]
    _ = ∑ j : Fin (r + 1), a j • L (psi j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hpsi j]
    _ = L (∑ j : Fin (r + 1), a j • psi j) := by
          rw [map_sum]
          simp only [map_smul]

/-- The same authentic all-depth physical Krylov source has an
original SU(2) gauge-invariant continuous representative. OV proves
pointwise invariance automatically from membership in the genuine
Gauss-law fixed Hilbert submodule and full-support spatial Haar. -/
theorem p4Q2OW_actualAllDepth_source_hasGaugeContinuousRepresentative
    (r : ℕ) (a : Fin (r + 1) → ℝ) :
    p4Q2OT_hasGaugeContinuousRepresentative Hn (S r a) := by
  obtain ⟨psi, hLp⟩ :=
    p4Q2OW_actualAllDepth_source_hasContinuousRepresentative
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hRep :
      (fun B : Cfg => ((S r a : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar] psi := by
    rw [hLp]
    exact psi.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  refine ⟨psi, hRep, ?_⟩
  intro gamma B
  exact p4Q2OV_originalPhysicalContinuousRepresentative_gaugeInvariant
    Hn (S r a) psi hRep gamma B

/-- UNCONDITIONAL physical-source/whole-original-GI kernel equality
at ALL finite right-Krylov depths, EVERY finite spatial volume and
EVERY nonnegative fine coupling, at any positive frozen b.
No actual Schur residual nonzero, third mode rank, quadratic closure,
or artificial all-source separation is assumed.

Proof: an invisible coefficient has zero original detector at EVERY
real Wilson context. If its actual physical synthesis were nonzero,
its proved continuous gauge-invariant representative would be detected
at an actual true original two-interacting-posterior context by OT,
contradicting this exact detector zero. The reverse inclusion is HJ. -/
theorem p4Q2OW_actualPositiveFrozen_allFine_allDepth_sourceKernel_eq_fullGIKernel
    (hFrozen : 0 < beta n)
    (e : Link) (left₀ : Cfg)
    (r : ℕ) :
    (S r).ker = (Full r).ker := by
  apply le_antisymm
  · exact p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  · intro a hFull
    have hAllZero : Full r a = 0 := (LinearMap.mem_ker).mp hFull
    by_contra hNot
    have hSource : S r a ≠ 0 := by
      intro hS
      exact hNot ((LinearMap.mem_ker).mpr hS)
    obtain ⟨z, hGI⟩ :=
      p4Q2OT_originalContinuousPhysical_nonzero_genuineGI
        Hn (beta n) hFrozen (S r a) hSource
        (p4Q2OW_actualAllDepth_source_hasGaugeContinuousRepresentative
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a)
        e left₀
    have hAt := congrArg (fun g : Link → C(Pair, ℝ) => g e z) hAllZero
    have hModalZero : M r e z a = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hAt
    have hOriginal :=
      p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e z
    change p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) (S r a) e z =
        M r e z a at hOriginal
    exact hGI (hOriginal.trans hModalZero)

/-- On the ACTUAL true depth-two Schur physical source, a nonzero
Hilbert vector automatically admits some nonzero THIRD original Wilson
GI context without a further regularity hypothesis. The latter has
been discharged uniformly for EVERY finite physical Krylov synthesis.
The physical Schur nonzero hypothesis itself remains genuinely OPEN. -/
theorem p4Q2OW_actualSchurPhysical_nonzero_implies_trueThirdGI
    (hFrozen : 0 < beta n)
    (e e' : Link) (z z' : Pair)
    (hSchur :
      S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0) :
    ∃ e'' : Link, ∃ z'' : Pair,
      M 2 e'' z''
        (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0 := by
  let residual : Fin (2 + 1) → ℝ :=
    p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')
  obtain ⟨z'', hGI⟩ :=
    p4Q2OT_originalContinuousPhysical_nonzero_genuineGI
      Hn (beta n) hFrozen (S 2 residual) hSchur
      (p4Q2OW_actualAllDepth_source_hasGaugeContinuousRepresentative
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2 residual) e z.1
  refine ⟨e, z'', ?_⟩
  rw [p4Q2OO_actualDepthTwo_SchurResidual_trueThirdGI_response
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e e' e z z' z'']
  exact hGI

end ActualOriginalWilsonKrylov
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OW_actualRightMode_hasContinuousRepresentative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OW_actualAllDepth_source_hasContinuousRepresentative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OW_actualAllDepth_source_hasGaugeContinuousRepresentative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OW_actualPositiveFrozen_allFine_allDepth_sourceKernel_eq_fullGIKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OW_actualSchurPhysical_nonzero_implies_trueThirdGI

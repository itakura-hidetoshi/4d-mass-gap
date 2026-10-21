import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedPowerDoubleEnergyV5_NW
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Tactic

/-!
# P4-Q2-NX — a bounded double action of the GENUINE Wilson–Perron signed functional

NW established the EXACT genuine double signed Haar-minus-Dirac energy
at each finite Wilson-character power, with the nonnegative Fock
coordinate-moment representation. To transport exponential convergence,
we now construct the needed continuous real-linear operator on the
FULL pair space C(SU(2) × SU(2), R), with no surrogate measure:

  T_L(F) = L_x( x ↦ L_g(F(x,g)) ).

Here L is the ORIGINAL bounded NJ Wilson–Perron signed functional
(or any bounded real-linear functional, without a new physical axiom).
Compactness and the mathlib compact-open curry map guarantee that
x ↦ L(F.curry x) really belongs to C(SU(2),R).
Pointwise estimates give the true uniform norm bound

  ‖x ↦ L_g F(x,g)‖ <= ‖L‖ ‖F‖,

thereby constructing a bounded real-linear operator. The resulting
L ∘ section map can be passed rigorously through *Banach* exponential
HasSum by mathlib HasSum.map.

No infinite series is interchanged with a pointwise formal integral.
The remaining step after this bounded bridge is to identify the
two-variable exponential Taylor terms with NW's genuine nonnegative
finite powers, and derive strict full-kernel energy. The original two
interacting Wilson posteriors, Gauss-law source, right-spatial factors,
and Perron half-density remain unchanged. No Dobrushin, artificial
rank assumption, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter

/-- Continuous partial application of an arbitrary SU(2) pair
observable through the *same* real signed functional L. -/
noncomputable def p4Q2NX_originalSignedPairSection
    (L : C(Gauge, ℝ) →L[ℝ] ℝ)
    (F : C(Gauge × Gauge, ℝ)) : C(Gauge, ℝ) :=
  (⟨L, L.continuous⟩ : C(C(Gauge, ℝ), ℝ)).comp F.curry

theorem p4Q2NX_originalSignedPairSection_apply
    (L : C(Gauge, ℝ) →L[ℝ] ℝ)
    (F : C(Gauge × Gauge, ℝ)) (x : Gauge) :
    p4Q2NX_originalSignedPairSection L F x = L (F.curry x) :=
  rfl

/-- Pairwise continuous functions add rowwise under compact-open
currying. -/
private theorem p4Q2NX_curry_add
    (F G : C(Gauge × Gauge, ℝ)) (x : Gauge) :
    (F + G).curry x = F.curry x + G.curry x := by
  ext g
  rfl

/-- Scalar multiplication also preserves original SU(2) sections. -/
private theorem p4Q2NX_curry_smul
    (a : ℝ) (F : C(Gauge × Gauge, ℝ)) (x : Gauge) :
    (a • F).curry x = a • F.curry x := by
  ext g
  rfl

/-- The signed inner-variable action is genuinely REAL LINEAR on
two-variable continuous functions; both additivity and homogeneity
are proved from the unchanged original L. -/
noncomputable def p4Q2NX_originalSignedPairSectionLinear
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) :
    C(Gauge × Gauge, ℝ) →ₗ[ℝ] C(Gauge, ℝ) where
  toFun := p4Q2NX_originalSignedPairSection L
  map_add' F G := by
    ext x
    change L ((F + G).curry x) = L (F.curry x) + L (G.curry x)
    rw [p4Q2NX_curry_add]
    exact map_add L _ _
  map_smul' a F := by
    ext x
    change L ((a • F).curry x) = a • L (F.curry x)
    rw [p4Q2NX_curry_smul]
    exact map_smul L a (F.curry x)

/-- Each genuine SU(2) continuous row has uniform norm no greater
than the source pair observable norm. -/
theorem p4Q2NX_originalPairRow_norm_le
    (F : C(Gauge × Gauge, ℝ)) (x : Gauge) :
    ‖F.curry x‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le_of_nonempty (F.curry x)).2
  intro g
  simpa only [ContinuousMap.curry_apply] using F.norm_coe_le_norm (x, g)

/-- The continuous signed section L_g F(x,g) is uniformly bounded
by the ORIGINAL L operator norm. No new physical posterior is assumed. -/
theorem p4Q2NX_originalSignedPairSection_norm_le
    (L : C(Gauge, ℝ) →L[ℝ] ℝ)
    (F : C(Gauge × Gauge, ℝ)) :
    ‖p4Q2NX_originalSignedPairSection L F‖ ≤ ‖L‖ * ‖F‖ := by
  apply (ContinuousMap.norm_le_of_nonempty
    (p4Q2NX_originalSignedPairSection L F)).2
  intro x
  change ‖L (F.curry x)‖ ≤ ‖L‖ * ‖F‖
  exact (L.le_opNorm (F.curry x)).trans
    (mul_le_mul_of_nonneg_left
      (p4Q2NX_originalPairRow_norm_le F x) (norm_nonneg L))

/-- Canonical bounded REAL-linear transport of the genuine signed
functional through one SU(2) coordinate of a pair continuous map. -/
noncomputable def p4Q2NX_originalSignedPairSectionCLM
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) :
    C(Gauge × Gauge, ℝ) →L[ℝ] C(Gauge, ℝ) :=
  (p4Q2NX_originalSignedPairSectionLinear L).mkContinuous ‖L‖
    (p4Q2NX_originalSignedPairSection_norm_le L)

/-- Two ORIGINAL bounded signed actions, now certified as ONE
continuous linear functional on C(SU2 × SU2, R). -/
noncomputable def p4Q2NX_originalSignedDoubleCLM
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) :
    C(Gauge × Gauge, ℝ) →L[ℝ] ℝ :=
  L.comp (p4Q2NX_originalSignedPairSectionCLM L)

theorem p4Q2NX_originalSignedDoubleCLM_apply
    (L : C(Gauge, ℝ) →L[ℝ] ℝ)
    (F : C(Gauge × Gauge, ℝ)) :
    p4Q2NX_originalSignedDoubleCLM L F =
      L (p4Q2NX_originalSignedPairSection L F) := by
  rfl

/-- Full actual SU(2) relative temporal character, now a continuous
function of BOTH genuine SU2 holonomies simultaneously. -/
noncomputable def p4Q2NX_originalTemporalPairCharacter :
    C(Gauge × Gauge, ℝ) := by
  have hShift : Continuous (fun p : Gauge × Gauge => p.1⁻¹ * p.2) :=
    continuous_fst.inv.mul continuous_snd
  have hChi :
      Continuous (fun p : Gauge × Gauge => chi p.1 p.2) := by
    unfold p4Q2NG_originalSU2TemporalCharacter
    exact continuous_const.sub
      ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp hShift)
  exact ⟨fun p => chi p.1 p.2, hChi⟩

/-- A complete genuine Wilson kernel Taylor series exists in the
BANACH space of continuous real functions on SU(2) × SU(2). -/
theorem p4Q2NX_originalPairWilsonBanachExp_hasSum (b : ℝ) :
    HasSum
      (fun n : ℕ => ((n.factorial : ℝ)⁻¹) •
        (b • p4Q2NX_originalTemporalPairCharacter)^n)
      (NormedSpace.exp (b • p4Q2NX_originalTemporalPairCharacter)) :=
  NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    (b • p4Q2NX_originalTemporalPairCharacter)

/-- The genuine double signed Wilson–Perron bounded functional
maps the full SUP-NORM convergent pair exponential series to an
actual convergent real series, with no unproved interchange. -/
theorem p4Q2NX_originalSignedDouble_BanachExp_hasSum
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (b : ℝ) :
    HasSum
      (fun n : ℕ =>
        p4Q2NX_originalSignedDoubleCLM L
          (((n.factorial : ℝ)⁻¹) •
            (b • p4Q2NX_originalTemporalPairCharacter)^n))
      (p4Q2NX_originalSignedDoubleCLM L
        (NormedSpace.exp (b • p4Q2NX_originalTemporalPairCharacter))) :=
  (p4Q2NX_originalPairWilsonBanachExp_hasSum b).map
    (p4Q2NX_originalSignedDoubleCLM L)
    (p4Q2NX_originalSignedDoubleCLM L).continuous

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NX_originalSignedPairSection_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NX_originalPairRow_norm_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NX_originalSignedPairSection_norm_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NX_originalSignedDoubleCLM_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NX_originalPairWilsonBanachExp_hasSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NX_originalSignedDouble_BanachExp_hasSum

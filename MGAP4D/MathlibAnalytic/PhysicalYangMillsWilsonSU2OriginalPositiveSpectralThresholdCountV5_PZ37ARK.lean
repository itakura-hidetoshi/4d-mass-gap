import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSpectralSplitBudgetV5_PZ37ARJ
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ARK — finite positive spectral threshold sets

From the actual complete squared-eigenvalue sum, construct the full finite
family above each positive threshold, preserving multiplicities. Relate its
count to every complete moment and use the actual threshold family in ARJ's
terminal estimate. No volume-uniform count or tail estimate is assumed proved.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace InnerProduct BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000
universe i

private theorem p4Q2PZ37ARK_finite_aux {ι : Type i} (rho : ι → ℝ)
    (r : ℝ) (hr : 0 < r) (hs : Summable (fun k => (rho k)^2)) :
    {k : ι | r ≤ rho k}.Finite := by
  let S : Set ι := {k | r ≤ rho k}
  have hsum : Summable (fun k : S => (rho k.val)^2) :=
    hs.comp_injective Subtype.val_injective
  have hconst : Summable (fun _ : S => r^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg r)
      (fun k => pow_le_pow_left₀ hr.le k.property 2) hsum
  have hf : Finite S := Finite.of_summable_const (pow_pos hr 2) hconst
  exact Set.finite_coe_iff.mp hf

private theorem p4Q2PZ37ARK_two_pos : 0 < (2 : ℕ) := by decide

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phys" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "Pair" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
local notation "Dec" => periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
local notation "K" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
local notation "OO" => periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure
local notation "EH" => periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
local notation "Step" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
local notation "PF" => p4Q2PZ37AQW_partitionFactor
local notation "Res" => p4Q2PZ37AQX_relativeResidual
local notation "Emb" => periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry

local instance p4Q2PZ37ARK_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ARK_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ARK_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ARK_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ARK_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ARK_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37ARK_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37ARK_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ARK_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ARK_nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local notation "h2" => p4Q2PZ37ARK_two_pos
local notation "M" => p4Q2PZ37ARD_pairMoment

local notation "Cut" => GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
local notation "c" => ((3071 : ℝ)/3072)

/-- Every strictly positive threshold cuts out a finite complete spectral
family. This is a theorem at each actual volume, not a uniform bound. -/
theorem p4Q2PZ37ARK_threshold_finite
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ) (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (r : ℝ) (hr : 0 < r) :
    {k : ι | r ≤ rho k}.Finite := by
  have hm := p4Q2PZ37ARD_moment_hasSum H beta hb 0 b rho he
  have hs : Summable (fun k => (rho k)^2) := by
    simpa using hm.summable
  exact p4Q2PZ37ARK_finite_aux rho r hr hs

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARK_threshold_finite

/-- The complete threshold family, not an arbitrarily selected subset. -/
def p4Q2PZ37ARK_thresholdFinset
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ) (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (r : ℝ) (hr : 0 < r) : Finset ι :=
  (p4Q2PZ37ARK_threshold_finite H beta hb b rho he r hr).toFinset

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARK_thresholdFinset

local notation "Q" => p4Q2PZ37ARK_thresholdFinset

theorem p4Q2PZ37ARK_mem_thresholdFinset
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ) (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (r : ℝ) (hr : 0 < r) (k : ι) :
    k ∈ Q H beta hb b rho he r hr ↔ r ≤ rho k := by
  exact Set.Finite.mem_toFinset (hs := p4Q2PZ37ARK_threshold_finite H beta hb b rho he r hr)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARK_mem_thresholdFinset

/-- Increasing a positive threshold can only remove spectral modes. -/
theorem p4Q2PZ37ARK_thresholdCard_antitone
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ) (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (r t : ℝ) (hr : 0 < r) (ht : 0 < t) (hrt : r ≤ t) :
    (Q H beta hb b rho he t ht).card ≤ (Q H beta hb b rho he r hr).card := by
  apply Finset.card_le_card
  intro k hk
  exact (p4Q2PZ37ARK_mem_thresholdFinset H beta hb b rho he r hr k).2
    (hrt.trans ((p4Q2PZ37ARK_mem_thresholdFinset H beta hb b rho he t ht k).1 hk))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARK_thresholdCard_antitone

/-- Every complete moment bounds the actual full threshold count. -/
theorem p4Q2PZ37ARK_thresholdCard_le_moment
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (n : ℕ)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ) (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (r : ℝ) (hr : 0 < r) :
    ((Q H beta hb b rho he r hr).card : ℝ) ≤ M H beta hb n / r^(2*(n+1)) := by
  apply (le_div_iff₀ (pow_pos hr _)).2
  exact p4Q2PZ37ARJ_thresholdCount_at_degree H beta hb n b rho he
    (Q H beta hb b rho he r hr) r hr.le
    (fun k hk => (p4Q2PZ37ARK_mem_thresholdFinset H beta hb b rho he r hr k).1 hk)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARK_thresholdCard_le_moment

/-- ARJ's terminal split now needs only a positive threshold, not a
hypothesized exceptional family or a separate tail-cap assumption. -/
theorem p4Q2PZ37ARK_terminal_le_thresholdSplit
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ Cut s hs)
    (n : ℕ) (hn : n ≤ H)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ) (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (r : ℝ) (hr : 0 < r) :
    (PF H beta hb)⁻¹ ^ 2 - 1 ≤
      ((Q H beta hb b rho he r hr).card : ℝ)*c^(2*(H+1)) +
      r^(2*(H-n))*M H beta hb n := by
  apply p4Q2PZ37ARJ_terminal_le_spectralSplit H beta hb s hs hcut n hn b rho he
    (Q H beta hb b rho he r hr) r hr.le
  intro k hk
  apply le_of_lt
  exact lt_of_not_ge (fun h => hk
    ((p4Q2PZ37ARK_mem_thresholdFinset H beta hb b rho he r hr k).2 h))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARK_terminal_le_thresholdSplit

end
end MGAP4D.MathlibAnalytic

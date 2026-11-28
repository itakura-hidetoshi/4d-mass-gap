import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalParitySurvivorRankV5_PZ37ASB
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ASC — local parity multiplicities and closed-pattern dimension

The actual ASB symmetric local-index fibers have exact binomial counts.
Use the literal mod-two incidence linear map, not an abstract replacement
graph, and rank-nullity for its kernel. Bound the weighted survivor count
by its exact number of closed patterns times the largest local weight.
The numeric rank of the lattice incidence matrix and a systematic
coordinate refinement of the weighted bound remain separate obligations.
No uniform spectral growth or continuum assertion is made.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000
universe i

private theorem p4Q2PZ37ASC_two_pos : 0 < (2 : ℕ) := by decide

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "K" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
local notation "Phys" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "Emb" => periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
local notation "Step" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
local notation "T" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
local notation "Raw" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
local notation "Kernel" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
local notation "L" => periodicHypercubicEvenSpatialSliceLinkList
local notation "NK" => p4Q2PZ37ARA_normalizedKernel
local notation "h2" => p4Q2PZ37ASC_two_pos

local instance p4Q2PZ37ASC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ASC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ASC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ASC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ASC_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ASC_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37ASC_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37ASC_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ASC_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ASC_nontrivial : Nontrivial G := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00


local notation "Gauge" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation
local notation "GT" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
local notation "Pull" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
local notation "Coord" => ((Fin 2 × Fin 2) × Bool)


local notation "J" => ((Fin 2 × Fin 2) × Bool)
local notation "Tr" => specialUnitaryNormalizedTraceRelativeKernel
local notation "kp" => specialUnitaryWilsonRelativeKernelPartial
local notation "Vtx" => PeriodicHypercubicEvenSpatialSliceVertex
local notation "Idx" => PZ37ARXLocalIndex
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "c0" => p4Q2PZ35D4_centralMinusOne


local notation "All" => fun H m : ℕ => Link H → Idx m
local notation "Pat" => fun H : ℕ => Link H → ZMod 2


local notation "Mlt" => p4Q2PZ37ASB_localMultiplicity
local notation "Closed" => p4Q2PZ37ASB_closedPatterns
local notation "Surv" => p4Q2PZ37ASB_survivors
local notation "Bd" => p4Q2PZ37ASB_boundary

/-- Exact local fiber count by degree, with full symmetric multiplicity. -/
theorem p4Q2PZ37ASC_localMultiplicity_formula (m : ℕ) (p : ZMod 2) :
    Mlt m p =
      ∑ k ∈ (Finset.univ : Finset (Fin (m+1))).filter (fun k => (k.val : ZMod 2) = p),
        (k.val+7).choose 7 := by
  classical
  have hs : (Finset.univ.filter (fun j : Idx m => (j.1.val : ZMod 2) = p)) =
      ((Finset.univ : Finset (Fin (m+1))).filter (fun k => (k.val : ZMod 2) = p)).sigma
        (fun k => (Finset.univ : Finset (Sym J k.val))) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sigma,and_true]
  rw [p4Q2PZ37ASB_localMultiplicity,hs,Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro k _
  have hJ : Fintype.card J = 8 := by decide
  rw [Finset.card_univ,Sym.card_sym_eq_multichoose,hJ,Nat.multichoose_eq]
  have h : 8+k.val-1 = k.val+7 := by omega
  rw [h]
  exact Nat.choose_symm_add

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_localMultiplicity_formula

theorem p4Q2PZ37ASC_evenMultiplicity (m : ℕ) :
    Mlt m 0 =
      ∑ k ∈ (Finset.univ : Finset (Fin (m+1))).filter (fun k => Even k.val),
        (k.val+7).choose 7 := by
  classical
  simp only [p4Q2PZ37ASC_localMultiplicity_formula,ZMod.natCast_eq_zero_iff_even]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_evenMultiplicity

theorem p4Q2PZ37ASC_oddMultiplicity (m : ℕ) :
    Mlt m 1 =
      ∑ k ∈ (Finset.univ : Finset (Fin (m+1))).filter (fun k => Odd k.val),
        (k.val+7).choose 7 := by
  classical
  simp only [p4Q2PZ37ASC_localMultiplicity_formula,ZMod.natCast_eq_one_iff_odd]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_oddMultiplicity

private theorem p4Q2PZ37ASC_two_univ :
    (Finset.univ : Finset (ZMod 2)) = {0,1} := by decide

theorem p4Q2PZ37ASC_localMultiplicity_total (m : ℕ) :
    Mlt m 0 + Mlt m 1 = p4Q2PZ37ARX_localTerms m := by
  classical
  have h : (Finset.univ : Finset (Idx m)).card =
      ∑ p : ZMod 2, (Finset.univ.filter (fun j : Idx m => (j.1.val : ZMod 2) = p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ,p4Q2PZ37ARX_localIndex_card] at h
  change p4Q2PZ37ARX_localTerms m = ∑ p : ZMod 2, Mlt m p at h
  rw [p4Q2PZ37ASC_two_univ] at h
  have h01 : (0 : ZMod 2) ∉ ({1} : Finset (ZMod 2)) := by decide
  rw [Finset.sum_insert h01,Finset.sum_singleton] at h
  exact h.symm

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_localMultiplicity_total

def p4Q2PZ37ASC_cycleDim (H : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.ker (Bd H))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_cycleDim

def p4Q2PZ37ASC_boundaryRank (H : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (Bd H))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_boundaryRank

theorem p4Q2PZ37ASC_rank_nullity (H : ℕ) :
    p4Q2PZ37ASC_boundaryRank H + p4Q2PZ37ASC_cycleDim H = Nat.card (Link H) := by
  simpa only [p4Q2PZ37ASC_boundaryRank,p4Q2PZ37ASC_cycleDim,Module.finrank_fintype_fun_eq_card,Fintype.card_eq_nat_card] using
    (Bd H).finrank_range_add_finrank_ker

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_rank_nullity

theorem p4Q2PZ37ASC_closed_card (H : ℕ) :
    (Closed H).card = 2^(p4Q2PZ37ASC_cycleDim H) := by
  classical
  let S := LinearMap.ker (Bd H)
  letI : Fintype S := Fintype.ofFinite _
  let e : ↥(Closed H) ≃ S :=
    { toFun := fun p => ⟨p.val,LinearMap.mem_ker.mpr
        ((Finset.mem_filter.mp p.property).2)⟩
      invFun := fun p => ⟨p.val,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,LinearMap.mem_ker.mp p.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let b := Module.finBasis (ZMod 2) S
  have he : Fintype.card S =
      Fintype.card (Fin (Module.finrank (ZMod 2) S) → ZMod 2) :=
    Fintype.card_congr b.equivFun.toEquiv
  calc
    _ = Fintype.card (Closed H : Type) := (Fintype.card_coe _).symm
    _ = Fintype.card S := Fintype.card_congr e
    _ = _ := by
      simp only [he,Fintype.card_fun,Fintype.card_fin,ZMod.card,p4Q2PZ37ASC_cycleDim,S]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_closed_card

theorem p4Q2PZ37ASC_closed_card_rank (H : ℕ) :
    (Closed H).card = 2^(Nat.card (Link H)-p4Q2PZ37ASC_boundaryRank H) := by
  rw [p4Q2PZ37ASC_closed_card]
  have h := p4Q2PZ37ASC_rank_nullity H
  have he : p4Q2PZ37ASC_cycleDim H = Nat.card (Link H)-p4Q2PZ37ASC_boundaryRank H := by omega
  rw [he]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_closed_card_rank

def p4Q2PZ37ASC_maxMultiplicity (m : ℕ) : ℕ :=
  max (Mlt m 0) (Mlt m 1)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_maxMultiplicity

theorem p4Q2PZ37ASC_multiplicity_le_max (m : ℕ) (p : ZMod 2) :
    Mlt m p ≤ p4Q2PZ37ASC_maxMultiplicity m := by
  have hp : p = 0 ∨ p = 1 := by
    have hm : p ∈ (Finset.univ : Finset (ZMod 2)) := Finset.mem_univ _
    rw [p4Q2PZ37ASC_two_univ] at hm
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  rcases hp with rfl | rfl
  · exact le_max_left _ _
  · exact le_max_right _ _

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_multiplicity_le_max

theorem p4Q2PZ37ASC_survivors_le_cycleWeight (H m : ℕ) :
    (Surv H m).card ≤ 2^(p4Q2PZ37ASC_cycleDim H) *
      (p4Q2PZ37ASC_maxMultiplicity m)^(Nat.card (Link H)) := by
  classical
  rw [p4Q2PZ37ASB_survivor_card]
  calc
    _ ≤ ∑ p ∈ Closed H, (p4Q2PZ37ASC_maxMultiplicity m)^(Nat.card (Link H)) := by
      apply Finset.sum_le_sum
      intro p _
      calc
        _ ≤ ∏ l : Link H, p4Q2PZ37ASC_maxMultiplicity m := by
          apply Finset.prod_le_prod
          · intro l _
            exact Nat.zero_le _
          · intro l _
            exact p4Q2PZ37ASC_multiplicity_le_max m (p l)
        _ = _ := by rw [Finset.prod_const,Finset.card_univ,Fintype.card_eq_nat_card]
    _ = _ := by
      rw [Finset.sum_const,Nat.nsmul_eq_mul,p4Q2PZ37ASC_closed_card]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_survivors_le_cycleWeight

theorem p4Q2PZ37ASC_count_le_cycleWeight
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (B : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ) (he : ∀ k, Step H 2 h2 beta hb (B k) = rho k • B k)
    (m : ℕ) (r : ℝ) (hr : 0 < r)
    (hclose : p4Q2PZ37ARW_normalizedError H beta hb m < r) :
    p4Q2PZ37ARL_spectralCount rho r ≤
      ((2^(p4Q2PZ37ASC_cycleDim H) *
        (p4Q2PZ37ASC_maxMultiplicity m)^(Nat.card (Link H)) : ℕ) : ℝ≥0∞) := by
  apply (p4Q2PZ37ASB_count_le H beta hb B rho he m r hr hclose).trans
  exact_mod_cast p4Q2PZ37ASC_survivors_le_cycleWeight H m

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASC_count_le_cycleWeight

end
end MGAP4D.MathlibAnalytic

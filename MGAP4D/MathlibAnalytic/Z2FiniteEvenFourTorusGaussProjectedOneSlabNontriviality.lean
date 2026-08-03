import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaussProjectedOneSlabTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Indicator of the finite gauge orbit containing a boundary configuration. -/
noncomputable def finiteGroupOrbitIndicator
    (G α : Type) [Group G] [Fintype α] [MulAction G α]
    (A : α) : FiniteBoundaryHilbert α :=
  WithLp.toLp 2 fun X : α => if ∃ g : G, g • X = A then 1 else 0

@[simp] theorem finiteGroupOrbitIndicator_apply
    (G α : Type) [Group G] [Fintype α] [MulAction G α]
    (A X : α) :
    finiteGroupOrbitIndicator G α A X =
      if ∃ g : G, g • X = A then 1 else 0 :=
  rfl

/-- Orbit indicators are pointwise nonnegative. -/
theorem finiteGroupOrbitIndicator_nonneg
    (G α : Type) [Group G] [Fintype α] [MulAction G α]
    (A X : α) :
    0 ≤ finiteGroupOrbitIndicator G α A X := by
  simp [finiteGroupOrbitIndicator]

/-- An orbit indicator takes value one at its defining configuration. -/
theorem finiteGroupOrbitIndicator_self
    (G α : Type) [Group G] [Fintype α] [MulAction G α]
    (A : α) :
    finiteGroupOrbitIndicator G α A A = 1 := by
  rw [finiteGroupOrbitIndicator_apply, if_pos]
  exact ⟨1, one_smul G A⟩

/-- Orbit indicators are invariant under the original finite group action. -/
theorem finiteGroupOrbitIndicator_mem_invariant
    (G α : Type) [Group G] [Fintype α] [MulAction G α]
    (A : α) :
    finiteGroupOrbitIndicator G α A ∈
      finiteGroupInvariantSubmodule G α := by
  intro a X
  rw [finiteGroupOrbitIndicator_apply, finiteGroupOrbitIndicator_apply]
  have horbit :
      (∃ g : G, g • (a • X) = A) ↔
        ∃ h : G, h • X = A := by
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g * a, by simpa [mul_smul] using hg⟩
    · rintro ⟨h, hh⟩
      refine ⟨h * a⁻¹, ?_⟩
      simpa [mul_smul, mul_assoc] using hh
  rw [show (∃ g : G, g • (a • X) = A) =
      (∃ h : G, h • X = A) from propext horbit]

/-- Canonical orbit-indicator vector in the invariant Hilbert subspace. -/
noncomputable def finiteGroupInvariantOrbitIndicator
    (G α : Type) [Group G] [Fintype α] [MulAction G α]
    (A : α) : finiteGroupInvariantSubmodule G α :=
  ⟨finiteGroupOrbitIndicator G α A,
    finiteGroupOrbitIndicator_mem_invariant G α A⟩

/-- Two configurations that are not related by any group element have disjoint
orbit indicators. -/
theorem finiteGroupOrbitIndicator_inner_eq_zero_of_not_related
    (G α : Type) [Group G] [Fintype α] [MulAction G α]
    (A B : α)
    (hsep : ∀ g : G, g • A ≠ B) :
    inner ℝ
        (finiteGroupOrbitIndicator G α A)
        (finiteGroupOrbitIndicator G α B) = 0 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro X _hX
  rw [finiteGroupOrbitIndicator_apply, finiteGroupOrbitIndicator_apply]
  by_cases hA : ∃ g : G, g • X = A
  · have hB : ¬ ∃ h : G, h • X = B := by
      rintro ⟨h, hh⟩
      rcases hA with ⟨g, hg⟩
      apply hsep (h * g⁻¹)
      calc
        (h * g⁻¹) • A = (h * g⁻¹) • (g • X) := by rw [hg]
        _ = h • X := by simp [mul_smul, mul_assoc]
        _ = B := hh
    simp [hA, hB]
  · simp [hA]

/-- A strictly positive finite kernel has a strictly positive normalized matrix
entry between any two nonempty orbit indicators. -/
theorem finiteKernelNormalizedOperator_orbitIndicator_matrixElement_pos
    (G α : Type) [Group G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hne : finiteKernelOperator kernel ≠ 0)
    (hpos : ∀ X Y : α, 0 < kernel X Y)
    (A B : α) :
    0 < inner ℝ
      (finiteKernelNormalizedOperator kernel
        (finiteGroupOrbitIndicator G α A))
      (finiteGroupOrbitIndicator G α B) := by
  classical
  rw [finiteKernelNormalizedOperator_matrixElement]
  apply mul_pos
  · exact inv_pos.mpr (norm_pos_iff.mpr hne)
  · apply (Finset.sum_pos_iff_of_nonneg ?_).2
    · intro X _hX
      exact Finset.sum_nonneg fun Y _hY =>
        mul_nonneg
          (mul_nonneg
            (finiteGroupOrbitIndicator_nonneg G α A X)
            (le_of_lt (hpos X Y)))
          (finiteGroupOrbitIndicator_nonneg G α B Y)
    · refine ⟨A, Finset.mem_univ A, ?_⟩
      apply (Finset.sum_pos_iff_of_nonneg ?_).2
      · intro Y _hY
        exact mul_nonneg
          (mul_nonneg
            (finiteGroupOrbitIndicator_nonneg G α A A)
            (le_of_lt (hpos A Y)))
          (finiteGroupOrbitIndicator_nonneg G α B Y)
      · refine ⟨B, Finset.mem_univ B, ?_⟩
        rw [finiteGroupOrbitIndicator_self,
          finiteGroupOrbitIndicator_self]
        simpa using hpos A B

/-- Canonical time-zero vertex on the side-two spatial torus (`H = 0`). -/
def finiteEvenFourTorusZ2GaussWitnessVertex :
    FiniteEvenFourTorusSpatialVertex 0 :=
  ⟨fun _ => 0, rfl⟩

/-- First distinguished spatial direction. -/
def finiteEvenFourTorusZ2GaussWitnessDirectionOne :
    FiniteEvenFourTorusSpatialDirection :=
  ⟨1, by decide⟩

/-- Second distinguished spatial direction. -/
def finiteEvenFourTorusZ2GaussWitnessDirectionTwo :
    FiniteEvenFourTorusSpatialDirection :=
  ⟨2, by decide⟩

/-- Distinguished spatial plaquette used to separate two gauge orbits. -/
def finiteEvenFourTorusZ2GaussWitnessPlaquette :
    FiniteEvenFourTorusSpatialPlaquette 0 :=
  (finiteEvenFourTorusZ2GaussWitnessVertex,
    ⟨(finiteEvenFourTorusZ2GaussWitnessDirectionOne,
       finiteEvenFourTorusZ2GaussWitnessDirectionTwo), by decide⟩)

/-- Distinguished first edge of the witness plaquette. -/
def finiteEvenFourTorusZ2GaussWitnessLink :
    FiniteEvenFourTorusSpatialLink 0 :=
  (finiteEvenFourTorusZ2GaussWitnessVertex,
    finiteEvenFourTorusZ2GaussWitnessDirectionOne)

/-- The identity slice has trivial witness-plaquette holonomy. -/
theorem finiteEvenFourTorusZ2GaussWitness_identity_holonomy :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy 0
      (finiteEvenFourTorusZ2IdentitySlice 0)
      finiteEvenFourTorusZ2GaussWitnessPlaquette = 1 := by
  native_decide

/-- Exciting one edge of the witness plaquette changes its holonomy. -/
theorem finiteEvenFourTorusZ2GaussWitness_excitation_holonomy :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy 0
      (finiteEvenFourTorusZ2SingleLinkExcitation 0
        finiteEvenFourTorusZ2GaussWitnessLink)
      finiteEvenFourTorusZ2GaussWitnessPlaquette = z2GaugeNontrivial := by
  native_decide

/-- The identity slice and the one-edge excitation lie in distinct residual
slice-gauge orbits, as certified by their different plaquette holonomies. -/
theorem finiteEvenFourTorusZ2GaussWitness_not_gauge_related :
    ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0,
      g • finiteEvenFourTorusZ2IdentitySlice 0 ≠
        finiteEvenFourTorusZ2SingleLinkExcitation 0
          finiteEvenFourTorusZ2GaussWitnessLink := by
  intro g h
  have hhol := congrArg
    (fun A : FiniteEvenFourTorusZ2SliceConfiguration 0 =>
      finiteEvenFourTorusZ2SpatialPlaquetteHolonomy 0 A
        finiteEvenFourTorusZ2GaussWitnessPlaquette) h
  rw [finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_smul,
    finiteEvenFourTorusZ2GaussWitness_identity_holonomy,
    finiteEvenFourTorusZ2GaussWitness_excitation_holonomy] at hhol
  exact (by native_decide : (1 : Z2Gauge) ≠ z2GaugeNontrivial) hhol

/-- Gauge-invariant orbit state of the identity boundary slice. -/
noncomputable def finiteEvenFourTorusZ2GaussWitnessIdentityState :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 :=
  finiteGroupInvariantOrbitIndicator
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
    (FiniteEvenFourTorusZ2SliceConfiguration 0)
    (finiteEvenFourTorusZ2IdentitySlice 0)

/-- Gauge-invariant orbit state of the plaquette-excited boundary slice. -/
noncomputable def finiteEvenFourTorusZ2GaussWitnessExcitationState :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 :=
  finiteGroupInvariantOrbitIndicator
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
    (FiniteEvenFourTorusZ2SliceConfiguration 0)
    (finiteEvenFourTorusZ2SingleLinkExcitation 0
      finiteEvenFourTorusZ2GaussWitnessLink)

/-- The two gauge-invariant witness states are orthogonal. -/
theorem finiteEvenFourTorusZ2GaussWitnessStates_orthogonal :
    inner ℝ finiteEvenFourTorusZ2GaussWitnessIdentityState
      finiteEvenFourTorusZ2GaussWitnessExcitationState = 0 :=
  finiteGroupOrbitIndicator_inner_eq_zero_of_not_related
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
    (FiniteEvenFourTorusZ2SliceConfiguration 0)
    (finiteEvenFourTorusZ2IdentitySlice 0)
    (finiteEvenFourTorusZ2SingleLinkExcitation 0
      finiteEvenFourTorusZ2GaussWitnessLink)
    finiteEvenFourTorusZ2GaussWitness_not_gauge_related

/-- The actual normalized one-slab transfer has a strictly positive matrix
entry between the two plaquette-separated gauge-invariant orbit states. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_witness_matrix_pos
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 < inner ℝ
      (finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy
        finiteEvenFourTorusZ2GaussWitnessIdentityState)
      finiteEvenFourTorusZ2GaussWitnessExcitationState := by
  exact finiteKernelNormalizedOperator_orbitIndicator_matrixElement_pos
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
    (FiniteEvenFourTorusZ2SliceConfiguration 0)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      0 β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
      0 β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_pos
      0 β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2IdentitySlice 0)
    (finiteEvenFourTorusZ2SingleLinkExcitation 0
      finiteEvenFourTorusZ2GaussWitnessLink)

/-- The Gauss-projected actual geometric one-slab transfer is explicitly
nonidentity on a gauge-invariant plaquette-separated observable sector. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_ne_identity
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy ≠ 1 := by
  intro hId
  have hmatrix := congrArg
    (fun T : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 →L[ℝ]
        FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 =>
      inner ℝ (T finiteEvenFourTorusZ2GaussWitnessIdentityState)
        finiteEvenFourTorusZ2GaussWitnessExcitationState) hId
  have hpos :=
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_witness_matrix_pos
      β energyIdentity energyNontrivial hβ hEnergy
  change inner ℝ
      (finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy
        finiteEvenFourTorusZ2GaussWitnessIdentityState)
      finiteEvenFourTorusZ2GaussWitnessExcitationState =
    inner ℝ finiteEvenFourTorusZ2GaussWitnessIdentityState
      finiteEvenFourTorusZ2GaussWitnessExcitationState at hmatrix
  rw [finiteEvenFourTorusZ2GaussWitnessStates_orthogonal] at hmatrix
  rw [hmatrix] at hpos
  exact (lt_irrefl 0) hpos

end

end MathlibAnalytic
end MGAP4D

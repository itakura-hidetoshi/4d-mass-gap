import MGAP4D.MathlibAnalytic.FiniteDimensionalPrincipalMinorExcitationNonempty
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronGroundSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Pointwise comparison of two real-valued functions on a finite list implies
comparison of their sums. -/
theorem list_sum_map_le_of_forall_le
    {ι : Type}
    (l : List ι)
    (f g : ι → ℝ)
    (hle : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : f a ≤ g a := hle a (by simp)
      have ht : ∀ x ∈ l, f x ≤ g x := by
        intro x hx
        exact hle x (by simp [hx])
      simp only [List.map_cons, List.sum_cons]
      linarith [ih ht]

/-- If one term is strictly smaller and all remaining terms are no larger,
the finite list sum is strictly smaller. -/
theorem list_sum_map_lt_of_forall_le_of_exists_lt
    {ι : Type}
    (l : List ι)
    (f g : ι → ℝ)
    (hle : ∀ x ∈ l, f x ≤ g x)
    (hex : ∃ x ∈ l, f x < g x) :
    (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => simp at hex
  | cons a l ih =>
      have ha : f a ≤ g a := hle a (by simp)
      have ht : ∀ x ∈ l, f x ≤ g x := by
        intro x hx
        exact hle x (by simp [hx])
      by_cases hstrict : f a < g a
      · have htail := list_sum_map_le_of_forall_le l f g ht
        simp only [List.map_cons, List.sum_cons]
        linarith
      · have htailExists : ∃ x ∈ l, f x < g x := by
          obtain ⟨x, hxmem, hxlt⟩ := hex
          simp only [List.mem_cons] at hxmem
          rcases hxmem with hxa | hxl
          · subst x
            exact False.elim (hstrict hxlt)
          · exact ⟨x, hxl, hxlt⟩
        have htail := ih ht htailExists
        simp only [List.map_cons, List.sum_cons]
        linarith

/-- The unique nonidentity element of the actual `Z₂` gauge group is not the
identity. -/
theorem z2GaugeNontrivial_ne_one : z2GaugeNontrivial ≠ (1 : Z2Gauge) := by
  native_decide

/-- The side-two spatial slice has only one spatial vertex. -/
instance finiteEvenFourTorusSpatialVertex_zero_subsingleton :
    Subsingleton (FiniteEvenFourTorusSpatialVertex 0) := by
  constructor
  intro v w
  apply Subtype.ext
  funext μ
  exact Subsingleton.elim _ _

/-- Every side-two spatial unit step returns to the same unique spatial
vertex. -/
theorem finiteEvenFourTorusSpatialVertexStep_zero
    (v : FiniteEvenFourTorusSpatialVertex 0)
    (μ : FiniteEvenFourTorusSpatialDirection) :
    finiteEvenFourTorusSpatialVertexStep 0 v μ = v :=
  Subsingleton.elim _ _

/-- Residual gauge transformations act trivially on the side-two spatial
slice: every spatial link is a loop at the unique vertex and `Z₂` is abelian. -/
theorem finiteEvenFourTorusZ2ResidualSlice_smul_zero
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
    (A : FiniteEvenFourTorusZ2SliceConfiguration 0) :
    g • A = A := by
  funext e
  rw [finiteEvenFourTorusZ2ResidualSlice_smul_apply,
    finiteEvenFourTorusSpatialVertexStep_zero]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Every side-two point state is automatically residual-Gauss invariant. -/
noncomputable def finiteEvenFourTorusZ2InvariantPointState
    (A : FiniteEvenFourTorusZ2SliceConfiguration 0) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 :=
  ⟨finiteBoundaryPointVector A, by
    intro g X
    rw [finiteEvenFourTorusZ2ResidualSlice_smul_zero]
  ⟩

/-- Identity point state in the side-two invariant Hilbert space. -/
noncomputable def finiteEvenFourTorusZ2StrictWitnessIdentityState :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 :=
  finiteEvenFourTorusZ2InvariantPointState
    (finiteEvenFourTorusZ2IdentitySlice 0)

/-- One-link point state in the side-two invariant Hilbert space. -/
noncomputable def finiteEvenFourTorusZ2StrictWitnessExcitationState :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 :=
  finiteEvenFourTorusZ2InvariantPointState
    (finiteEvenFourTorusZ2SingleLinkExcitation 0
      finiteEvenFourTorusZ2GaussWitnessLink)

/-- Every temporal-gauge crossing action on equal boundaries is the same:
each temporal plaquette carries the identity energy. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingAction_self_eq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction
        H β energyIdentity energyNontrivial A A =
      finiteEvenFourTorusZ2TemporalGaugeCrossingAction
        H β energyIdentity energyNontrivial B B := by
  unfold finiteEvenFourTorusZ2TemporalGaugeCrossingAction
  simp

/-- Under strict coupling, changing one temporal crossing link from identity to
nontrivial strictly raises the crossing action. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingAction_identity_lt_singleLink
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction
        0 β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2IdentitySlice 0)
        (finiteEvenFourTorusZ2IdentitySlice 0) <
      finiteEvenFourTorusZ2TemporalGaugeCrossingAction
        0 β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2IdentitySlice 0)
        (finiteEvenFourTorusZ2SingleLinkExcitation 0
          finiteEvenFourTorusZ2GaussWitnessLink) := by
  unfold finiteEvenFourTorusZ2TemporalGaugeCrossingAction
  apply list_sum_map_lt_of_forall_le_of_exists_lt
  · intro e _he
    by_cases hlink : e = finiteEvenFourTorusZ2GaussWitnessLink
    · subst e
      simp [finiteEvenFourTorusZ2IdentitySlice,
        finiteEvenFourTorusZ2SingleLinkExcitation,
        z2GaugeNontrivial_ne_one, hEnergy.le]
    · simp [finiteEvenFourTorusZ2IdentitySlice,
        finiteEvenFourTorusZ2SingleLinkExcitation, hlink]
  · refine ⟨finiteEvenFourTorusZ2GaussWitnessLink, by simp, ?_⟩
    simpa [finiteEvenFourTorusZ2IdentitySlice,
      finiteEvenFourTorusZ2SingleLinkExcitation,
      z2GaugeNontrivial_ne_one] using hEnergy

/-- The strict crossing-action increase is exactly the strict midpoint
inequality needed for the two-state one-slab kernel determinant; all spatial
half-actions cancel. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabAction_witness_midpoint_strict
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
        0 β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2IdentitySlice 0)
        (finiteEvenFourTorusZ2IdentitySlice 0) +
      finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
        0 β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2SingleLinkExcitation 0
          finiteEvenFourTorusZ2GaussWitnessLink)
        (finiteEvenFourTorusZ2SingleLinkExcitation 0
          finiteEvenFourTorusZ2GaussWitnessLink) <
      2 * finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
        0 β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2IdentitySlice 0)
        (finiteEvenFourTorusZ2SingleLinkExcitation 0
          finiteEvenFourTorusZ2GaussWitnessLink) := by
  have hcross :=
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction_identity_lt_singleLink
      β energyIdentity energyNontrivial hEnergy
  have hdiag :=
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction_self_eq
      0 β energyIdentity energyNontrivial
      (finiteEvenFourTorusZ2IdentitySlice 0)
      (finiteEvenFourTorusZ2SingleLinkExcitation 0
        finiteEvenFourTorusZ2GaussWitnessLink)
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
  nlinarith

/-- The raw temporal-gauge one-slab kernel has a strictly positive principal
minor on the identity/one-link witness sector whenever `β > 0` and the
nontrivial plaquette energy is strictly larger. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabKernel_witness_minor_pos
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 <
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel
          (finiteEvenFourTorusZ2IdentitySlice 0)
          (finiteEvenFourTorusZ2IdentitySlice 0) *
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel
          (finiteEvenFourTorusZ2SingleLinkExcitation 0
            finiteEvenFourTorusZ2GaussWitnessLink)
          (finiteEvenFourTorusZ2SingleLinkExcitation 0
            finiteEvenFourTorusZ2GaussWitnessLink) -
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel
          (finiteEvenFourTorusZ2IdentitySlice 0)
          (finiteEvenFourTorusZ2SingleLinkExcitation 0
            finiteEvenFourTorusZ2GaussWitnessLink) *
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel
          (finiteEvenFourTorusZ2SingleLinkExcitation 0
            finiteEvenFourTorusZ2GaussWitnessLink)
          (finiteEvenFourTorusZ2IdentitySlice 0) := by
  let K := finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  let A := finiteEvenFourTorusZ2IdentitySlice 0
  let B := finiteEvenFourTorusZ2SingleLinkExcitation 0
    finiteEvenFourTorusZ2GaussWitnessLink
  have hsymm : K.kernel B A = K.kernel A B :=
    finite_os_reflection_kernel_symmetric K.toCertificate B A
  have haction :=
    finiteEvenFourTorusZ2TemporalGaugeOneSlabAction_witness_midpoint_strict
      β energyIdentity energyNontrivial hEnergy
  change 0 < K.kernel A A * K.kernel B B - K.kernel A B * K.kernel B A
  rw [hsymm]
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann]
  apply sub_pos.mpr
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- Exact normalized matrix element of the actual invariant unfixed transfer on
side-two invariant point states. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_point_matrixElement
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration 0) :
    inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2InvariantPointState A))
      (finiteEvenFourTorusZ2InvariantPointState B) =
      ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy‖⁻¹ *
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        0 β energyIdentity energyNontrivial hβ hEnergy).kernel A B := by
  change inner ℝ
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
      0 β energyIdentity energyNontrivial hβ hEnergy
      (finiteBoundaryPointVector A))
    (finiteBoundaryPointVector B) = _
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
    finiteKernelNormalizedOperator
  rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
  congr 1
  change inner ℝ
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
      0 β energyIdentity energyNontrivial hβ hEnergy
      (finiteBoundaryPointVector A))
    (finiteBoundaryPointVector B) = _
  rw [finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_apply_invariant
    0 β energyIdentity energyNontrivial hβ hEnergy
    (finiteEvenFourTorusZ2InvariantPointState A)]
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
  exact finiteKernelOperator_point_matrixElement
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      0 β energyIdentity energyNontrivial hβ hEnergy).kernel A B

/-- The normalized actual invariant unfixed transfer retains a strictly
positive two-state principal minor under strict coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_witness_minor_pos
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 <
      inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le
          finiteEvenFourTorusZ2StrictWitnessIdentityState)
        finiteEvenFourTorusZ2StrictWitnessIdentityState *
      inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le
          finiteEvenFourTorusZ2StrictWitnessExcitationState)
        finiteEvenFourTorusZ2StrictWitnessExcitationState -
      inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le
          finiteEvenFourTorusZ2StrictWitnessIdentityState)
        finiteEvenFourTorusZ2StrictWitnessExcitationState *
      inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le
          finiteEvenFourTorusZ2StrictWitnessExcitationState)
        finiteEvenFourTorusZ2StrictWitnessIdentityState := by
  let c := ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
    0 β energyIdentity energyNontrivial hβ.le hEnergy.le‖⁻¹
  let K := finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  let A := finiteEvenFourTorusZ2IdentitySlice 0
  let B := finiteEvenFourTorusZ2SingleLinkExcitation 0
    finiteEvenFourTorusZ2GaussWitnessLink
  have hc : 0 < c := by
    exact inv_pos.mpr (norm_pos_iff.mpr
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le))
  have hraw :=
    finiteEvenFourTorusZ2TemporalGaugeOneSlabKernel_witness_minor_pos
      β energyIdentity energyNontrivial hβ hEnergy
  have hscaled :
      0 < (c * c) *
        (K.kernel A A * K.kernel B B - K.kernel A B * K.kernel B A) :=
    mul_pos (mul_pos hc hc) hraw
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_point_matrixElement,
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_point_matrixElement,
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_point_matrixElement,
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_point_matrixElement]
  change 0 < (c * K.kernel A A) * (c * K.kernel B B) -
    (c * K.kernel A B) * (c * K.kernel B A)
  nlinarith

/-- Under strict coupling, the actual side-two compressed unfixed transfer has
an unconditionally inhabited strictly excited spectral sector. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le) := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  obtain ⟨p, _hpne, _hppos, _hpfix, hpgen⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariant_fixed_space_generated_by_positiveGround
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  exact D.nonempty_excitedSpectralIndex_of_fixed_space_generated_and_minor_pos
    p hpgen
    finiteEvenFourTorusZ2StrictWitnessIdentityState
    finiteEvenFourTorusZ2StrictWitnessExcitationState
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_witness_minor_pos
      β energyIdentity energyNontrivial hβ hEnergy)

end

end MathlibAnalytic
end MGAP4D

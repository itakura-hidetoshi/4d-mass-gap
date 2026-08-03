import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelPerronPositiveGround
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The ambient actual unfixed-gauge finite `Z₂` transfer has a nonzero
pointwise-strictly-positive fixed vector, and every ambient fixed vector is a
real scalar multiple of it. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbient_fixed_space_generated_by_positiveGround
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ∃ p : FiniteEvenFourTorusZ2SliceHilbert H,
      p ≠ 0 ∧
      FiniteBoundaryPointwisePositive p ∧
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy p = p ∧
      ∀ g : FiniteEvenFourTorusZ2SliceHilbert H,
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy g = g →
          ∃ c : ℝ, g = c • p := by
  obtain ⟨f, hfne, hffix⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbient_exists_nonzero_fixedVector
      H β energyIdentity energyNontrivial hβ hEnergy
  simpa [finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer] using
    finiteKernelNormalizedOperator_fixed_space_generated_by_positive_ground
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
        H β energyIdentity energyNontrivial hβ hEnergy)
      f hfne hffix

/-- The actual compressed Gauss-invariant transfer has a nonzero ambiently
strictly-positive fixed vector, and every compressed fixed vector lies on its
real line. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariant_fixed_space_generated_by_positiveGround
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ∃ p : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      p ≠ 0 ∧
      FiniteBoundaryPointwisePositive p.1 ∧
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy p = p ∧
      ∀ g : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
        finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy g = g →
          ∃ c : ℝ, g = c • p := by
  obtain ⟨p, hpne, hppos, hpfix, hpgen⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbient_fixed_space_generated_by_positiveGround
      H β energyIdentity energyNontrivial hβ hEnergy
  have hpinv :=
    finiteEvenFourTorusZ2UnfixedGauge_fixedVector_mem_invariant
      H β energyIdentity energyNontrivial hβ hEnergy p hpfix
  let q : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
    ⟨p, hpinv⟩
  have hqne : q ≠ 0 := by
    intro hqzero
    apply hpne
    have hval := congrArg Subtype.val hqzero
    simpa [q] using hval
  have hqfix :
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy q = q := by
    apply Subtype.ext
    exact hpfix
  refine ⟨q, hqne, ?_, hqfix, ?_⟩
  · exact hppos
  · intro g hgfix
    have hgambient :
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy g.1 = g.1 := by
      have hval := congrArg Subtype.val hgfix
      simpa using hval
    obtain ⟨c, hc⟩ := hpgen g.1 hgambient
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [q] using hc

/-- Any two fixed vectors of the actual compressed invariant transfer are
linearly dependent through the same strictly-positive ground ray. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariant_fixed_pair_generated_by_positiveGround
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f g : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (hffix : finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy f = f)
    (hgfix : finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy g = g) :
    ∃ p : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      p ≠ 0 ∧
      FiniteBoundaryPointwisePositive p.1 ∧
      ∃ a b : ℝ, f = a • p ∧ g = b • p := by
  obtain ⟨p, hpne, hppos, _hpfix, hpgen⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariant_fixed_space_generated_by_positiveGround
      H β energyIdentity energyNontrivial hβ hEnergy
  obtain ⟨a, ha⟩ := hpgen f hffix
  obtain ⟨b, hb⟩ := hpgen g hgfix
  exact ⟨p, hpne, hppos, a, b, ha, hb⟩

end

end MathlibAnalytic
end MGAP4D

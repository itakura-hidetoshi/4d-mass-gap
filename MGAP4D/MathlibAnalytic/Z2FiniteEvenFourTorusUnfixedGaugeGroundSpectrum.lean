import MGAP4D.MathlibAnalytic.FiniteDimensionalGroundNullOperatorCharacterization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeSupportHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Generic positive-contraction spectral data carried by the ambient actual
finite `Z₂` unfixed-gauge one-slab transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteDimensionalSymmetricPositiveContractionData
      (FiniteEvenFourTorusZ2SliceHilbert H) :=
  { operator :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
    symmetric :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_isSymmetric
        H β energyIdentity energyNontrivial hβ hEnergy
    quadratic_nonneg :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_quadratic_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
    norm_apply_le :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_norm_apply_le
        H β energyIdentity energyNontrivial hβ hEnergy }

/-- The ambient normalized transfer has a nonempty canonical ground spectrum. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientGroundSpectralIndex_nonempty
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Nonempty
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).GroundSpectralIndex :=
  (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).nonempty_groundSpectralIndex_of_norm_eq_one
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_norm_eq_one
        H β energyIdentity energyNontrivial hβ hEnergy)

/-- The ambient transfer has a nonzero exact fixed vector synthesized from its
ground spectrum. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbient_exists_nonzero_fixedVector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ∃ v : FiniteEvenFourTorusZ2SliceHilbert H,
      v ≠ 0 ∧
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy v = v := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy
  letI : Nonempty D.GroundSpectralIndex :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientGroundSpectralIndex_nonempty
      H β energyIdentity energyNontrivial hβ hEnergy
  simpa [D, finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData] using
    D.exists_nonzero_fixedVector_of_nonempty_ground

/-- Every ambient fixed vector is automatically Gauss invariant because every
unfixed-transfer output lies in the invariant subspace. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_fixedVector_mem_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (v : FiniteEvenFourTorusZ2SliceHilbert H)
    (hfix : finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy v = v) :
    v ∈ finiteGroupInvariantSubmodule
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) := by
  have hout :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_mem_invariant
      H β energyIdentity energyNontrivial hβ hEnergy v
  rw [hfix] at hout
  exact hout

/-- The compressed invariant transfer therefore has a nonzero exact fixed
vector. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariant_exists_nonzero_fixedVector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ∃ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      f ≠ 0 ∧
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f = f := by
  obtain ⟨v, hv, hfix⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbient_exists_nonzero_fixedVector
      H β energyIdentity energyNontrivial hβ hEnergy
  let f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
    ⟨v, finiteEvenFourTorusZ2UnfixedGauge_fixedVector_mem_invariant
      H β energyIdentity energyNontrivial hβ hEnergy v hfix⟩
  refine ⟨f, ?_, ?_⟩
  · intro hf
    apply hv
    have hval := congrArg Subtype.val hf
    simpa [f] using hval
  · apply Subtype.ext
    exact hfix

/-- The compressed invariant transfer also has operator norm exactly one. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_eq_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ‖finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy‖ = 1 := by
  let T := finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
    H β energyIdentity energyNontrivial hβ hEnergy
  have hupper : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound (by norm_num)
    intro x
    simpa [T] using
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_apply_le
        H β energyIdentity energyNontrivial hβ hEnergy x
  obtain ⟨f, hf, hfix⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariant_exists_nonzero_fixedVector
      H β energyIdentity energyNontrivial hβ hEnergy
  have hlowerRaw := T.le_opNorm f
  rw [hfix] at hlowerRaw
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hlower : 1 ≤ ‖T‖ := by
    nlinarith [norm_nonneg T]
  exact le_antisymm hupper hlower

/-- Ground indices of the actual compressed invariant transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).GroundSpectralIndex

/-- Strictly excited indices of the actual compressed invariant transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).ExcitedSpectralIndex

/-- Null indices of the actual compressed invariant transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).NullSpectralIndex

/-- The actual compressed invariant transfer has nonempty ground spectrum at
every finite side length. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_nonempty
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex
        H β energyIdentity energyNontrivial hβ hEnergy) := by
  obtain ⟨f, hf, _hfix⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariant_exists_nonzero_fixedVector
      H β energyIdentity energyNontrivial hβ hEnergy
  letI : Nontrivial (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :=
    ⟨⟨f, 0, hf⟩⟩
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy).nonempty_groundSpectralIndex_of_norm_eq_one
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_eq_one
          H β energyIdentity energyNontrivial hβ hEnergy)

end

end MathlibAnalytic
end MGAP4D

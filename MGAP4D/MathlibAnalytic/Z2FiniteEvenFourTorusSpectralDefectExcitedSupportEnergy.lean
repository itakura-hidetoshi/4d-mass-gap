import MGAP4D.MathlibAnalytic.FiniteDimensionalSpectralDefectExcitedSupportNontriviality
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusActualGroundLiftedOperatorBridge
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeSupportHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Strictly excited indices of the actual ambient finite-Z₂ transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugeAmbientExcitedSpectralIndex
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).ExcitedSpectralIndex

/-- Package Z's nonzero complemented block already forces the full actual
ambient spectral defect `P_ground - T` itself to be nonzero throughout a whole
small-positive interval. -/
theorem finiteEvenFourTorusZ2AmbientGroundSpectralDefect_exists_smallPositive_ne_zero_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
              0 β energyIdentity energyNontrivial hβ.le hEnergy.le).groundSpectralProjector -
          (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
              0 β energyIdentity energyNontrivial hβ.le hEnergy.le).operator ≠ 0 := by
  rcases
      finiteEvenFourTorusZ2ActualGroundSpectralDefect_exists_smallPositive_uniformComplementBlock_ne_zero_zero
        energyIdentity energyNontrivial hEnergy with
    ⟨ε, hε, hBlock⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε hzero
  apply hBlock β hβ hβε
  rw [hzero]
  simp

/-- Hence the actual ambient transfer has a genuine strictly excited spectral
mode for every sufficiently small positive coupling. -/
theorem finiteEvenFourTorusZ2AmbientExcitedSpectralIndex_exists_smallPositive_nonempty_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
        Nonempty
          (FiniteEvenFourTorusZ2UnfixedGaugeAmbientExcitedSpectralIndex
            0 β energyIdentity energyNontrivial hβ.le hEnergy.le) := by
  rcases
      finiteEvenFourTorusZ2AmbientGroundSpectralDefect_exists_smallPositive_ne_zero_zero
        energyIdentity energyNontrivial hEnergy with
    ⟨ε, hε, hDefect⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  let D :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  exact
    D.nonempty_excitedSpectralIndex_of_groundSpectralProjector_sub_operator_ne_zero
      (hDefect β hβ hβε)

/-- Every ambient excited canonical eigenvector is automatically Gauss
invariant.  The reason is exact and elementary: its eigenvalue is strictly
positive, every transfer output is invariant, and the eigenvector is recovered
by multiplying that output by the inverse eigenvalue. -/
theorem finiteEvenFourTorusZ2AmbientExcitedEigenbasis_mem_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeAmbientExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).eigenbasis i.1 ∈
      finiteGroupInvariantSubmodule
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H) := by
  let D :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy
  let v : FiniteEvenFourTorusZ2SliceHilbert H := D.eigenbasis i.1
  have heig :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy v =
        D.eigenvalue i.1 • v := by
    simpa [D, finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData, v] using
      D.operator_apply_eigenbasis i.1
  have hout :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_mem_invariant
      H β energyIdentity energyNontrivial hβ hEnergy v
  have hscaled :
      (D.eigenvalue i.1)⁻¹ •
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy v ∈
        finiteGroupInvariantSubmodule
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) :=
    (finiteGroupInvariantSubmodule
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)).smul_mem _ hout
  have hEigenvalueNe : D.eigenvalue i.1 ≠ 0 := ne_of_gt i.2.1
  have hrecover :
      (D.eigenvalue i.1)⁻¹ •
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy v = v := by
    rw [heig, smul_smul, inv_mul_cancel₀ hEigenvalueNe, one_smul]
  change v ∈
    finiteGroupInvariantSubmodule
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
  rw [← hrecover]
  exact hscaled

/-- An ambient excited mode therefore forces the compressed Gauss-invariant
transfer to have a nonzero ground spectral defect and hence a strictly excited
canonical mode of its own. -/
theorem finiteEvenFourTorusZ2InvariantExcitedSpectralIndex_nonempty_of_ambientExcited
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeAmbientExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ hEnergy) := by
  let Damb :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy
  let Dinv :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy
  let v : FiniteEvenFourTorusZ2SliceHilbert H := Damb.eigenbasis i.1
  have hvInv :=
    finiteEvenFourTorusZ2AmbientExcitedEigenbasis_mem_invariant
      H β energyIdentity energyNontrivial hβ hEnergy i
  let q : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H := ⟨v, hvInv⟩
  have hvne : v ≠ 0 := by
    intro hv
    have hnorm : ‖v‖ = 1 := by
      simp [v]
    rw [hv] at hnorm
    norm_num at hnorm
  have hqne : q ≠ 0 := by
    intro hq
    apply hvne
    have hval := congrArg Subtype.val hq
    simpa [q] using hval
  have heigAmb :
      Damb.operator v = Damb.eigenvalue i.1 • v :=
    Damb.operator_apply_eigenbasis i.1
  have heigInv :
      Dinv.operator q = Damb.eigenvalue i.1 • q := by
    apply Subtype.ext
    simpa [Damb, Dinv, q, v,
      finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using heigAmb
  have hDefect : Dinv.groundSpectralProjector - Dinv.operator ≠ 0 :=
    Dinv.groundSpectralProjector_sub_operator_ne_zero_of_strict_eigenvector
      q hqne (Damb.eigenvalue i.1) i.2.1 i.2.2 heigInv
  exact
    Dinv.nonempty_excitedSpectralIndex_of_groundSpectralProjector_sub_operator_ne_zero
      hDefect

/-- The strictly excited sector therefore survives the actual Gauss-invariant
compression on a whole sufficiently small positive-coupling interval. -/
theorem finiteEvenFourTorusZ2InvariantExcitedSpectralIndex_exists_smallPositive_nonempty_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
        Nonempty
          (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
            0 β energyIdentity energyNontrivial hβ.le hEnergy.le) := by
  rcases
      finiteEvenFourTorusZ2AmbientExcitedSpectralIndex_exists_smallPositive_nonempty_zero
        energyIdentity energyNontrivial hEnergy with
    ⟨ε, hε, hAmbient⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  let i : FiniteEvenFourTorusZ2UnfixedGaugeAmbientExcitedSpectralIndex
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le :=
    Classical.choice (hAmbient β hβ hβε)
  exact
    finiteEvenFourTorusZ2InvariantExcitedSpectralIndex_nonempty_of_ambientExcited
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le i

/-- On the same interval, the actual Gauss-invariant support Hamiltonian has a
strictly positive spectral energy.  This is an excited-state existence result,
not yet a uniform lower bound in volume or the exact continuum mass `33/20`. -/
theorem finiteEvenFourTorusZ2SupportHamiltonian_exists_smallPositive_positiveEnergy_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
        ∃ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
            0 β energyIdentity energyNontrivial hβ.le hEnergy.le,
          0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
            0 β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive := by
  rcases
      finiteEvenFourTorusZ2InvariantExcitedSpectralIndex_exists_smallPositive_nonempty_zero
        energyIdentity energyNontrivial hEnergy with
    ⟨ε, hε, hExcited⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  let D :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  let i : D.ExcitedSpectralIndex := Classical.choice (hExcited β hβ hβε)
  refine ⟨i, ?_⟩
  simpa [D, finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy] using
    D.excitedSpectralEnergy_pos i

/-- Equivalently, the actual Gauss-invariant positive-support Hamiltonian is a
nonzero operator throughout a sufficiently small positive-coupling interval. -/
theorem finiteEvenFourTorusZ2SupportHamiltonian_exists_smallPositive_ne_zero_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
        finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le ≠ 0 := by
  rcases
      finiteEvenFourTorusZ2InvariantExcitedSpectralIndex_exists_smallPositive_nonempty_zero
        energyIdentity energyNontrivial hEnergy with
    ⟨ε, hε, hExcited⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  let D :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  simpa [D, finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian] using
    D.positiveSpectralHamiltonian_ne_zero_of_nonempty_excitedSpectralIndex
      (hExcited β hβ hβε)

/-- Audit-visible Package-AA receipt. -/
structure Z2FiniteEvenFourTorusExcitedSupportEnergyPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  invariantExcitedNonempty :
    ∀ β : ℝ, ∀ hβ : 0 < β, β < epsilon →
      Nonempty
        (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le)
  supportHamiltonianNonzero :
    ∀ β : ℝ, ∀ hβ : 0 < β, β < epsilon →
      finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le ≠ 0
  positiveEnergy :
    ∀ β : ℝ, ∀ hβ : 0 < β, β < epsilon →
      ∃ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le,
        0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive

/-- Construct Package AA with one common small-positive interval. -/
noncomputable def z2FiniteEvenFourTorusExcitedSupportEnergyPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2FiniteEvenFourTorusExcitedSupportEnergyPackage
      energyIdentity energyNontrivial hEnergy := by
  let hExists :=
    finiteEvenFourTorusZ2InvariantExcitedSpectralIndex_exists_smallPositive_nonempty_zero
      energyIdentity energyNontrivial hEnergy
  let ε : ℝ := Classical.choose hExists
  have hSpec :
      0 < ε ∧
        ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
          Nonempty
            (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
              0 β energyIdentity energyNontrivial hβ.le hEnergy.le) :=
    Classical.choose_spec hExists
  have hε : 0 < ε := hSpec.1
  have hExcited :
      ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
        Nonempty
          (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
            0 β energyIdentity energyNontrivial hβ.le hEnergy.le) :=
    hSpec.2
  refine
    { epsilon := ε
      epsilon_pos := hε
      invariantExcitedNonempty := hExcited
      supportHamiltonianNonzero := ?_
      positiveEnergy := ?_ }
  · intro β hβ hβε
    let D :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le
    simpa [D, finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian] using
      D.positiveSpectralHamiltonian_ne_zero_of_nonempty_excitedSpectralIndex
        (hExcited β hβ hβε)
  · intro β hβ hβε
    let D :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le
    let i : D.ExcitedSpectralIndex := Classical.choice (hExcited β hβ hβε)
    refine ⟨i, ?_⟩
    simpa [D, finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy] using
      D.excitedSpectralEnergy_pos i

end

end MathlibAnalytic
end MGAP4D

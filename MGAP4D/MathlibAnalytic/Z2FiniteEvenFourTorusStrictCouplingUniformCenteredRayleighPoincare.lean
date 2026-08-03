import MGAP4D.MathlibAnalytic.FiniteDimensionalUniqueGroundCenteredRayleigh
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingUniformSpectralCap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- A volume-independent, basis-free Rayleigh contraction on the actual
strict-coupling `Z₂` transfer after removing its ground coordinates. -/
structure Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  centeredRayleigh :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0 →
        inner ℝ
            (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
              H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x ≤
          rate * ‖x‖ ^ 2

namespace Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (R : Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- The centered Rayleigh estimate bounds every actual excited transfer
eigenvalue by the same rate. -/
noncomputable def toSpectralCapCertificate :
    Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := R.rate
  rate_pos := R.rate_pos
  rate_lt_one := R.rate_lt_one
  excitedEigenvalue_le_rate := by
    intro H i
    let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
    change D.eigenvalue i.1 ≤ R.rate
    exact
      D.excited_eigenvalue_le_of_operator_quadraticForm_le_of_groundCoordinates_eq_zero
        R.rate (by
          intro x hx
          exact R.centeredRayleigh H x hx) i

/-- The spectral cap generated from centered Rayleigh data retains the supplied
rate exactly. -/
theorem toSpectralCapCertificate_rate_eq :
    R.toSpectralCapCertificate.rate = R.rate :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate

namespace Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- A common excited spectral cap generates a basis-free centered Rayleigh
contraction for the actual transfer at every finite volume. -/
noncomputable def toCenteredRayleighCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := C.rate
  rate_pos := C.rate_pos
  rate_lt_one := C.rate_lt_one
  centeredRayleigh := by
    intro H x hx
    let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
    have hnull : ¬ Nonempty D.NullSpectralIndex :=
      finiteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex_not_nonempty_strict
        H β energyIdentity energyNontrivial hβ hEnergy
    change inner ℝ (D.operator x) x ≤ C.rate * ‖x‖ ^ 2
    exact
      D.operator_quadraticForm_le_of_groundCoordinates_eq_zero_of_excited_cap
        hnull C.rate (fun i => C.excitedEigenvalue_le_rate H i) x hx

/-- The centered Rayleigh certificate generated from a spectral cap retains the
same rate. -/
theorem toCenteredRayleighCertificate_rate_eq :
    C.toCenteredRayleighCertificate.rate = C.rate :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

/-- A volume-independent Poincare/Dirichlet coercivity estimate for the actual
one-step transfer defect `I - T_H` on the ground-centered sector. -/
structure Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  coercivity : ℝ
  coercivity_pos : 0 < coercivity
  coercivity_lt_one : coercivity < 1
  centeredPoincare :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0 →
        coercivity * ‖x‖ ^ 2 ≤
          inner ℝ
            (x - finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
              H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x

namespace Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (R : Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Rayleigh contraction and Poincare coercivity are the same estimate after
the exact change of variables `coercivity = 1 - rate`. -/
noncomputable def toCenteredPoincareCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  coercivity := 1 - R.rate
  coercivity_pos := sub_pos.mpr R.rate_lt_one
  coercivity_lt_one := by linarith [R.rate_pos]
  centeredPoincare := by
    intro H x hx
    let T :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    have hRayleigh : inner ℝ (T x) x ≤ R.rate * ‖x‖ ^ 2 :=
      R.centeredRayleigh H x hx
    have hExpanded :
        (1 - R.rate) * ‖x‖ ^ 2 ≤
          ‖x‖ ^ 2 - inner ℝ (T x) x := by
      linarith
    have hDefect :
        inner ℝ (x - T x) x =
          ‖x‖ ^ 2 - inner ℝ (T x) x := by
      calc
        inner ℝ (x - T x) x =
            inner ℝ x x - inner ℝ (T x) x :=
          inner_sub_left x (T x) x
        _ = ‖x‖ ^ 2 - inner ℝ (T x) x := by
          rw [real_inner_self_eq_norm_sq]
    rw [hDefect]
    exact hExpanded

@[simp] theorem toCenteredPoincareCertificate_coercivity :
    R.toCenteredPoincareCertificate.coercivity = 1 - R.rate :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate

namespace Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (P : Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Poincare coercivity gives the exactly dual centered Rayleigh contraction
with `rate = 1 - coercivity`. -/
noncomputable def toCenteredRayleighCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := 1 - P.coercivity
  rate_pos := sub_pos.mpr P.coercivity_lt_one
  rate_lt_one := by linarith [P.coercivity_pos]
  centeredRayleigh := by
    intro H x hx
    let T :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    have hPoincare :
        P.coercivity * ‖x‖ ^ 2 ≤ inner ℝ (x - T x) x :=
      P.centeredPoincare H x hx
    have hDefect :
        inner ℝ (x - T x) x =
          ‖x‖ ^ 2 - inner ℝ (T x) x := by
      calc
        inner ℝ (x - T x) x =
            inner ℝ x x - inner ℝ (T x) x :=
          inner_sub_left x (T x) x
        _ = ‖x‖ ^ 2 - inner ℝ (T x) x := by
          rw [real_inner_self_eq_norm_sq]
    rw [hDefect] at hPoincare
    linarith

/-- Poincare coercivity therefore generates the common excited spectral cap. -/
noncomputable def toSpectralCapCertificate :
    Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  P.toCenteredRayleighCertificate.toSpectralCapCertificate

@[simp] theorem toCenteredRayleighCertificate_rate :
    P.toCenteredRayleighCertificate.rate = 1 - P.coercivity :=
  rfl

@[simp] theorem toSpectralCapCertificate_rate :
    P.toSpectralCapCertificate.rate = 1 - P.coercivity :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate

namespace Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- A common spectral cap also generates the exactly dual Poincare estimate. -/
noncomputable def toCenteredPoincareCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  C.toCenteredRayleighCertificate.toCenteredPoincareCertificate

@[simp] theorem toCenteredPoincareCertificate_coercivity :
    C.toCenteredPoincareCertificate.coercivity = 1 - C.rate :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

/-- Existence of a common spectral cap is exactly equivalent to existence of a
basis-free centered Rayleigh contraction for the actual family. -/
theorem z2UnfixedGaugeStrictCoupling_uniformCenteredRayleigh_iff_uniformSpectralCap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
          β energyIdentity energyNontrivial hβ hEnergy) ↔
      Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
          β energyIdentity energyNontrivial hβ hEnergy) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toSpectralCapCertificate⟩
  · rintro ⟨C⟩
    exact ⟨C.toCenteredRayleighCertificate⟩

/-- The same common spectral cap is exactly equivalent to a volume-independent
centered Poincare/Dirichlet coercivity estimate for `I - T_H`. -/
theorem z2UnfixedGaugeStrictCoupling_uniformCenteredPoincare_iff_uniformSpectralCap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
          β energyIdentity energyNontrivial hβ hEnergy) ↔
      Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
          β energyIdentity energyNontrivial hβ hEnergy) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toSpectralCapCertificate⟩
  · rintro ⟨C⟩
    exact ⟨C.toCenteredPoincareCertificate⟩

end

end MathlibAnalytic
end MGAP4D

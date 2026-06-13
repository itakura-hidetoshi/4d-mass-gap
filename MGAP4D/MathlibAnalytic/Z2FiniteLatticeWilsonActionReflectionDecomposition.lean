import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonReflectionFactorization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The crossing-plane Wilson action obtained from the list of `Z₂` boundary
variables. -/
def z2CrossingAction
    {α : Type} [Fintype α]
    (crossingVariables : List (α → Z2Gauge))
    (energyIdentity energyNontrivial : ℝ)
    (x y : α) : ℝ :=
  (crossingVariables.map fun q =>
    if (q x)⁻¹ * q y = 1 then energyIdentity else energyNontrivial).sum

/-- The product of all transported local `Z₂` Wilson kernels is the exponential
of minus beta times the additive crossing action. -/
theorem z2_crossing_kernel_product_eq_exp_action
    {α : Type} [Fintype α]
    (crossingVariables : List (α → Z2Gauge))
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x y : α) :
    ((crossingVariables.map fun q =>
      (z2GaugeWilsonPlaquetteGramKernel
        β energyIdentity energyNontrivial hβ hEnergy).kernel (q x) (q y)).prod) =
      Real.exp (-β *
        z2CrossingAction crossingVariables energyIdentity energyNontrivial x y) := by
  induction crossingVariables with
  | nil =>
      simp [z2CrossingAction]
  | cons q qs ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons,
        z2CrossingAction]
      rw [z2GaugeWilsonPlaquetteGramKernel_eq_boltzmann]
      rw [ih]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Reflection decomposition of the finite-lattice Wilson action.

This is the geometric statement expected from a time-reflection split of the
plaquette set: same-side plaquettes contribute `halfAction x` and
`halfAction y`, while every crossing plaquette contributes one local `Z₂`
boundary interaction. -/
structure Z2FiniteLatticeWilsonActionReflectionDecomposition
    (L : FiniteLatticeWilsonSystem) where
  PositiveConfiguration : Type
  [positiveFintype : Fintype PositiveConfiguration]
  [positiveInhabited : Inhabited PositiveConfiguration]
  assemble : PositiveConfiguration → PositiveConfiguration → L.Configuration
  reflection : L.Configuration → L.Configuration
  reflection_involutive : Function.Involutive reflection
  reflection_assemble :
    ∀ x y, reflection (assemble x y) = assemble y x
  energyIdentity : ℝ
  energyNontrivial : ℝ
  energy_order : energyIdentity ≤ energyNontrivial
  crossingVariables : List (PositiveConfiguration → Z2Gauge)
  halfAction : PositiveConfiguration → ℝ
  wilsonAction_decomposition :
    ∀ x y,
      L.wilsonAction (assemble x y) =
        halfAction x +
          z2CrossingAction crossingVariables
            energyIdentity energyNontrivial x y +
          halfAction y

attribute [instance]
  Z2FiniteLatticeWilsonActionReflectionDecomposition.positiveFintype
  Z2FiniteLatticeWilsonActionReflectionDecomposition.positiveInhabited

/-- The positive-half Boltzmann factor associated with the same-side Wilson
action. -/
def Z2FiniteLatticeWilsonActionReflectionDecomposition.halfSpaceFactor
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonActionReflectionDecomposition L)
    (x : D.PositiveConfiguration) : ℝ :=
  Real.exp (-L.beta * D.halfAction x)

/-- Additive decomposition of the Wilson action automatically supplies the
multiplicative reflection factorization required by the OS Gram bridge. -/
def Z2FiniteLatticeWilsonActionReflectionDecomposition.toFactorization
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonActionReflectionDecomposition L) :
    Z2FiniteLatticeWilsonReflectionFactorization L :=
  { PositiveConfiguration := D.PositiveConfiguration
    assemble := D.assemble
    reflection := D.reflection
    reflection_involutive := D.reflection_involutive
    reflection_assemble := D.reflection_assemble
    energyIdentity := D.energyIdentity
    energyNontrivial := D.energyNontrivial
    energy_order := D.energy_order
    crossingVariables := D.crossingVariables
    halfSpaceFactor := D.halfSpaceFactor
    wilson_weight_factorization := by
      intro x y
      rw [D.wilsonAction_decomposition x y]
      rw [z2_crossing_kernel_product_eq_exp_action]
      simp only [Z2FiniteLatticeWilsonActionReflectionDecomposition.halfSpaceFactor]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring }

/-- The full finite-volume `Z₂` Wilson kernel is OS reflection positive from the
additive plaquette-action decomposition alone. -/
theorem z2_finite_lattice_wilson_reflectionPositive_of_actionDecomposition
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonActionReflectionDecomposition L) :
    FiniteLatticeWilsonOSReflectionPositive D.toFactorization.toReflectionCertificate :=
  z2_finite_lattice_wilson_reflectionPositive D.toFactorization

/-- Audit-visible finite-volume OS certificate generated from an additive
Wilson-action reflection decomposition. -/
def z2FiniteLatticeWilsonOSCertificateOfActionDecomposition
    (L : FiniteLatticeWilsonSystem)
    (D : Z2FiniteLatticeWilsonActionReflectionDecomposition L) :
    FiniteWilsonOSReflectionPositivityCertificate L :=
  z2FiniteLatticeWilsonOSCertificate L D.toFactorization

end

end MathlibAnalytic
end MGAP4D

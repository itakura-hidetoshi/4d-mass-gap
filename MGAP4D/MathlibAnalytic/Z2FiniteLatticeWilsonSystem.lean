import MGAP4D.MathlibAnalytic.Z2SinglePlaquetteOSKernel
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual two-element multiplicative gauge group, obtained from the
additive group `ZMod 2`. -/
abbrev Z2Gauge : Type := Multiplicative (ZMod 2)

/-- The unique nonidentity element of `Z2Gauge`. -/
def z2GaugeNontrivial : Z2Gauge :=
  Multiplicative.ofAdd (1 : ZMod 2)

instance z2GaugeMeasurableSpace : MeasurableSpace Z2Gauge := ⊤

instance z2GaugeMeasurableSingleton : MeasurableSingletonClass Z2Gauge where
  measurableSet_singleton _ := by simp

/-- Explicit equivalence between the earlier Boolean local carrier and the
actual multiplicative group carrier. -/
def boolEquivZ2Gauge : Bool ≃ Z2Gauge where
  toFun b := if b then z2GaugeNontrivial else 1
  invFun g := decide (g ≠ 1)
  left_inv := by
    intro b
    cases b <;> simp [z2GaugeNontrivial]
  right_inv := by
    intro g
    rcases g with ⟨g⟩
    fin_cases g <;> norm_num [z2GaugeNontrivial]

/-- Transport a fixed-carrier Gram kernel along a finite equivalence. -/
def FiniteOSGramKernelOn.transport
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β)
    (K : FiniteOSGramKernelOn α) :
    FiniteOSGramKernelOn β :=
  { Feature := K.Feature
    kernel := fun x y => K.kernel (e.symm x) (e.symm y)
    coefficient := K.coefficient
    coefficient_nonneg := K.coefficient_nonneg
    feature := fun k x => K.feature k (e.symm x)
    kernel_decomposition := by
      intro x y
      exact K.kernel_decomposition (e.symm x) (e.symm y) }

@[simp]
theorem finite_os_gram_kernel_transport_apply
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β)
    (K : FiniteOSGramKernelOn α)
    (x y : β) :
    (K.transport e).kernel x y = K.kernel (e.symm x) (e.symm y) :=
  rfl

/-- Reflection positivity is invariant under finite relabelling of the carrier. -/
theorem finite_os_gram_kernel_transport_reflectionPositive
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β)
    (K : FiniteOSGramKernelOn α) :
    FiniteOSReflectionPositive (K.transport e).toCertificate :=
  finite_os_gram_certificate_reflectionPositive (K.transport e).toCertificate

/-- The explicit local Wilson Gram kernel on the actual two-element gauge
group. -/
def z2GaugeWilsonPlaquetteGramKernel
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteOSGramKernelOn Z2Gauge :=
  (z2WilsonPlaquetteGramKernel
    β energyIdentity energyNontrivial hβ hEnergy).transport boolEquivZ2Gauge

/-- The transported kernel depends only on whether its two gauge arguments
agree; this isolates the carrier relabelling from all later group reasoning. -/
theorem z2GaugeWilsonPlaquetteGramKernel_apply
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial)
    (x y : Z2Gauge) :
    (z2GaugeWilsonPlaquetteGramKernel
      β energyIdentity energyNontrivial hβ hEnergy).kernel x y =
      if x = y then
        z2WilsonWeightIdentity β energyIdentity
      else
        z2WilsonWeightNontrivial β energyNontrivial := by
  by_cases hxy : x = y
  · subst y
    simp [z2GaugeWilsonPlaquetteGramKernel,
      FiniteOSGramKernelOn.transport, z2WilsonPlaquetteGramKernel,
      z2PlaquetteGramKernel, z2PlaquetteKernel]
  · have hsymm :
        boolEquivZ2Gauge.symm x ≠ boolEquivZ2Gauge.symm y := by
      intro h
      exact hxy (boolEquivZ2Gauge.symm.injective h)
    simp [z2GaugeWilsonPlaquetteGramKernel,
      FiniteOSGramKernelOn.transport, z2WilsonPlaquetteGramKernel,
      z2PlaquetteGramKernel, z2PlaquetteKernel, hxy, hsymm]

/-- The local `Z2Gauge` Wilson kernel is OS reflection positive. -/
theorem z2GaugeWilson_singlePlaquette_reflectionPositive
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteOSReflectionPositive
      (z2GaugeWilsonPlaquetteGramKernel
        β energyIdentity energyNontrivial hβ hEnergy).toCertificate :=
  finite_os_gram_kernel_transport_reflectionPositive boolEquivZ2Gauge
    (z2WilsonPlaquetteGramKernel
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Construct an actual finite-lattice Wilson system with gauge group `Z₂`.
The lattice geometry remains arbitrary; only finiteness and the ordered
four-edge plaquette boundary are required. -/
def z2FiniteLatticeWilsonSystem
    (Vertex Edge Plaquette : Type)
    [Fintype Vertex] [Fintype Edge] [Fintype Plaquette]
    (source target : Edge → Vertex)
    (boundary : Plaquette → Fin 4 → Edge)
    (boundary_cycle_01 : ∀ p, target (boundary p 0) = source (boundary p 1))
    (boundary_cycle_12 : ∀ p, target (boundary p 1) = source (boundary p 2))
    (boundary_cycle_23 : ∀ p, target (boundary p 2) = source (boundary p 3))
    (boundary_cycle_30 : ∀ p, target (boundary p 3) = source (boundary p 0))
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial) :
    FiniteLatticeWilsonSystem :=
  { Gauge := Z2Gauge
    Vertex := Vertex
    Edge := Edge
    Plaquette := Plaquette
    source := source
    target := target
    boundary := boundary
    boundary_cycle_01 := boundary_cycle_01
    boundary_cycle_12 := boundary_cycle_12
    boundary_cycle_23 := boundary_cycle_23
    boundary_cycle_30 := boundary_cycle_30
    plaquetteEnergy := fun g =>
      if g = 1 then energyIdentity else energyNontrivial
    plaquetteEnergy_nonneg := by
      intro g
      split_ifs
      · exact hEnergyIdentity
      · exact hEnergyNontrivial
    plaquetteEnergy_conjInvariant := by
      intro h g
      have hconj : h * g * h⁻¹ = g := by
        rw [mul_comm h g, mul_assoc, mul_inv_cancel, mul_one]
      rw [hconj]
    beta := β
    beta_nonneg := hβ }

/-- The concrete system assigns the identity plaquette energy to the identity
group element. -/
@[simp]
theorem z2FiniteLatticeWilsonSystem_energy_identity
    (Vertex Edge Plaquette : Type)
    [Fintype Vertex] [Fintype Edge] [Fintype Plaquette]
    (source target : Edge → Vertex)
    (boundary : Plaquette → Fin 4 → Edge)
    (h01 : ∀ p, target (boundary p 0) = source (boundary p 1))
    (h12 : ∀ p, target (boundary p 1) = source (boundary p 2))
    (h23 : ∀ p, target (boundary p 2) = source (boundary p 3))
    (h30 : ∀ p, target (boundary p 3) = source (boundary p 0))
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hE0 : 0 ≤ energyIdentity) (hE1 : 0 ≤ energyNontrivial) :
    (z2FiniteLatticeWilsonSystem Vertex Edge Plaquette source target boundary
      h01 h12 h23 h30 β energyIdentity energyNontrivial hβ hE0 hE1)
      .plaquetteEnergy (1 : Z2Gauge) = energyIdentity := by
  simp [z2FiniteLatticeWilsonSystem]

/-- The concrete system assigns the nontrivial plaquette energy to the unique
nonidentity group element. -/
@[simp]
theorem z2FiniteLatticeWilsonSystem_energy_nontrivial
    (Vertex Edge Plaquette : Type)
    [Fintype Vertex] [Fintype Edge] [Fintype Plaquette]
    (source target : Edge → Vertex)
    (boundary : Plaquette → Fin 4 → Edge)
    (h01 : ∀ p, target (boundary p 0) = source (boundary p 1))
    (h12 : ∀ p, target (boundary p 1) = source (boundary p 2))
    (h23 : ∀ p, target (boundary p 2) = source (boundary p 3))
    (h30 : ∀ p, target (boundary p 3) = source (boundary p 0))
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hE0 : 0 ≤ energyIdentity) (hE1 : 0 ≤ energyNontrivial) :
    (z2FiniteLatticeWilsonSystem Vertex Edge Plaquette source target boundary
      h01 h12 h23 h30 β energyIdentity energyNontrivial hβ hE0 hE1)
      .plaquetteEnergy z2GaugeNontrivial = energyNontrivial := by
  simp [z2FiniteLatticeWilsonSystem, z2GaugeNontrivial]

/-- On the actual `Z₂` gauge carrier, the transported local kernel agrees with
the Boltzmann weight determined by the concrete plaquette energy. -/
theorem z2GaugeWilsonPlaquetteGramKernel_eq_boltzmann
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial)
    (x y : Z2Gauge) :
    (z2GaugeWilsonPlaquetteGramKernel
      β energyIdentity energyNontrivial hβ hEnergy).kernel x y =
      Real.exp (-β *
        (if x⁻¹ * y = 1 then energyIdentity else energyNontrivial)) := by
  rw [z2GaugeWilsonPlaquetteGramKernel_apply]
  by_cases hxy : x = y
  · subst y
    simp [z2WilsonWeightIdentity]
  · have hne : x⁻¹ * y ≠ 1 := by
      intro h
      have hleft := congrArg (fun z : Z2Gauge => x * z) h
      have hyx : y = x := by
        simpa [mul_assoc] using hleft
      exact hxy hyx.symm
    simp [hxy, hne, z2WilsonWeightNontrivial]

end

end MathlibAnalytic
end MGAP4D

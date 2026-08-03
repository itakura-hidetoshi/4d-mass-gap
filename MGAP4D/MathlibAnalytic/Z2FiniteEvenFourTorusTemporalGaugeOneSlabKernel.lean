import MGAP4D.MathlibAnalytic.FiniteOSGramKernelComap
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialSlice
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The local temporal-plaquette kernel attached to one spatial link.  In
temporal gauge the time-like links are one, so the plaquette holonomy is the
relative boundary link `A(e)⁻¹ B(e)`. -/
def finiteEvenFourTorusZ2TemporalLinkGramKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (e : FiniteEvenFourTorusSpatialLink H) :
    FiniteOSGramKernelOn
      (FiniteEvenFourTorusZ2SliceConfiguration H) :=
  (z2GaugeWilsonPlaquetteGramKernel
    β energyIdentity energyNontrivial hβ hEnergy).comap
      (fun A => A e)

@[simp] theorem finiteEvenFourTorusZ2TemporalLinkGramKernel_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (e : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2TemporalLinkGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy e).kernel A B =
      Real.exp (-β *
        (if (A e)⁻¹ * B e = 1 then
          energyIdentity
        else
          energyNontrivial)) := by
  exact z2GaugeWilsonPlaquetteGramKernel_eq_boltzmann
    β energyIdentity energyNontrivial hβ hEnergy (A e) (B e)

/-- Product of all temporal plaquette kernels in one geometric slab. -/
def finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteOSGramKernelOn
      (FiniteEvenFourTorusZ2SliceConfiguration H) :=
  FiniteOSGramKernelOn.listProduct
    (Finset.univ.toList.map fun e : FiniteEvenFourTorusSpatialLink H =>
      finiteEvenFourTorusZ2TemporalLinkGramKernel
        H β energyIdentity energyNontrivial hβ hEnergy e)

/-- Temporal Wilson action of the one-slab temporal-gauge configuration. -/
def finiteEvenFourTorusZ2TemporalGaugeCrossingAction
    (H : ℕ)
    (_β energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (Finset.univ.toList.map fun e : FiniteEvenFourTorusSpatialLink H =>
    if (A e)⁻¹ * B e = 1 then energyIdentity else energyNontrivial).sum

/-- The full crossing kernel is exactly the exponential of the temporal
one-slab Wilson action. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel A B =
      Real.exp (-β *
        finiteEvenFourTorusZ2TemporalGaugeCrossingAction
          H β energyIdentity energyNontrivial A B) := by
  unfold finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
  rw [finite_os_gram_kernel_listProduct_apply]
  simp only [List.map_map, Function.comp_apply]
  simp_rw [finiteEvenFourTorusZ2TemporalLinkGramKernel_apply]
  unfold finiteEvenFourTorusZ2TemporalGaugeCrossingAction
  let es := Finset.univ.toList
  change
    (es.map fun e : FiniteEvenFourTorusSpatialLink H =>
      Real.exp (-β *
        (if (A e)⁻¹ * B e = 1 then energyIdentity else energyNontrivial))).prod =
      Real.exp (-β *
        (es.map fun e : FiniteEvenFourTorusSpatialLink H =>
          if (A e)⁻¹ * B e = 1 then energyIdentity else energyNontrivial).sum)
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih, ← Real.exp_add]
      congr 1
      ring

/-- Symmetric temporal-gauge one-slab Wilson action: half the spatial action on
each boundary plus the complete temporal crossing action. -/
def finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (1 / 2 : ℝ) *
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A +
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction
      H β energyIdentity energyNontrivial A B +
    (1 / 2 : ℝ) *
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial B

/-- The actual temporal-gauge one-slab Wilson kernel, constructed as the
crossing Gram kernel sandwiched by the two spatial half-amplitudes. -/
def finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteOSGramKernelOn
      (FiniteEvenFourTorusZ2SliceConfiguration H) :=
  (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
    H β energyIdentity energyNontrivial hβ hEnergy).sandwich
      (finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial)

/-- Exact Boltzmann formula for the complete temporal-gauge one-slab kernel. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel A B =
      Real.exp (-β *
        finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
          H β energyIdentity energyNontrivial A B) := by
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
  rw [finite_os_gram_kernel_sandwich_apply,
    finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_eq_boltzmann]
  unfold finiteEvenFourTorusZ2SpatialHalfWeight
    finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The concrete one-slab kernel is strictly positive at every pair of boundary
configurations. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel A B := by
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann]
  exact Real.exp_pos _

/-- The actual one-slab kernel has a nonnegative finite Gram factorization. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlab_reflectionPositive
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteOSReflectionPositive
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        H β energyIdentity energyNontrivial hβ hEnergy).toCertificate :=
  finite_os_gram_certificate_reflectionPositive _

end

end MathlibAnalytic
end MGAP4D

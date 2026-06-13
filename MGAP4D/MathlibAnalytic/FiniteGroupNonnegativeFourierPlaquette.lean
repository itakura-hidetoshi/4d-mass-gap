import MGAP4D.MathlibAnalytic.FiniteGroupSinglePlaquetteOSKernel

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite real Fourier system normalized so that autocorrelation of a
synthesized function diagonalizes mode-by-mode.

For a genuine finite-group Fourier basis this identity is supplied by character
orthogonality.  Keeping it explicit separates the reusable square-root argument
from the later representation-theoretic instantiation. -/
structure FiniteRealFourierAutocorrelationSystem
    (G : Type) [Group G] [Fintype G] where
  Mode : Type
  [modeFintype : Fintype Mode]
  basis : Mode → G → ℝ
  autocorrelation_synthesis :
    ∀ (amplitude : Mode → ℝ) (g : G),
      finiteGroupAutocorrelation G
          (fun h => ∑ r : Mode, amplitude r * basis r h) g =
        ∑ r : Mode, (amplitude r) ^ 2 * basis r g

attribute [instance]
  FiniteRealFourierAutocorrelationSystem.modeFintype

/-- Nonnegative Fourier data for the single-plaquette Wilson Boltzmann weight. -/
structure FiniteGroupPlaquetteNonnegativeFourierExpansion
    (L : FiniteLatticeWilsonSystem) where
  fourier : FiniteRealFourierAutocorrelationSystem L.Gauge
  coefficient : fourier.Mode → ℝ
  coefficient_nonneg : ∀ r, 0 ≤ coefficient r
  weight_expansion :
    ∀ g : L.Gauge,
      Real.exp (-L.beta * L.plaquetteEnergy g) =
        ∑ r : fourier.Mode, coefficient r * fourier.basis r g

/-- Fourier square root obtained by taking the nonnegative square root of every
spectral coefficient. -/
def FiniteGroupPlaquetteNonnegativeFourierExpansion.squareRoot
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeFourierExpansion L) :
    L.Gauge → ℝ :=
  fun h =>
    ∑ r : E.fourier.Mode,
      Real.sqrt (E.coefficient r) * E.fourier.basis r h

/-- The autocorrelation of the Fourier square root reproduces the original
nonnegative Fourier expansion. -/
theorem finite_group_nonnegative_fourier_squareRoot_autocorrelation
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeFourierExpansion L)
    (g : L.Gauge) :
    finiteGroupAutocorrelation L.Gauge E.squareRoot g =
      ∑ r : E.fourier.Mode,
        E.coefficient r * E.fourier.basis r g := by
  rw [E.fourier.autocorrelation_synthesis]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Real.sq_sqrt (E.coefficient_nonneg r)]

/-- A nonnegative Fourier expansion supplies the convolution-square certificate
required by the finite-group single-plaquette OS theorem. -/
theorem finite_group_nonnegative_fourier_implies_convolutionSquare
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeFourierExpansion L) :
    HasFiniteGroupPlaquetteConvolutionSquare L := by
  refine ⟨E.squareRoot, ?_⟩
  intro g
  rw [finite_group_nonnegative_fourier_squareRoot_autocorrelation E g]
  exact E.weight_expansion g

/-- Direct single-plaquette OS positivity from nonnegative Fourier data. -/
theorem finite_group_nonnegative_fourier_singlePlaquette_reflectionPositive
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeFourierExpansion L) :
    FiniteOSReflectionPositive
      (finiteGroupSinglePlaquetteWilsonGramKernel L
        (finite_group_nonnegative_fourier_implies_convolutionSquare E))
        .toCertificate :=
  finite_group_single_plaquette_wilson_reflectionPositive L
    (finite_group_nonnegative_fourier_implies_convolutionSquare E)

/-- A finite collection of crossing plaquettes carrying the same nonnegative
Fourier expansion produces a reflection-positive crossing kernel. -/
theorem finite_group_nonnegative_fourier_crossing_list_reflectionPositive
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeFourierExpansion L)
    (n : ℕ) :
    FiniteOSReflectionPositive
      (FiniteOSGramKernelOn.listProduct
        (List.replicate n
          (finiteGroupSinglePlaquetteWilsonGramKernel L
            (finite_group_nonnegative_fourier_implies_convolutionSquare E))))
        .toCertificate :=
  finite_os_gram_kernel_listProduct_reflectionPositive _

/-- Same-side action factors can be absorbed after the Fourier construction. -/
theorem finite_group_nonnegative_fourier_full_crossing_reflectionPositive
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeFourierExpansion L)
    (n : ℕ) (a : L.Gauge → ℝ) :
    FiniteOSReflectionPositive
      ((FiniteOSGramKernelOn.listProduct
        (List.replicate n
          (finiteGroupSinglePlaquetteWilsonGramKernel L
            (finite_group_nonnegative_fourier_implies_convolutionSquare E))))
        .sandwich a).toCertificate :=
  finite_os_crossing_product_with_halfspace_factor_reflectionPositive _ a

/-- Audit-visible local implication chain for one finite-group plaquette. -/
structure FiniteGroupPlaquetteOSFourierCertificate
    (L : FiniteLatticeWilsonSystem) where
  expansion : FiniteGroupPlaquetteNonnegativeFourierExpansion L
  convolutionSquare : HasFiniteGroupPlaquetteConvolutionSquare L
  reflectionPositive :
    FiniteOSReflectionPositive
      (finiteGroupSinglePlaquetteWilsonGramKernel L convolutionSquare)
        .toCertificate

/-- Build the complete local OS certificate from nonnegative Fourier data. -/
def finiteGroupPlaquetteOSFourierCertificate
    (L : FiniteLatticeWilsonSystem)
    (E : FiniteGroupPlaquetteNonnegativeFourierExpansion L) :
    FiniteGroupPlaquetteOSFourierCertificate L :=
  { expansion := E
    convolutionSquare :=
      finite_group_nonnegative_fourier_implies_convolutionSquare E
    reflectionPositive :=
      finite_group_nonnegative_fourier_singlePlaquette_reflectionPositive E }

end

end MathlibAnalytic
end MGAP4D

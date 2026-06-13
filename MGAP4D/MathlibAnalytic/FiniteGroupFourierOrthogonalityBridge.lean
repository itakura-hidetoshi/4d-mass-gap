import MGAP4D.MathlibAnalytic.FiniteGroupNonnegativeFourierPlaquette

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite real Fourier family stated through the translated orthogonality
relation actually used by the OS argument.

For genuine characters this is the finite-group character orthogonality law,
with the basis normalized so that no additional group-cardinality factor
appears. -/
structure FiniteRealFourierOrthogonalitySystem
    (G : Type) [Group G] [Fintype G] where
  Mode : Type
  [modeFintype : Fintype Mode]
  basis : Mode → G → ℝ
  translated_orthogonality :
    ∀ (r s : Mode) (g : G),
      (∑ h : G, basis r h * basis s (h * g)) =
        if r = s then basis r g else 0

attribute [instance]
  FiniteRealFourierOrthogonalitySystem.modeFintype

/-- Expanding both synthesized factors and applying translated character
orthogonality yields the diagonal autocorrelation formula. -/
theorem finite_real_fourier_autocorrelation_synthesis_of_orthogonality
    (G : Type) [Group G] [Fintype G]
    (O : FiniteRealFourierOrthogonalitySystem G)
    (amplitude : O.Mode → ℝ) (g : G) :
    finiteGroupAutocorrelation G
        (fun h => ∑ r : O.Mode, amplitude r * O.basis r h) g =
      ∑ r : O.Mode, (amplitude r) ^ 2 * O.basis r g := by
  classical
  unfold finiteGroupAutocorrelation
  calc
    (∑ h : G,
      (∑ r : O.Mode, amplitude r * O.basis r h) *
        (∑ s : O.Mode, amplitude s * O.basis s (h * g))) =
        ∑ h : G, ∑ r : O.Mode, ∑ s : O.Mode,
          (amplitude r * O.basis r h) *
            (amplitude s * O.basis s (h * g)) := by
              apply Finset.sum_congr rfl
              intro h _hh
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro r _hr
              rw [Finset.mul_sum]
    _ = ∑ r : O.Mode, ∑ s : O.Mode, ∑ h : G,
          (amplitude r * O.basis r h) *
            (amplitude s * O.basis s (h * g)) := by
              rw [Fintype.sum_comm]
              apply Finset.sum_congr rfl
              intro r _hr
              rw [Fintype.sum_comm]
    _ = ∑ r : O.Mode, ∑ s : O.Mode,
          (amplitude r * amplitude s) *
            (∑ h : G, O.basis r h * O.basis s (h * g)) := by
              apply Finset.sum_congr rfl
              intro r _hr
              apply Finset.sum_congr rfl
              intro s _hs
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro h _hh
              ring
    _ = ∑ r : O.Mode, ∑ s : O.Mode,
          (amplitude r * amplitude s) *
            (if r = s then O.basis r g else 0) := by
              simp_rw [O.translated_orthogonality]
    _ = ∑ r : O.Mode, (amplitude r) ^ 2 * O.basis r g := by
              simp [pow_two]

/-- Every translated-orthogonality system canonically supplies the synthesis
system used by the nonnegative-Fourier square-root theorem. -/
def FiniteRealFourierOrthogonalitySystem.toAutocorrelationSystem
    (G : Type) [Group G] [Fintype G]
    (O : FiniteRealFourierOrthogonalitySystem G) :
    FiniteRealFourierAutocorrelationSystem G :=
  { Mode := O.Mode
    basis := O.basis
    autocorrelation_synthesis :=
      finite_real_fourier_autocorrelation_synthesis_of_orthogonality G O }

/-- Nonnegative Fourier coefficients relative to an orthogonality system. -/
structure FiniteGroupPlaquetteNonnegativeOrthogonalFourierExpansion
    (L : FiniteLatticeWilsonSystem) where
  orthogonality : FiniteRealFourierOrthogonalitySystem L.Gauge
  coefficient : orthogonality.Mode → ℝ
  coefficient_nonneg : ∀ r, 0 ≤ coefficient r
  weight_expansion :
    ∀ g : L.Gauge,
      Real.exp (-L.beta * L.plaquetteEnergy g) =
        ∑ r : orthogonality.Mode,
          coefficient r * orthogonality.basis r g

/-- Convert orthogonality-based data into the previous synthesis-based Fourier
expansion without adding a new mathematical assumption. -/
def FiniteGroupPlaquetteNonnegativeOrthogonalFourierExpansion.toFourierExpansion
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeOrthogonalFourierExpansion L) :
    FiniteGroupPlaquetteNonnegativeFourierExpansion L :=
  { fourier := E.orthogonality.toAutocorrelationSystem L.Gauge
    coefficient := E.coefficient
    coefficient_nonneg := E.coefficient_nonneg
    weight_expansion := E.weight_expansion }

/-- Character orthogonality plus nonnegative Fourier coefficients produces the
single-plaquette convolution square. -/
theorem finite_group_orthogonal_fourier_implies_convolutionSquare
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeOrthogonalFourierExpansion L) :
    HasFiniteGroupPlaquetteConvolutionSquare L :=
  finite_group_nonnegative_fourier_implies_convolutionSquare
    E.toFourierExpansion

/-- Direct finite-group single-plaquette OS positivity from character
orthogonality and nonnegative Fourier coefficients. -/
theorem finite_group_orthogonal_fourier_singlePlaquette_reflectionPositive
    {L : FiniteLatticeWilsonSystem}
    (E : FiniteGroupPlaquetteNonnegativeOrthogonalFourierExpansion L) :
    FiniteOSReflectionPositive
      (finiteGroupSinglePlaquetteWilsonGramKernel L
        (finite_group_orthogonal_fourier_implies_convolutionSquare E))
        .toCertificate :=
  finite_group_single_plaquette_wilson_reflectionPositive L
    (finite_group_orthogonal_fourier_implies_convolutionSquare E)

/-- Audit-visible implication chain with character orthogonality as the only
Fourier-analytic structural input. -/
structure FiniteGroupPlaquetteOSOrthogonalFourierCertificate
    (L : FiniteLatticeWilsonSystem) where
  expansion : FiniteGroupPlaquetteNonnegativeOrthogonalFourierExpansion L
  convolutionSquare : HasFiniteGroupPlaquetteConvolutionSquare L
  reflectionPositive :
    FiniteOSReflectionPositive
      (finiteGroupSinglePlaquetteWilsonGramKernel L convolutionSquare)
        .toCertificate

/-- Build the local OS certificate directly from orthogonal Fourier data. -/
def finiteGroupPlaquetteOSOrthogonalFourierCertificate
    (L : FiniteLatticeWilsonSystem)
    (E : FiniteGroupPlaquetteNonnegativeOrthogonalFourierExpansion L) :
    FiniteGroupPlaquetteOSOrthogonalFourierCertificate L :=
  { expansion := E
    convolutionSquare :=
      finite_group_orthogonal_fourier_implies_convolutionSquare E
    reflectionPositive :=
      finite_group_orthogonal_fourier_singlePlaquette_reflectionPositive E }

end

end MathlibAnalytic
end MGAP4D

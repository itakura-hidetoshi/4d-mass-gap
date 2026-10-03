import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonEnergySUNHaarTwoMode
import Mathlib.Tactic

/-!
# The arbitrary-rank Wilson two-mode Gram--Schmidt family has the seed span

The canonical two-mode family is obtained by Gram--Schmidt normalization from
the literal Wilson-energy seed pair `1, E_W`.

For the H1-D5 crossing strictness argument the concrete coefficients of that
orthonormalization are irrelevant.  Mathlib's Gram--Schmidt span theorems show
directly that the theorem-generated orthonormal pair and the literal seed pair
generate exactly the same real submodule.

This lets later arguments prove strictness on the transparent `1, E_W`
carrier and transport it to the existing two-mode basis without computing a
change-of-basis matrix.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The SU(N) Wilson two-mode Gram--Schmidt family spans exactly the same
submodule as the literal constant-one / Wilson-energy seed pair. -/
theorem specialUnitaryWilsonHaarTwoMode_span_eq_seed
    {N : ℕ}
    (hN2 : 2 ≤ N) :
    Submodule.span ℝ
        (Set.range (specialUnitaryWilsonHaarTwoMode hN2)) =
      Submodule.span ℝ
        (Set.range
          (specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed
            (lt_of_lt_of_le (by norm_num) hN2))) := by
  let hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN2
  let seed : Fin 2 → SpecialUnitaryNormalizedHaarL2 N :=
    specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed hNpos
  change
    Submodule.span ℝ
        (Set.range (InnerProductSpace.gramSchmidtNormed ℝ seed)) =
      Submodule.span ℝ (Set.range seed)
  rw [InnerProductSpace.span_gramSchmidtNormed_range,
    InnerProductSpace.span_gramSchmidt]

/-- Each theorem-generated two-mode vector belongs to the literal seed span. -/
theorem specialUnitaryWilsonHaarTwoMode_mem_seed_span
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    specialUnitaryWilsonHaarTwoMode hN2 k ∈
      Submodule.span ℝ
        (Set.range
          (specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed
            (lt_of_lt_of_le (by norm_num) hN2))) := by
  rw [← specialUnitaryWilsonHaarTwoMode_span_eq_seed hN2]
  exact Submodule.subset_span (Set.mem_range_self k)

/-- Conversely each literal seed vector belongs to the theorem-generated
orthonormal two-mode span. -/
theorem specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed_mem_twoMode_span
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed
        (lt_of_lt_of_le (by norm_num) hN2) k ∈
      Submodule.span ℝ
        (Set.range (specialUnitaryWilsonHaarTwoMode hN2)) := by
  rw [specialUnitaryWilsonHaarTwoMode_span_eq_seed hN2]
  exact Submodule.subset_span (Set.mem_range_self k)

end

end MathlibAnalytic
end MGAP4D

import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalTotalVariationContraction
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanScale

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Iterate the concrete finite Wilson random-scan heat-bath sweep. -/
def FiniteLatticeWilsonSystem.randomScanHeatBathIterate
    (L : FiniteLatticeWilsonSystem) :
    ℕ → (L.Configuration → ℝ) → (L.Configuration → ℝ)
  | 0, f => f
  | n + 1, f =>
      L.randomScanHeatBathSweep (L.randomScanHeatBathIterate n f)

@[simp] theorem finite_lattice_randomScanHeatBathIterate_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.randomScanHeatBathIterate 0 f = f :=
  rfl

@[simp] theorem finite_lattice_randomScanHeatBathIterate_succ
    (L : FiniteLatticeWilsonSystem)
    (n : ℕ)
    (f : L.Configuration → ℝ) :
    L.randomScanHeatBathIterate (n + 1) f =
      L.randomScanHeatBathSweep (L.randomScanHeatBathIterate n f) :=
  rfl

/-- Canonical total variation decays geometrically along every finite
random-scan heat-bath trajectory. -/
theorem finite_lattice_randomScanHeatBathIterate_canonicalTotalVariation_le_pow_mul
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (n : ℕ) :
    L.canonicalTotalVariation (L.randomScanHeatBathIterate n f) ≤
      (finiteLatticeWilsonDobrushinRandomScanRate L D) ^ n *
        L.canonicalTotalVariation f := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hRateNonneg :
          0 ≤ finiteLatticeWilsonDobrushinRandomScanRate L D :=
        finite_lattice_dobrushinRandomScanRate_nonneg L D hEdge
      calc
        L.canonicalTotalVariation
            (L.randomScanHeatBathIterate (n + 1) f) =
          L.canonicalTotalVariation
            (L.randomScanHeatBathSweep
              (L.randomScanHeatBathIterate n f)) := rfl
        _ ≤ finiteLatticeWilsonDobrushinRandomScanRate L D *
            L.canonicalTotalVariation
              (L.randomScanHeatBathIterate n f) :=
          finite_lattice_randomScanHeatBathSweep_canonicalTotalVariation_le_rate_mul
            L (L.randomScanHeatBathIterate n f) D hEdge
        _ ≤ finiteLatticeWilsonDobrushinRandomScanRate L D *
            ((finiteLatticeWilsonDobrushinRandomScanRate L D) ^ n *
              L.canonicalTotalVariation f) :=
          mul_le_mul_of_nonneg_left ih hRateNonneg
        _ = (finiteLatticeWilsonDobrushinRandomScanRate L D) ^ (n + 1) *
            L.canonicalTotalVariation f := by
          rw [pow_succ]
          ring

end

end MathlibAnalytic
end MGAP4D

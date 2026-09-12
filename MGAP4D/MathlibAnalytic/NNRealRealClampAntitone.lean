import MGAP4D.MathlibAnalytic.NNRealContinuousRealClampMidpointExtension

/-!
# Antitonicity of real clamp extensions

The canonical clamp `Real.toNNReal : ℝ → NNReal` is monotone.  Therefore an
antitone function on `NNReal` remains antitone after extending it to all real
arguments by clamping negative inputs to zero.

This elementary order bridge is independent of the physical OS layer.
-/

namespace MGAP4D

/-- Antitonicity is preserved by the canonical real clamp extension. -/
theorem nnrealRealClampExtension_antitone
    (f : NNReal → ℝ) (hf : Antitone f) :
    Antitone (nnrealRealClampExtension f) := by
  intro s t hst
  exact hf (Real.toNNReal_mono hst)

end MGAP4D

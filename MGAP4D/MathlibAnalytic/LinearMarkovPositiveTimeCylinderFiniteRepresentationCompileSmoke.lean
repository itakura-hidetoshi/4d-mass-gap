import MGAP4D.MathlibAnalytic.LinearMarkovPositiveTimeCylinderFiniteRepresentation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example {Ω : Type*}
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    ∃ n : ℕ, ∃ H : LinearMarkovPositiveTimeFuturePath Ω n → ℝ,
      (F : (ℕ → Ω) → ℝ) =
        H ∘ linearMarkovPositiveTimeFuturePrefix n :=
  linearMarkovPositiveTimeCylinder_finiteRepresentable F

end

end MathlibAnalytic
end MGAP4D

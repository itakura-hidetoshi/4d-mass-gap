import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveObservableDescent
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerTietzeReadout

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v w

variable {Edge : Type} [Fintype Edge]

/-- Any observable obtained by reading only the selected positive open half is
negative-half independent in the exact boundary-fibered coordinates. -/
theorem negativeHalfIndependent_comp_positiveRestriction
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} {Target : Type w}
    (g : P.OpenHalfConfiguration Value → Target) :
    P.NegativeHalfIndependent (fun A => g (P.positiveRestriction A)) := by
  intro b x y₁ y₂
  simp

end FiniteInvolutiveEdgeOrbitPartition

private theorem normalizedTracePowerBoundaryPositiveOSTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerBoundaryPositiveOSNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerBoundaryPositiveOSTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerBoundaryPositiveOSCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerBoundaryPositiveOSSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerBoundaryPositiveOSMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerBoundaryPositiveOSBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerBoundaryPositiveOSSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

/-- The existing full finite normalized-trace-power target reads only the
positive open-half restriction, hence is automatically negative-half
independent. -/
theorem normalizedTracePowerTietzeFullTarget_negativeHalfIndependent
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (n j : ℕ) :
    (periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).NegativeHalfIndependent
      (fun A => normalizedTracePowerTietzeFullTarget
        halfExtent beta hbeta n j A) := by
  exact
    FiniteInvolutiveEdgeOrbitPartition.negativeHalfIndependent_comp_positiveRestriction
      (periodicHypercubicEvenEdgeOrbitPartition (halfExtent n))
      (fun x =>
        periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j x)

/-- Every existing SU(2) normalized-trace-power full target therefore satisfies
the actual finite even-periodic Wilson Gibbs Osterwalder--Schrader inequality.
The proof contains no separate reflection-positivity or locality premise. -/
theorem normalizedTracePowerTietzeFullTarget_wilsonGibbs_reflectionPositive
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (n j : ℕ) :
    0 ≤ ∫ A,
      normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A *
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        2 normalizedTracePowerBoundaryPositiveOSTwoRankPositive
        (beta n) (hbeta n)).gibbsMeasure := by
  exact
    periodicHypercubicEvenWilsonGibbs_reflectionPositive_of_negativeHalfIndependent
      (halfExtent n) 2 normalizedTracePowerBoundaryPositiveOSTwoRankPositive
      (beta n) (hbeta n)
      (normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j)
      (normalizedTracePowerTietzeFullTarget_negativeHalfIndependent
        halfExtent beta hbeta n j)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D

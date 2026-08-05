import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedTemporalCrossingMixedAction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialIncidenceBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Membership in the temporal-target crossing-link set is exactly the
outgoing-or-incoming endpoint alternative. -/
theorem finiteEvenFourTorusZ2_mem_temporalTargetCrossingLinks_iff_endpoint
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    e ∈ finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target ↔
      target = e.1 ∨
        target = finiteEvenFourTorusSpatialVertexStep H e.1 e.2 := by
  rw [finiteEvenFourTorusZ2_mem_temporalTargetCrossingLinks]
  simp [finiteEvenFourTorusZ2AugmentedCrossingLinkSupport]

/-- A target-incident temporal crossing link, retained as a subtype so that
periodic coincidences in the smallest volume do not need to be excluded. -/
abbrev FiniteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrence
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialVertex H) : Type :=
  ↥(finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target)

/-- Code a target-incident crossing link by outgoing/incoming side and spatial
direction.  If a periodic link is simultaneously outgoing and incoming, the
outgoing code is chosen. -/
def finiteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrenceCode
    {H : ℕ}
    {target : FiniteEvenFourTorusSpatialVertex H}
    (o : FiniteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrence H target) :
    Bool × FiniteEvenFourTorusSpatialDirection :=
  (if o.1.1 = target then false else true, o.1.2)

/-- The outgoing/incoming-direction code is injective.  Incoming bases are
recovered using injectivity of translation in the fixed spatial direction. -/
theorem finiteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrenceCode_injective
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialVertex H) :
    Function.Injective
      (finiteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrenceCode
        (H := H) (target := target)) := by
  rintro ⟨e, he⟩ ⟨f, hf⟩ hCode
  apply Subtype.ext
  have hDirection : e.2 = f.2 :=
    congrArg
      (fun p : Bool × FiniteEvenFourTorusSpatialDirection => p.2)
      hCode
  have hSide :
      (if e.1 = target then false else true) =
        (if f.1 = target then false else true) :=
    congrArg
      (fun p : Bool × FiniteEvenFourTorusSpatialDirection => p.1)
      hCode
  by_cases heTail : e.1 = target
  · by_cases hfTail : f.1 = target
    · exact Prod.ext (heTail.trans hfTail.symm) hDirection
    · simp [heTail, hfTail] at hSide
  · by_cases hfTail : f.1 = target
    · simp [heTail, hfTail] at hSide
    · have heEndpoint :=
        (finiteEvenFourTorusZ2_mem_temporalTargetCrossingLinks_iff_endpoint
          H target e).1 he
      have hfEndpoint :=
        (finiteEvenFourTorusZ2_mem_temporalTargetCrossingLinks_iff_endpoint
          H target f).1 hf
      have heHead :
          target = finiteEvenFourTorusSpatialVertexStep H e.1 e.2 :=
        heEndpoint.resolve_left (fun h => heTail h.symm)
      have hfHead :
          target = finiteEvenFourTorusSpatialVertexStep H f.1 f.2 :=
        hfEndpoint.resolve_left (fun h => hfTail h.symm)
      have hStepRaw :
          finiteEvenFourTorusSpatialVertexStep H e.1 e.2 =
            finiteEvenFourTorusSpatialVertexStep H f.1 f.2 :=
        heHead.symm.trans hfHead
      have hStep :
          finiteEvenFourTorusSpatialVertexStep H e.1 e.2 =
            finiteEvenFourTorusSpatialVertexStep H f.1 e.2 := by
        simpa [hDirection] using hStepRaw
      have hBase : e.1 = f.1 :=
        finiteEvenFourTorusSpatialVertexStep_injective H e.2 hStep
      exact Prod.ext hBase hDirection

/-- Every temporal vertex is incident to at most six crossing links: three
outgoing and three incoming.  The bound is valid in every odd side length,
including the modulus-two member where the two classes may overlap. -/
theorem finiteEvenFourTorusZ2TemporalTargetCrossingLinks_card_le_six
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialVertex H) :
    (finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target).card ≤ 6 := by
  calc
    (finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target).card =
        Fintype.card
          (FiniteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrence H target) := by
      simp [FiniteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrence]
    _ ≤ Fintype.card (Bool × FiniteEvenFourTorusSpatialDirection) :=
      Fintype.card_le_of_injective
        (finiteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrenceCode
          (H := H) (target := target))
        (finiteEvenFourTorusZ2TemporalTargetCrossingLinkOccurrenceCode_injective
          H target)
    _ = 6 := by
      simp

end

end MathlibAnalytic
end MGAP4D

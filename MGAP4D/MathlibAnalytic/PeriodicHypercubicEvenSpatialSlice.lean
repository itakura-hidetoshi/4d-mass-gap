import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFixedTimeClassification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Vertices of the canonical time-zero spatial slice in the modern even-periodic
hypercubic geometry.  This is the primary reflection-fixed plane. -/
abbrev PeriodicHypercubicEvenSpatialSliceVertex (H : ℕ) : Type :=
  {v : PeriodicHypercubicEvenVertex H //
    periodicHypercubicEvenOnPrimaryReflectionPlane H v}

/-- The three non-time coordinate directions. -/
abbrev PeriodicHypercubicEvenSpatialDirection : Type :=
  {mu : PeriodicHypercubicAxis // mu ≠ 0}

/-- A positively oriented spatial link based on the canonical time-zero slice. -/
abbrev PeriodicHypercubicEvenSpatialSliceLink (H : ℕ) : Type :=
  PeriodicHypercubicEvenSpatialSliceVertex H ×
    PeriodicHypercubicEvenSpatialDirection

/-- Gauge-valued configurations on one canonical spatial time slice. -/
abbrev PeriodicHypercubicEvenSpatialSliceConfiguration
    (H : ℕ) (Gauge : Type) : Type :=
  PeriodicHypercubicEvenSpatialSliceLink H → Gauge

/-- A spatial unit shift preserves the canonical time-zero slice. -/
def periodicHypercubicEvenSpatialSliceShift
    (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu : PeriodicHypercubicEvenSpatialDirection) :
    PeriodicHypercubicEvenSpatialSliceVertex H :=
  ⟨periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v.1 mu.1, by
    have h0mu : (0 : PeriodicHypercubicAxis) ≠ mu.1 := Ne.symm mu.2
    simpa [periodicHypercubicEvenOnPrimaryReflectionPlane,
      periodicHypercubicShift_apply, h0mu] using v.2⟩

@[simp] theorem periodicHypercubicEvenSpatialSliceShift_coe
    (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu : PeriodicHypercubicEvenSpatialDirection) :
    (periodicHypercubicEvenSpatialSliceShift H v mu).1 =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v.1 mu.1 :=
  rfl

/-- Embed a canonical spatial-slice link into the actual four-dimensional
physical positive-link carrier. -/
def periodicHypercubicEvenSpatialSliceLinkEmbedding
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenEdge H :=
  (e.1.1, e.2.1)

@[simp] theorem periodicHypercubicEvenSpatialSliceLinkEmbedding_source
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEdgeSource (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) = e.1.1 :=
  rfl

@[simp] theorem periodicHypercubicEvenSpatialSliceLinkEmbedding_target
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEdgeTarget (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) =
      (periodicHypercubicEvenSpatialSliceShift H e.1 e.2).1 :=
  rfl

/-- The spatial-slice link embedding loses no link information. -/
theorem periodicHypercubicEvenSpatialSliceLinkEmbedding_injective
    (H : ℕ) :
    Function.Injective (periodicHypercubicEvenSpatialSliceLinkEmbedding H) := by
  intro e f h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst h
  · apply Subtype.ext
    exact congrArg Prod.snd h

/-- Restrict a full four-dimensional link configuration to the canonical
spatial slice. -/
def periodicHypercubicEvenSpatialSliceRestriction
    {H : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge :=
  fun e => A (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)

@[simp] theorem periodicHypercubicEvenSpatialSliceRestriction_apply
    {H : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSliceRestriction A e =
      A (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) :=
  rfl

/-- Ordered pairs of distinct spatial coordinate directions.  The inherited
strict order chooses each spatial coordinate plane exactly once. -/
abbrev PeriodicHypercubicEvenSpatialDirectionPair : Type :=
  {pair : PeriodicHypercubicEvenSpatialDirection ×
      PeriodicHypercubicEvenSpatialDirection // pair.1.1 < pair.2.1}

/-- Spatial plaquettes based on the canonical time-zero slice. -/
abbrev PeriodicHypercubicEvenSpatialSlicePlaquette (H : ℕ) : Type :=
  PeriodicHypercubicEvenSpatialSliceVertex H ×
    PeriodicHypercubicEvenSpatialDirectionPair

/-- Embed a spatial-slice plaquette into the modern four-dimensional periodic
plaquette carrier. -/
def periodicHypercubicEvenSpatialSlicePlaquetteEmbedding
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    PeriodicHypercubicEvenPlaquette H :=
  (p.1.1, ⟨(p.2.1.1.1, p.2.1.2.1), p.2.2⟩)

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_firstAxis
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicPlaquetteFirstAxis
        (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) =
      p.2.1.1.1 :=
  rfl

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_secondAxis
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicPlaquetteSecondAxis
        (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) =
      p.2.1.2.1 :=
  rfl

/-- The spatial-slice plaquette embedding loses no plaquette information. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_injective
    (H : ℕ) :
    Function.Injective (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst h
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z => periodicHypercubicPlaquetteFirstAxis z) h
    · apply Subtype.ext
      exact congrArg (fun z => periodicHypercubicPlaquetteSecondAxis z) h

/-- Embedded spatial-slice plaquettes contain no Euclidean-time direction. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_not_hasTimeDirection
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    ¬ periodicHypercubicEvenPlaquetteHasTimeDirection
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) := by
  intro htime
  rcases htime with htime | htime
  · exact p.2.1.1.2 htime
  · exact p.2.1.2.2 htime

/-- The base of every embedded spatial-slice plaquette lies on the primary
reflection plane. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_onPrimary
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenOnPrimaryReflectionPlane H
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p).1 :=
  p.1.2

/-- Hence every canonical spatial-slice plaquette is one of the existing
spatial crossing plaquettes on the primary reflection plane.  This is the
bridge from the new adjacent-slice carrier to the already formalized Wilson
crossing-kernel geometry. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_isSpatialCrossing
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpatialCrossingPlaquette
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) := by
  rw [periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane]
  exact ⟨
    periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_not_hasTimeDirection H p,
    Or.inl
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_onPrimary H p)⟩

/-- Intrinsic plaquette holonomy of a gauge-valued spatial-slice configuration. -/
def periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) : Gauge :=
  let v := p.1
  let mu := p.2.1.1
  let nu := p.2.1.2
  A (v, mu) *
    A (periodicHypercubicEvenSpatialSliceShift H v mu, nu) *
    (A (periodicHypercubicEvenSpatialSliceShift H v nu, mu))⁻¹ *
    (A (v, nu))⁻¹

/-- Restriction from the full four-dimensional configuration reproduces exactly
the full Wilson plaquette holonomy on every embedded spatial-slice plaquette. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_restriction_eq
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (periodicHypercubicEvenSpatialSliceRestriction A) p =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) := by
  rfl

end

end MathlibAnalytic
end MGAP4D

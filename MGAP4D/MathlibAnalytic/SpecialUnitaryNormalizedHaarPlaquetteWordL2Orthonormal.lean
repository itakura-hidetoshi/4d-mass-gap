import MGAP4D.MathlibAnalytic.HaarPlaquetteWordL2Orthonormal
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSingleHaarCoordinateBoundaryOrthonormal

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance plaquetteHaarTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance plaquetteHaarCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance plaquetteHaarSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance plaquetteHaarMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance plaquetteHaarBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Real `L²` of four independent normalized-Haar `SU(N)` edge variables,
grouped as two oriented pairs for one plaquette. -/
abbrev SpecialUnitaryNormalizedHaarPlaquetteEdgeL2 (N : ℕ) :=
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  Lp ℝ 2 ((μ.prod μ).prod (μ.prod μ))

/-- Exact `L²` pullback of a normalized-Haar `SU(N)` holonomy mode along the
oriented plaquette word `a * b * c⁻¹ * d⁻¹`. -/
noncomputable def specialUnitaryNormalizedHaarPlaquetteWordL2Pullback
    (N : ℕ) :
    SpecialUnitaryNormalizedHaarL2 N →ₗᵢ[ℝ]
      SpecialUnitaryNormalizedHaarPlaquetteEdgeL2 N :=
  haarPlaquetteWordL2Pullback
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- Any orthonormal family of normalized-Haar `SU(N)` holonomy modes remains
orthonormal on four independent Haar edge variables after plaquette-word
pullback.  In the next geometric layer these four variables are identified
with the four distinct fixed edges of a time-zero spatial plaquette. -/
theorem specialUnitaryNormalizedHaarPlaquetteWordL2Pullback_orthonormal
    (N : ℕ)
    {κ : Type*}
    (v : κ → SpecialUnitaryNormalizedHaarL2 N)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((specialUnitaryNormalizedHaarPlaquetteWordL2Pullback N) ∘ v) :=
  haarPlaquetteWordL2Pullback_orthonormal
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) v hv

end

end MathlibAnalytic
end MGAP4D

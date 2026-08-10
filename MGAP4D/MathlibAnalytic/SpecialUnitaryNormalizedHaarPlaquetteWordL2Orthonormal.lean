import MGAP4D.MathlibAnalytic.HaarPlaquetteWordL2Orthonormal
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSingleHaarCoordinateBoundaryOrthonormal

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open MeasureTheory.Measure

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

/-- The repository's normalized compact Haar measure is left invariant by
construction: it is Mathlib's normalized `Measure.haarMeasure` on the whole
compact group. -/
local instance plaquetteHaarLeftInvariant (N : ℕ) :
    IsMulLeftInvariant
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  unfold normalizedCompactHaar
  infer_instance

/-- Real `L²` of four independent normalized-Haar `SU(N)` edge variables in
the nested cyclic order `(((b,a),d),c)`.

This order is chosen so the cyclic plaquette word is
`c⁻¹ * d⁻¹ * a * b`, which is conjugate to the physical oriented holonomy
`a * b * c⁻¹ * d⁻¹`. -/
abbrev SpecialUnitaryNormalizedHaarCyclicPlaquetteEdgeL2 (N : ℕ) :=
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  Lp ℝ 2 (((μ.prod μ).prod μ).prod μ)

/-- Exact `L²` pullback of a normalized-Haar `SU(N)` mode along the cyclic
plaquette word `c⁻¹ * d⁻¹ * a * b`.

Only left Haar invariance is used.  No compact-group unimodularity or
inversion-invariance receipt is needed.  For the class functions used by
Wilson observables, this cyclic word has exactly the same value as the actual
oriented plaquette holonomy because the two group elements are conjugate. -/
noncomputable def specialUnitaryNormalizedHaarCyclicPlaquetteWordL2Pullback
    (N : ℕ) :
    SpecialUnitaryNormalizedHaarL2 N →ₗᵢ[ℝ]
      SpecialUnitaryNormalizedHaarCyclicPlaquetteEdgeL2 N :=
  haarCyclicPlaquetteWordL2Pullback
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- Any orthonormal family of normalized-Haar `SU(N)` holonomy modes remains
orthonormal on four independent Haar edge variables after cyclic
plaquette-word pullback.  The next geometric layer identifies these four
variables with the four distinct reflection-fixed edges of a canonical
time-zero spatial plaquette. -/
theorem specialUnitaryNormalizedHaarCyclicPlaquetteWordL2Pullback_orthonormal
    (N : ℕ)
    {κ : Type*}
    (v : κ → SpecialUnitaryNormalizedHaarL2 N)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((specialUnitaryNormalizedHaarCyclicPlaquetteWordL2Pullback N) ∘ v) :=
  haarCyclicPlaquetteWordL2Pullback_orthonormal
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) v hv

end

end MathlibAnalytic
end MGAP4D

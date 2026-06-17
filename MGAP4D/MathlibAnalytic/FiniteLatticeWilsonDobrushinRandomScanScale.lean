import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinMatrix
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanRayleighContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The continuous-time heat-bath coercivity constant suggested by a strict
Dobrushin coefficient.  This quantity is dimensionless and belongs to the
Markov/heat-bath layer, not to the normalized physical-gap layer. -/
def finiteLatticeWilsonDobrushinHeatBathGap
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L) : ℝ :=
  1 - D.dobrushinCoefficient

/-- The standard normalized random-scan rate corresponding to a Dobrushin
coefficient `alpha`: `rho = 1 - (1 - alpha) / |E|`. -/
def finiteLatticeWilsonDobrushinRandomScanRate
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L) : ℝ :=
  1 - finiteLatticeWilsonDobrushinHeatBathGap D /
    (Fintype.card L.Edge : ℝ)

/-- Strict Dobrushin uniqueness gives a positive heat-bath gap `1 - alpha`. -/
theorem finite_lattice_dobrushinHeatBathGap_pos
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L) :
    0 < finiteLatticeWilsonDobrushinHeatBathGap D := by
  unfold finiteLatticeWilsonDobrushinHeatBathGap
  exact sub_pos.mpr D.dobrushinCoefficient_lt_one

/-- For a nonempty edge set, the standard Dobrushin random-scan rate is
nonnegative. -/
theorem finite_lattice_dobrushinRandomScanRate_nonneg
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ finiteLatticeWilsonDobrushinRandomScanRate L D := by
  have hCardPos : (0 : ℝ) < (Fintype.card L.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  have hCardOne : (1 : ℝ) ≤ (Fintype.card L.Edge : ℝ) := by
    exact_mod_cast hEdge
  have hGapLeOne : finiteLatticeWilsonDobrushinHeatBathGap D ≤ 1 := by
    unfold finiteLatticeWilsonDobrushinHeatBathGap
    linarith [D.dobrushinCoefficient_nonneg]
  have hGapLeCard :
      finiteLatticeWilsonDobrushinHeatBathGap D ≤
        (Fintype.card L.Edge : ℝ) :=
    le_trans hGapLeOne hCardOne
  have hDivLeOne :
      finiteLatticeWilsonDobrushinHeatBathGap D /
          (Fintype.card L.Edge : ℝ) ≤ 1 :=
    (div_le_one hCardPos).2 hGapLeCard
  unfold finiteLatticeWilsonDobrushinRandomScanRate
  linarith

/-- For a nonempty edge set, the standard Dobrushin random-scan rate is
strictly below one. -/
theorem finite_lattice_dobrushinRandomScanRate_lt_one
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteLatticeWilsonDobrushinRandomScanRate L D < 1 := by
  have hCardPos : (0 : ℝ) < (Fintype.card L.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  have hQuotPos :
      0 < finiteLatticeWilsonDobrushinHeatBathGap D /
        (Fintype.card L.Edge : ℝ) :=
    div_pos (finite_lattice_dobrushinHeatBathGap_pos D) hCardPos
  unfold finiteLatticeWilsonDobrushinRandomScanRate
  linarith

/-- Random-scan normalization recovers the unnormalized heat-bath gap exactly:
`|E| * (1 - rho) = 1 - alpha`. -/
theorem finite_lattice_edgeCard_mul_one_sub_dobrushinRandomScanRate
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    (Fintype.card L.Edge : ℝ) *
        (1 - finiteLatticeWilsonDobrushinRandomScanRate L D) =
      finiteLatticeWilsonDobrushinHeatBathGap D := by
  have hCard : (Fintype.card L.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  unfold finiteLatticeWilsonDobrushinRandomScanRate
  field_simp [hCard]

/-- Explicit positive conversion factor from the Dobrushin heat-bath gap to the
repository's normalized exact-gap carrier.  This is a normalization bridge; it
is not an independent derivation of the normalized value from the Wilson law. -/
def finiteLatticeWilsonDobrushinNormalizedScale
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L) : ℝ :=
  exactGapValueReal / finiteLatticeWilsonDobrushinHeatBathGap D

/-- The explicit Dobrushin normalization scale is positive. -/
theorem finite_lattice_dobrushinNormalizedScale_pos
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L) :
    0 < finiteLatticeWilsonDobrushinNormalizedScale D := by
  unfold finiteLatticeWilsonDobrushinNormalizedScale
  exact div_pos exactGapValueReal_pos
    (finite_lattice_dobrushinHeatBathGap_pos D)

/-- Multiplying the heat-bath gap by the explicit scale reproduces the public
normalized carrier, with no claim that the scale is dynamically derived. -/
theorem finite_lattice_dobrushinNormalizedScale_mul_heatBathGap
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L) :
    finiteLatticeWilsonDobrushinNormalizedScale D *
        finiteLatticeWilsonDobrushinHeatBathGap D =
      exactGapValueReal := by
  have hGap : finiteLatticeWilsonDobrushinHeatBathGap D ≠ 0 :=
    ne_of_gt (finite_lattice_dobrushinHeatBathGap_pos D)
  unfold finiteLatticeWilsonDobrushinNormalizedScale
  exact div_mul_cancel₀ exactGapValueReal hGap

/-- The remaining analytic input after Dobrushin matrix construction: the
actual centered Gibbs-pairing contraction of the concrete random-scan sweep at
the standard Dobrushin rate.  Keeping this as a separate certificate prevents
a TV row-sum bound from being silently treated as an already-proved `L²`
Rayleigh theorem. -/
structure FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
    (L : FiniteLatticeWilsonSystem) where
  matrixData : FiniteLatticeWilsonDobrushinMatrixData L
  edgeCard_pos : 0 < Fintype.card L.Edge
  centered_rayleigh_contraction :
    ∀ f : L.Configuration → ℝ,
      L.gibbsExpectationReal f = 0 →
        L.gibbsPairingReal (L.randomScanHeatBathSweep f) f ≤
          finiteLatticeWilsonDobrushinRandomScanRate L matrixData *
            L.gibbsPairingReal f f

/-- A certified Dobrushin random-scan rate lies in the Markov interval
`[0,1)`. -/
theorem FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate.rate_mem
    {L : FiniteLatticeWilsonSystem}
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate L) :
    finiteLatticeWilsonDobrushinRandomScanRate L C.matrixData ∈
      Set.Ico (0 : ℝ) 1 := by
  exact ⟨
    finite_lattice_dobrushinRandomScanRate_nonneg
      L C.matrixData C.edgeCard_pos,
    finite_lattice_dobrushinRandomScanRate_lt_one
      L C.matrixData C.edgeCard_pos⟩

end

end MathlibAnalytic
end MGAP4D

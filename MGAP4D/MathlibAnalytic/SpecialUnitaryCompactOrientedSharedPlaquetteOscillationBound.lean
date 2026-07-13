import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedSharedPlaquetteOscillation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Short name for the canonical compact oriented `SU(N)` Wilson system used by
the quantitative oscillation theorem. -/
abbrev specialUnitaryCompactOrientedOscillationSystem
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) : CompactOrientedGaugeWilsonSystem :=
  specialUnitaryCompactOrientedGaugeWilsonSystem
    geometry N hN beta beta_nonneg

/-- For the canonical `SU(N)` Wilson energy, every shared plaquette contributes
at most four to the conditional log-weight oscillation before multiplication
by `beta`. -/
theorem specialUnitaryCompactOriented_gibbsExponent_sourceResponse_oscillation_abs_le
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (A B : (specialUnitaryCompactOrientedOscillationSystem
      geometry N hN beta beta_nonneg).Configuration)
    (target source : geometry.Edge)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAgree : (specialUnitaryCompactOrientedOscillationSystem
      geometry N hN beta beta_nonneg).AgreeOffLink A B source) :
    let L := specialUnitaryCompactOrientedOscillationSystem
      geometry N hN beta beta_nonneg
    |(L.gibbsExponent (L.replaceLink A target u) -
        L.gibbsExponent (L.replaceLink B target u)) -
      (L.gibbsExponent (L.replaceLink A target v) -
        L.gibbsExponent (L.replaceLink B target v))| ≤
      beta * (4 * ((L.sharedPlaquettes target source).card : ℝ)) := by
  dsimp only
  let L := specialUnitaryCompactOrientedOscillationSystem
    geometry N hN beta beta_nonneg
  have hEnergy : ∀ g : L.Gauge, L.plaquetteEnergy g ≤ (2 : ℝ) := by
    intro g
    change specialUnitaryWilsonPlaquetteEnergy N g ≤ 2
    exact specialUnitaryWilsonPlaquetteEnergy_le_two hN g
  have h :=
    compact_oriented_gibbsExponent_sourceResponse_oscillation_abs_le_shared
      L 2 (by norm_num) hEnergy A B target source u v hAgree
  change _ ≤ beta * (4 * (((L.sharedPlaquettes target source).card : ℝ)))
  convert h using 1 <;> ring

end

end MathlibAnalytic
end MGAP4D

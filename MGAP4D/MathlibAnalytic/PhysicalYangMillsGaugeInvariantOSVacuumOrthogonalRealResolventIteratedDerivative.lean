import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventSmooth
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

set_option maxHeartbeats 1200000

/-- The `k`-th composition power of the excitation resolvent has derivative
`k â€¢ R^(k+1)` within the open real sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_pow_hasDerivWithinAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (k : â„•) {lambda : â„} (hlambda : lambda < G.mass) :
    HasDerivWithinAt
      (fun mu =>
        (G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ k)
      ((k : â„) â€¢
        (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (k + 1))
      (Set.Iio G.mass) lambda := by
  induction k with
  | zero =>
      have hconst :
          HasDerivWithinAt
            (fun _ : â„ =>
              (1 : P.VacuumOrthogonalHilbert â†’L[â„]
                P.VacuumOrthogonalHilbert))
            (0 : P.VacuumOrthogonalHilbert â†’L[â„]
              P.VacuumOrthogonalHilbert)
            (Set.Iio G.mass) lambda :=
        hasDerivWithinAt_const lambda (Set.Iio G.mass)
          (1 : P.VacuumOrthogonalHilbert â†’L[â„]
            P.VacuumOrthogonalHilbert)
      have hzero :
          (0 : P.VacuumOrthogonalHilbert â†’L[â„]
            P.VacuumOrthogonalHilbert) =
            (0 : â„) â€¢
              (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^
                (0 + 1) := by
        simp
      simpa only [pow_zero] using hconst.congr_deriv hzero
  | succ k ih =>
      have hR :
          HasDerivWithinAt
            (G.vacuumOrthogonalRealResolventOn T hP hSelf)
            ((G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ 2)
            (Set.Iio G.mass) lambda := by
        simpa [pow_two, ContinuousLinearMap.mul_def,
          G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hlambda] using
          G.vacuumOrthogonalRealResolventOn_hasDerivWithinAt
            T hP hSelf hlambda
      have hmul := HasDerivWithinAt.mul
        (ğ•œ := â„)
        (ğ”¸ := P.VacuumOrthogonalHilbert â†’L[â„]
          P.VacuumOrthogonalHilbert)
        ih hR
      have hmul' :
          HasDerivWithinAt
            (fun mu =>
              (G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ (k + 1))
            ((k : â„) â€¢
                (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (k + 1) *
                  G.vacuumOrthogonalRealResolventOn T hP hSelf lambda +
              (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ k *
                (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ 2)
            (Set.Iio G.mass) lambda := by
        simpa only [Pi.mul_apply, pow_succ] using hmul
      have hderiv :
          ((k : â„) â€¢
                (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (k + 1) *
                  G.vacuumOrthogonalRealResolventOn T hP hSelf lambda +
              (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ k *
                (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ 2) =
            ((Nat.succ k : â„•) : â„) â€¢
              (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^
                (Nat.succ k + 1) := by
        let Rlambda :=
          G.vacuumOrthogonalRealResolventOn T hP hSelf lambda
        change
          ((k : â„) â€¢ Rlambda ^ (k + 1)) * Rlambda +
              Rlambda ^ k * Rlambda ^ 2 =
            ((Nat.succ k : â„•) : â„) â€¢
              Rlambda ^ (Nat.succ k + 1)
        rw [smul_mul_assoc]
        have hfirst : Rlambda ^ (k + 1) * Rlambda = Rlambda ^ (k + 2) := by
          simpa [Nat.add_assoc] using (pow_succ Rlambda (k + 1)).symm
        have hsecond : Rlambda ^ k * Rlambda ^ 2 = Rlambda ^ (k + 2) := by
          simpa using (pow_add Rlambda k 2).symm
        rw [hfirst, hsecond]
        simp [Nat.cast_succ, Nat.succ_eq_add_one, add_smul, Nat.add_assoc]
      exact hmul'.congr_deriv hderiv

/-- Every iterated derivative within the open real sub-mass interval is the
factorial multiple of the corresponding composition power. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_iteratedDerivWithin
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (n : â„•) {lambda : â„} (hlambda : lambda < G.mass) :
    iteratedDerivWithin n
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) lambda =
      (n.factorial : â„) â€¢
        (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (n + 1) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (G.vacuumOrthogonalRealResolventOn T hP hSelf)
                (Set.Iio G.mass))
              (Set.Iio G.mass) lambda =
            derivWithin
              (fun mu =>
                (n.factorial : â„) â€¢
                  (G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ (n + 1))
              (Set.Iio G.mass) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hpow :=
        G.vacuumOrthogonalRealResolventOn_pow_hasDerivWithinAt
          T hP hSelf (n + 1) hlambda
      have hscaled :
          HasDerivWithinAt
            (fun mu =>
              (n.factorial : â„) â€¢
                (G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ (n + 1))
            ((n.factorial : â„) â€¢
              (((n + 1 : â„•) : â„) â€¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆbÆÖ&F’à¢†â²"’’¢…6WBä––òræÖ72’ÆÖ&F£Ò'¢6–×öæÇ’µ’ç6×VÅöÇ•ÒW6–æp¢„†4FW&—ev—F†–äBæ6öç7E÷6×VÀ¢	ÙYÂ£Ò(IÒ’…"£Ò(IÒ¢„b£Òåf7WVÔ÷'F†övöæÄ†–Æ&W'B(i$Å¾(IÕĞ¢åf7WVÔ÷'F†övöæÄ†–Æ&W'B¢†âæf7F÷&–Â¢(IÒ’‡÷r¢ÆWBFW&—efÇVR ¢åf7WVÔ÷'F†övöæÄ†–Æ&W'B(i$Å¾(IÕĞ¢åf7WVÔ÷'F†övöæÄ†–Æ&W'B£Ğ¢†âæf7F÷&–Â¢(IÒ’(
 ¢‚‚†â²¢(IR’¢(IÒ’(
 ¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆbÆÖ&F’à¢†â²"’¢†fR†g66ÆVB ¢†4dFW&—ev—F†–ä@¢†gVâ×RÓà¢†âæf7F÷&–Â¢(IÒ’(
 ¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb×R’â†â²’¢‡Fõ7å6–ævÆWFöâ(IÒFW&—efÇVR¢…6WBä––òræÖ72’ÆÖ&F£Ò'¢6–×¶FW&—efÇVUÒW6–ær‡66ÆVBæ†4dFW&—ev—F†–ä@¢†fR†fFW&—b ¢fFW&—ev—F†–â(IĞ¢†gVâ×RÓà¢†âæf7F÷&–Â¢(IÒ’(
 ¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb×R’â†â²’¢…6WBä––òræÖ72’ÆÖ&FĞ¢Fõ7å6–ævÆWFöâ(IÒFW&—efÇVR£Ğ¢†g66ÆVBæfFW&—ev—F†–â†—4÷Våô––òçVæ—VTF–fdöâÆÖ&F†ÆÖ&F¢†fR‡66ÆVDFW&—b ¢FW&—ev—F†–à¢†gVâ×RÓà¢†âæf7F÷&–Â¢(IÒ’(
 ¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb×R’â†â²’¢…6WBä––òræÖ72’ÆÖ&FÒFW&—efÇVR£Ò'¢VæföÆBFW&—ev—F†–à¢'r¶†fFW&—eĞ¢6–×¶FW&—efÇVUĞ¢'r¶‡66ÆVDFW&—eĞ¢6–×¶FW&—efÇVRÂæBæf7F÷&–Å÷7V62ÂæBæ67Eö×VÂÂæBæ67E÷7V62À¢6×VÅ÷6×VÂÂ×VÅö6öÖÒÂ×VÅö76ö2ÂæBæFEö76ö5Ğ ¢òÒÒW‡Æ–6—B÷&F–æ'’ÆÂÖ÷&FW"FW&—fF—fRf÷&×VÆ&VÆ÷rF†RG&ç6fW'&VBÖ73 ¦%â†â’†ÆÖ&F’Òâ(
""†ÆÖ&F•â†â³–âÒğ§F†V÷&VÒf–æ—FUföÇVÖUf7WVÔvG&ç6fW"çf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöåö—FW&FVDFW&—`¢…B¢å7G&öævÇ”6öçF–çV÷W5‡—6–6Å6VÖ–w&÷W¢„r¢Bäf–æ—FUföÇVÖUf7WVÔvG&ç6fW"¢†…¢ä—4æ÷&ÖÆ—¦VB¢†…6VÆb¢—56VÆdF¦ö–çBBæ6Æ÷6VE&–v‡D†Ö–ÇFöæ–â¢†â¢(IR’¶ÆÖ&F¢(I×Ò††ÆÖ&F¢ÆÖ&FÂræÖ72’ ¢—FW&FVDFW&—bà¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb’ÆÖ&FĞ¢†âæf7F÷&–Â¢(IÒ’(
 ¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçBB……6VÆb†ÆÖ&F’â†â²’£Ò'¢6Æ0¢—FW&FVDFW&—bà¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb’ÆÖ&FĞ¢—FW&FVDFW&—ev—F†–âà¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb¢…6WBä––òræÖ72’ÆÖ&F£Ğ¢†—FW&FVDFW&—ev—F†–åööeö—4÷Và¢†â£Òâ¢†b£Òrçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb¢—4÷Våô––ò†ÆÖ&F’ç7–ÖĞ¢òÒ†âæf7F÷&–Â¢(IÒ’(
 ¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆbÆÖ&F’â†â²’£Ğ¢rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöåö—FW&FVDFW&—ev—F†–à¢B……6VÆbâ†ÆÖ&F¢òÒ†âæf7F÷&–Â¢(IÒ’(
 ¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçBB……6VÆb†ÆÖ&F’â†â²’£Ò'¢'r´rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöåööeöÇBB……6VÆb†ÆÖ&FĞ ¢òÒÒ6Öö÷F†æW72æBÆÂÖ÷&FW"FW&—fF—fR6¶vRf÷"F†RW†6—FF–öâ&W6öÇfVçBâÒğ§F†V÷&VÒf–æ—FUföÇVÖUf7WVÔvG&ç6fW"çf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçE6Öö÷F…÷6¶vP¢…B¢å7G&öævÇ”6öçF–çV÷W5‡—6–6Å6VÖ–w&÷W¢„r¢Bäf–æ—FUföÇVÖUf7WVÔvG&ç6fW"¢†…¢ä—4æ÷&ÖÆ—¦VB¢†…6VÆb¢—56VÆdF¦ö–çBBæ6Æ÷6VE&–v‡D†Ö–ÇFöæ–â’ ¢6öçDF–fdöâ(IÒ(‰à¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb¢…6WBä––òræÖ72’(Šp¢(ˆ†â¢(IR’¶ÆÖ&F¢(I×Ò††ÆÖ&F¢ÆÖ&FÂræÖ72’À¢—FW&FVDFW&—bà¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöâB……6VÆb’ÆÖ&FĞ¢†âæf7F÷&–Â¢(IÒ’(
 ¢„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçBB……6VÆb†ÆÖ&F’â†â²’£Ğ¢)ú„rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöåö6öçDF–fdöåö–ægG’B……6VÆbÀ¢gVââ¶ÆÖ&FÒ†ÆÖ&FÓà¢rçf7WVÔ÷'F†övöæÅ&VÅ&W6öÇfVçDöåö—FW&FVDFW&—`¢B……6VÆbâ†ÆÖ&F£ÒÆÖ&F’†ÆÖ&F)ú ¦VæB7G&öævÇ”6öçF–çV÷W5‡—6–6Å6VÖ–w&÷W ¦VæB‡—6–6Å–ætÖ–ÆÇ4vVvT–çf&–çDõ5&VfÆV7F–öäFFäõ5&T†–Æ&W'DFF ¦VæBÖF†Æ–$æÇ—F–0¦VæBÔtD@ ¦Væ@
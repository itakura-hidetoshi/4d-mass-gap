# P4-Q2-PZ37AIH — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、左右のhalfweight、ZW signed physical L² source、その連続代表、元の空間積Haar、型付き証明履歴、Lean/mathlib pinおよびworkflowを変更しない。

## 1．実際のexact-source検証台帳

| 対象 | 検証された値 |
| --- | --- |
| [AIH定理PR #6517](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6517) | MERGED |
| 基礎formal HEAD（AIG記録まで） | `88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7` |
| 検証済みsource HEAD | `37b799c13b6b2b86b1471f0188717755fd27663b` |
| 検証済みtest-merge HEAD | `9ca5d1ca6353b09690355b463704261f1b98ee1a` |
| AIH定理squash／統合時formal HEAD | `d2ca52eaf35da603774a6664d74a688905bd35ab` |
| source／test-merge／squashの共通Git tree | `0ce1f185f26fffa0a88b42925f9bec0be830204e` |
| AIH新規Leanの共通Git blob | `6afcb3b1b16694f688bc9a11b9051067a0379d73` |
| [Exact-source CI #42476531600 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42476531600/attempts/1) | completed／SUCCESS |
| Lean job | `128719019032`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| 依存閉包 | **11,396／11,396 SUCCESS** |
| 独立completion receipt job | `128720592936`、completed／SUCCESS |
| Receipt実ログ | `exact_sha=37b799c13b6b2b86b1471f0188717755fd27663b source_result=success run=42476531600 attempt=1` |
| Commit status context | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| 新規公開宣言・公理出力 | **19／19**。全件 `propext`／`Classical.choice`／`Quot.sound` のみ |
| 公理出力の欠落・余剰・重複 | **0／0／0** |
| 完了ログの `sorryAx` | なし |
| 変更AIHファイルのwarning／error | **0／0**（依存ファイルの既存warningとは区別） |
| 診断artifact | `13615947107`、`lean-fast-check-log` |
| Artifact digest | `sha256:04815aee765a02666dc26bff5e0cb26aae85f527dbfb87989d530882d04becf2` |
| 差分 | 新規Leanファイル1件、365行追加、削除0、17定理＋2定義 |
| 新規外部公理／sorry／admit／unsafe | なし |
| Lean pin | `v4.30.0-rc2` |
| mathlib pin | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

完成ジョブのログからAIHの19個の `#print axioms` 実出力を数え、19宣言の名前と一対一で照合した。結果はすべて標準の3公理だけ。ソースの `#print axioms` 指令の存在だけで公理監査を済ませず、完成ログ側の実出力を確認した。独立受領書は同一source SHA・同一run・attempt 1を記録し、successのcommit statusも確認済みである。

GitHubのGit commit/tree/blobを読み戻してsource・test-mergeのtree一致を先に確認し、squash後のformal HEADがAIHソースの同じtreeおよびLean blobを持つことを再確認した。初期候補のCI初回attemptで完成しており、Leanソースの修正、heartbeat増加、仮定変更、toolchain変更、workflows変更は不要だった。既存依存モジュールの一部warningは存在するが、**変更AIHファイルのwarning/errorは0/0**である。

[検証済みAIH Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d2ca52eaf35da603774a6664d74a688905bd35ab/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAllCouplingNegativeHaarBallV5_PZ37AIH.lean)

## 2．対象と条件

`H : ℕ` は元の有限体積パラメータ、`Link_H` は元の空間リンク集合、`Cfg_H` は元のSU(2)空間境界配置、`mu_H` は元の規格化積Haar確率測度とする。

- `W_H`：元の空間Wilson作用。
- `S_H(A,B)`：元の完全一スラブWilson作用。左空間halfweight＋時間交差作用＋右空間halfweight。
- `K_{H,beta}(A,B)=exp(-beta*S_H(A,B))`：元の完全kernel。
- `f_{0,H}`：元のZW符号付き物理的L² source。既存AHPによる `fCont_H` とのHaar-a.e.一致だけを利用し、任意L²代表の点ごとの値と同一視しない。
- `T_{H,beta} f_{0,H}`：元の物理的transfer。
- `M_H=∫|fCont_H| dmu_H=∫|f_{0,H}| dmu_H`：既存AHN/AEVが証明した元のsourceの真正Haar L¹質量（a.e.同一視を介する）。既存AHJにより `0≤M_H≤p_H/2`。
- `D_sp,H(B,C)=∑_{e∈Link_H} d_J(B_e,C_e)`：元のADKの真正SU(2) chordal distanceを使うAGGの全リンク距離。
- `n_H=Nat.card Link_H`、`kappa(r)=p4Q2PZ37ADQ_sphereRadiusFraction r`。

元kernelの全ての物理的定義、有限型carrier、測度、作用、source、仮定はAIH内で再定義・置換しない。

## 3．真正作用から全結合Lipschitz評価へ

AEMの元の交差Wilson作用は、右リンクを一つ変更すると

```text
|Cross(A, B[e↦g]) - Cross(A, B[e↦h])| ≤ d_J(g,h)
```

となる。元の右空間Wilson作用は、同じ変更で

```text
|W(B[e↦g]) - W(B[e↦h])| ≤ 24*d_J(g,h)
```

となる。元の完全一スラブ作用には右空間作用の係数1/2があり、変更しない左空間作用は差で消える。したがってAIHは

```text
|S(A, B[e↦g]) - S(A, B[e↦h])| ≤ (1+24/2)*d_J(g,h)
                                   = 13*d_J(g,h)
```

を新規Lean定理として構成する。

既存AEMの `p4Q2PZ37AEM_real_nonnegativeWilsonBoltzmannLipschitz` は任意の `beta≥0` と非負作用に使用でき、指数因子の新しい上界や小結合仮定を不要とする。この定理で真のkernelの差を評価する：

```text
|K_beta(A,B[e↦g])-K_beta(A,B[e↦h])|
   ≤ 13*beta*d_J(g,h)             (beta≥0).
```

AGGの有限座標telescopingを適用すると

```text
|K_beta(A,B)-K_beta(A,C)|
   ≤ 13*beta*D_sp,H(B,C)          (beta≥0)
```

が得られる。ここで任意の左積分配置Aを保持する。

AIHは元のsource質量だけから

```text
Lambda_H(beta) := (13*beta)*M_H
```

を定義し、`beta≥0` で `Lambda_H(beta)≥0`、および

```text
Lambda_H(beta) ≤ (13*beta)*(p_H/2)
```

を証明する。さらにAHPの全結合に対する元物理transferと連続source積分の一致、AEVの符号付き積分差の定理、AHNのHaar L¹同一性から

```text
|T_beta f0(B) - T_beta f0(C)|
  ≤ Lambda_H(beta) * D_sp,H(B,C)  (beta≥0)
```

を得る。正sourceへの置換、別Haar則の使用、外部Lipschitz仮定の導入はない。

`Lambda_H(0)=0` であり、元の固定結合 `beta0=log(3/2)/64` では

```text
Lambda_H(beta0) = p4Q2PZ37AHH_transferSlope H
```

が定義上の等式として成り立つ。既存AHHの固定結合傾き評価を上書きせず、同じ値に特殊化する。

## 4．一般正結合における負値球とHaar下界

AIGが既に全 `H : ℕ`、`beta>0` で構成した元の負余裕を

```text
epsilon_H(beta)
 = beta * Zcross_H(beta) * exp(-2*beta*p_H) * V_H / 2 > 0
```

とする。AIGは元の物理的transferがこの**全余裕**を超えて負となる中心 `B` の存在を証明済み。

AIHは `beta≥0` と任意の `epsilon>0` に対して

```text
R_H(beta,epsilon)
 = epsilon / (2*(Lambda_H(beta)+1)) > 0
```

を導入する。全リンク変動評価によって、

```text
T_beta f0(B) < -epsilon
  ⇒ ∀ C, D_sp,H(B,C) < R_H(beta,epsilon)
       ⇒ T_beta f0(C) < -epsilon/2
```

を証明した。固定結合 `beta0` では `R_H(beta0,epsilon)` がAIGの既存固定結合半径と定義上で一致する。

既存AHLの**同じ元の空間積Haar**球下界と固定mathlibの `Fintype.card_eq_nat_card` を使用して、

```text
0 < kappa(R/(n_H+1))^n_H
  ≤ mu_H.real {C | D_sp,H(B,C) < R}
```

を証明した。これにより全 `beta>0` に対し、`epsilon=epsilon_H(beta)`、`R=R_H(beta,epsilon_H(beta))` で、正の具体的半径と真正Haar質量下界を持つ負値安定球が存在する。

**集合の区別**：AIGの全余裕領域 `{C | T_beta f0(C)<-epsilon_H(beta)}` は、既存AIGにより開・正Haar測度。AIHの球はこの全余裕領域に包含されるとは主張しない。AIHが定量的に下界を与えるのは球と、これを含む**半余裕領域**

```text
{C | T_beta f0(C) < -epsilon_H(beta)/2}
```

である。この違いは形式証明の結論に保存している。

## 5．宣言19件と証明出力の対応

| # | AIH宣言（prefix `p4Q2PZ37AIH_` を省略） | 意味 |
|---:|---|---|
| 1 | `originalOneSlabAction_rightOneLinkChordSlope` | 真の完全作用の1リンク係数13 |
| 2 | `originalKernel_rightOneLinkChordSlope` | 全非負結合でkernelの1リンク係数13β |
| 3 | `originalKernel_rightAllLinkChordSlope` | 全リンクの真のkernel変動 |
| 4 | `transferSlope` | 元sourceからのΛ_H(β)定義 |
| 5 | `transferSlope_nonneg` | β≥0で非負 |
| 6 | `transferSlope_le_halfCount` | 元plaquette数による上限 |
| 7 | `transferSlope_zero` | β=0でΛ=0 |
| 8 | `transferSlope_fixedCoupling` | 既存AHH傾きへの厳密特殊化 |
| 9 | `originalTransfer_allLinkSlope` | 元の物理transferの全結合Lipschitz評価 |
| 10 | `originalTransfer_allLinkHalfCountSlope` | plaquette数による元transfer傾き上限 |
| 11 | `originalNegativeBallRadius` | 半余裕の半径定義 |
| 12 | `originalNegativeBallRadius_pos` | β≥0、ε>0で半径正 |
| 13 | `originalNegativeBallRadius_fixedCoupling` | AIG固定半径への厳密特殊化 |
| 14 | `originalNegativeBall_stable` | 元transferの球内半余裕負性 |
| 15 | `originalNegativeBall_mass_ge_explicit` | 元球の真正Haar質量下界 |
| 16 | `originalNegativeBall_mass_pos` | 元球の正の実数Haar測度 |
| 17 | `originalHalfNegativeRegion_mass_of_center` | 半余裕領域への明示的下界 |
| 18 | `originalTransfer_exists_negativeHaarBall` | β>0で実際の負中心＋正半径＋質量下界の無条件存在 |
| 19 | `originalHalfNegativeRegion_mass_ge_explicit` | β>0で半余裕領域の明示的な正下界 |

19件全てに実際の `#print axioms` 出力があり、依存公理は標準の3件のみ。通常のLean証明中に新しい公理を加えたわけではない。新規のLean leafを変更した以外、元の物理的定義、既存定理署名、import root、Lean/mathlib pin、CI設定に変更はない。

## 6．境界と今後の障害（未認証のまま保持）

AIHが新たに証明したのは、各有限H・全非負結合の元transfer Lipschitz評価、および各有限H・各正結合での元の負値安定球と元Haarの下界である。係数、半径、測度下界はHに依存する。元の`Zcross_H(beta)`、`V_H`、`M_H`、`p_H`も明示評価済み数値とは限らない。

以下をこの成果から認証しない。

- 正のtransfer値を持つ右境界や、同じ結合における正負双方のHaar領域、二殻の存在。
- 数値的な元境界リンク割当て、計算済みAGP符号判定表、算出済みtransfer値。
- H／体積について一様な負余裕、半径、真正Haar質量下界。
- Uniform coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gap。
- β≤0での負領域の正値余裕や定量的質量下界（β=0のLipschitz評価は成立しているが、負値存在は主張しない）。

今後のAI I（AII）以降では、例えば正境界を新たな定理として示すか、負領域の体積一様性に必要な独立した評価を構成する必要がある。どちらもAIHだけからは得られない。

## 7．再検証参照先

- [AIH Lean4正本](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d2ca52eaf35da603774a6664d74a688905bd35ab/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAllCouplingNegativeHaarBallV5_PZ37AIH.lean)
- [AIG既証明負領域と固定球](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean)
- [AEM元kernel・空間作用の変動評価](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSpatialChordKernelV5_PZ37AEM.lean)
- [AGG元全リンクchordal評価](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSpatialChordalCellOscillationV5_PZ37AGG.lean)
- [AEV真正符号付き積分差定理](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalReceiverRightBoundaryTransferKernelSlopeV5_PZ37AEV.lean)
- [AHP全結合の物理sourceと積分の橋渡し](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFirstOrderHaarExpansionV5_PZ37AHP.lean)
- [AHN真正source L¹質量](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentitySourceHaarMomentV5_PZ37AHN.lean)
- [AHL元の球の真正Haar測度下界](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAlignedPositiveSpatialHaarMassV5_PZ37AHL.lean)
- [固定mathlibの有限card API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/SetTheory/Cardinal/Finite.lean)

本正式記録は検証済みCIおよび元Lean定理についての報告であり、記録文章それ自体を数学的形式証明の代替とはしない。

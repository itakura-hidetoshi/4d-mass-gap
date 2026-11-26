# MGAP4D — 研究ロードマップ

**2026-11-27 JST / 実ソース・独立 CI 照合に基づく現況**

目的：真正4次元 Wilson 格子模型の有限体積での認証済み数学から、非自明な完成 OS 空間・連続体の構成および正の Hamiltonian 質量ギャップへ進む。**連続体質量ギャップは未証明。** 課題の依存を明示し、成立しない一般化は no-go として残す。

## 1. 認証の現在地

- Formal 正本：[b61bba86ceee0ba4886b3582bd73072640a4521e](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/b61bba86ceee0ba4886b3582bd73072640a4521e)、AQP まで正式統合。
- AQN：[PR #7058](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/7058)・[CI #45818034796](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45818034796)、19 / 19 公理監査。
- AQO：[PR #7062](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/7062)・[CI #45894555500](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45894555500)、11,607 / 11,607 jobs、13 / 13 公理監査、統合後成果物引継ぎ [CI #45897012142](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45897012142) SUCCESS。
- AQP：[PR #7066](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/7066)・[CI #45902581226](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45902581226)、11,608 / 11,608 jobs、7 / 7 公理監査、独立認証・正式統合済み。
- AQR：以下の相対転送二次形式の研究候補。Lean 候補・CI・認証は未実施。

| 区分 | 判定 |
|---|---|
| MERGED | Formal 正本の同一ソースで確認済み |
| INDEPENDENT GREEN | 直接Lean・実Lean MCP・別runner独立CIで認証、まだ正本に未統合 |
| SANDBOX GREEN | 直接Leanと実Lean MCPで認証、独立CI待ち |
| OPEN / HOLD | 未証明、未検査、または条件不足。失敗と論理的不可能性を混同しない |
| NO-GO | 指定された仮定・評価法に対する障害を形式証明済み |

## 2. 研究全体の到達点

| 層 | 状態 | 残りの証明義務 |
|---|---|---|
| 真正有限格子作用・Haar・Gibbs・Gauss-law transfer | 既存正本 | 元の定義・型・測度の保持 |
| 小結合区間の全top直交補一様収縮 | [AKL](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformTopOrthogonalCoercivityV5_PZ37AKL.lean) MERGED：3071/3072 | これを真正完成 OS の非零励起、適切な半群、連続体スケールへ接続する |
| 真正物理モードと局所真空評価 | [AOG](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformFirstModeMagnitudeV5_PZ37AOG.lean)、[AOU](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFirstRowRightSlopeLimitV5_PZ37AOU.lean) MERGED | 固定Hの極限を移動体積の極限と混同しない |
| 真正有限体積 OS 像 | APL–APW MERGED | 完成OSの実現条件・非退化の保持 |
| 支持予算付き時間移動・零方向降下 | [APZ](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalSupportBudgetTransportV5_PZ37APZ.lean)、[AQC](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSNullDescentV5_PZ37AQC.lean) MERGED | 支持予算が尽きる前の局所代数と極限の整合 |
| 真正 Gibbs 反射相関の絶対・条件付き相対減衰 | [AQJ](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSConnectedGeometricV5_PZ37AQJ.lean)、[AQK](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSRelativeHorizonV5_PZ37AQK.lean) MERGED | 相対前因子 B/a₀ の一様制御 |
| 四辺の具体的中心化方向 | [AQN](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSFourEdgeCenteredRayV5_PZ37AQN.lean) MERGED | H 一様な OS 分母の下界 |
| 定量的端点テンソル試験 | [AQO](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSQuantitativeEndpointTensorV5_PZ37AQO.lean) MERGED | 正の下界の体積一様化 |
| 真空重み付き二モードノルム | [AQP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalVacuumWeightedProbeUniformNormV5_PZ37AQP.lean) MERGED | 認証済み成果物引継ぎ（実行中） |
| 完成OSの真正 transfer・連続体 | OPEN | 下記 3–5 |

## 3. 直近のクリティカルパス：真正 OS 分母

### AQP — 正式統合完了

真正SU(2) Wilson の一辺 Haar refresh と局所真空 Harnack により、任意 H・β≥0・q∈ℝ で

$$ \|w_{H,\beta,q}\|^2\geq e^{-16\beta}(1+q^2). $$

R1の格子辺長と内積展開の失敗、R2/R3の型接続失敗を保持し、R4の独立抽象Hilbert補題で解消。Sandbox直接Lean・実Lean MCPの7/7監査、独立CIの7/7監査、標準3公理のみ。認証済み提出blob `30625b2eb6daa7e3394dc16cae1225c713b05b0b`。

提出・テストマージ・正式統合の Git tree は `674b005cb87fc11924b071ada33a5e35dcc79658` で完全一致。認証済み leaf delta の引継ぎ [CI #45904145140](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45904145140) は観測時点で実行中。公開確認後に次の Sandbox を起動する。

### AQR — 相対転送二次形式（OPEN / 研究候補）

AQO と同じ真正物理 T_H、λ_H=‖T_H‖>0、真空重み付き w_H（APP の中心化係数 q_C）、真正 Wilson 分配関数の逆平方根 c_H を用いる。β>0 の AQO の等式から

$$ \frac{J_H}{\|w_H\|}=P_HR_HN_H,\quad P_H=c_H\lambda_H^{H+1},\quad R_H=\frac{\langle T_Hw_H,w_H\rangle}{\lambda_H\|w_H\|^2},\quad N_H=\|w_H\|. $$

- N_H の下界は AQP で独立認証済み。
- R_H は各有限体積で厳密正値。まず既存定理索引・元Lean型・依存・障害を照合し、真正 local Haar 特徴・正値作用素・局所条件付き評価から、固定の正の β または明示した正の結合区間で H に依存しない正の下界が得られるかを検討する。
- 上からの収縮定理 AKL は R_H の下界を直接与えない。β=0 の退化、真空直交の有無、局所的な分散下界と符号付き転送二次形式の違いを保持する。必要なら反例を形式化し、条件を分離する。

**完了条件：** 真正 w_H と T_H のままで下界定理（または仮定を明記した障害定理）が直接Lean・実Lean MCP・独立CIに合格すること。未認証の段階名は証明成果ではない。

### 分配関数因子（OPEN）

真正 c_H=Z_H^{-1/2} と λ_H の冪の比を評価する。物理 Gauss-law sector と全周期 Gibbs 分配関数との同一性・境界条件・正規化を確認し、trace 等との接続が必要ならその等式自体を形式化する。単なる有限体積での正値性や上界から一様下界を推論しない。P_H の一様下界または P_HR_H の直接下界を探す。

### AQO → AQN → AQK の接続（条件付き、未閉鎖）

上記の因子積に体積一様な正の下界 δ が得られた場合、AQO から真正初期 OS 相関 a₀≥δ² を得る。AQN の4辺支持・一様分子ノルム上界と Dobrushin 閾値の下で、AQK の相対前因子 B/a₀≤K を確立する。AQK の有限整数 horizon は支持の二重到達条件が満たされる場合にだけ適用する。

## 4. no-go と再利用禁止の誤った推論

| 既存形式成果 | 保持する障害 | 代替経路 |
|---|---|---|
| [APX](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalPositiveTimeHalfTurnObstructionV5_PZ37APX.lean) / [APY](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalCompletedOSVacuumLineObstructionV5_PZ37APY.lean) | 全時間の同一正半代数保存は真空線への退化を強いる条件付き障害 | 支持予算のある局所時間移動と極限での降下 |
| [AQG](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSReflectedCorrelationThresholdV5_PZ37AQG.lean) | Haar norm majorant は非零基底を厳密に縮める証明書にならない | 真正 Gibbs 反射相関へ戻る |
| [AQK](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSRelativeHorizonV5_PZ37AQK.lean) | 絶対幾何上界から一様相対収縮は自動的に出ない | 非零初期値に対する前因子を制御 |
| [AQL](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSRelativeAmplitudeFiberV5_PZ37AQL.lean) | 定数加算で中心化相関を保ちながら raw prefactor を非有界化できる | 中心化した代表を選ぶ |
| [AQM](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSCenteredNullFiberV5_PZ37AQM.lean) | 非零OS零方向が存在すると中心化fiberも非有界化する | read の単射性を確認した選択部分空間 |

これらは指定した仮定・表現・評価経路の no-go である。真正模型全体や連続体 Yang–Mills の不可能性には昇格させない。局所的に得た証明を大域化する際は型・定義域・極限の互換性を改めて検証する。

## 5. 中長期 — 完成OSと連続体への証明義務

1. 真正の非零励起の境界実現と同一性を、完成OSの定義域・商・閉包の中で確認する。選択一次元方向の単射性を全励起の coercivity と混同しない。
2. 局所時間移動から整合的な正時間半群を構成し、真空の保存、強連続性、真正物理 transfer との接続、必要な非退化を確認する。APX/APY の矛盾する有限周期の全時間仮定を復活させない。
3. 体積極限および格子間隔の極限を区別し、同一の物理的正規化と観測量を保つ。固定小結合の lattice contraction を物理単位の連続体質量ギャップと同一視しない。
4. 非自明な連続体量子 Yang–Mills 理論の存在・公理的整合と、生成 Hamiltonian の真空上の正のスペクトルギャップを、必要な群・スケール・定義域の条件を含めて証明する。現時点で達成済みとはしない。

## 6. 実行・認証規律

- 版固定 Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。現行 Formal HEAD、元ソース blob、imports、依存signature、固定mathlib API を照合してから候補を作る。
- 既存証明・失敗履歴・no-go を版固定で再利用し、重複した新規証明や同じ失敗候補の再計算を避ける。
- 隔離 GitHub Sandbox で同一runner上の候補を直接Lean・標準公理監査し、合格候補を実Lean MCPで検証する。GREEN 前に独立CIを起動しない。
- 別runner独立CIで同じ blob と test-merge tree、Lean step 完了、warning/error/sorryAx、独立completion receipt を照合。合格した追加leafだけを正式統合する。
- exact cache は認証済みのものだけを再利用する。統合後tree・来歴・no-build検査が合格すれば追加の全体Leanビルドを不要とする。キャッシュ公開確認前に次の Sandbox を起動しない。インフラHOLDを証明失敗と混同しない。
- append-only / tighten-only を守る。仮定の弱化、既存物理定義の無断変更、sorry/admit、新規公理を禁止する。文書だけの更新では Lean を変更・再検証しない。

## 7. 記録と出典

- [README — 現況](README.md)
- [Formal 正本の観測時ソース](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic)
- [AQP 正式統合済みソース](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b61bba86ceee0ba4886b3582bd73072640a4521e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalVacuumWeightedProbeUniformNormV5_PZ37AQP.lean)、[独立認証](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45902581226)
- [旧 ROADMAP 全文の保存コピー](docs/archive/2026-11-27-pre-refresh/ROADMAP.md) / [更新前の固定版（元の相対リンク付き）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/bcea883b55142c8c53c51271bb8861107813519b/ROADMAP.md)

本ロードマップは研究経路と証明義務の記録であり、定理の認証はソースと実行証拠に従う。旧版は全文・blobを保存し、現在地を誤読させないため現行入口から分離した。

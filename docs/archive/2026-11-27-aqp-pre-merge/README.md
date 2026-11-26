# MGAP4D — 4次元 Yang–Mills 質量ギャップの Lean 4 形式証明研究

**現況スナップショット：2026-11-27 JST（Formal 正本・GitHub Actions 実ログ照合）**

> **4次元 Yang–Mills の連続体質量ギャップ問題は未解決。** 本リポジトリはその形式証明研究であり、Clay ミレニアム問題を解決したという主張ではない。小結合の真正有限格子 transfer の一様収縮と、完成 OS 空間・連続体 Hamiltonian の質量ギャップは別の命題である。

MGAP4D is a Lean 4 research project on the four-dimensional Yang–Mills existence and mass gap problem. The current model-facing route studies the genuine finite periodic SU(2) Wilson system, its normalized physical transfer, reflection positivity and Osterwalder–Schrader (OS) boundary data. Certified finite-volume results and conditional bridges are distinguished from unresolved continuum obligations.

## 1. 正本と現在の認証

| 項目 | 2026-11-27 の観測結果 |
|---|---|
| Lean 定理の唯一の正本 | [formal/real-hilbert-uniform-coercive-strong-limit](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) |
| 観測時 Formal HEAD | [`d401555b432add745150c1c28d3e54a0fae59e64`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d401555b432add745150c1c28d3e54a0fae59e64)（AQO まで正式統合） |
| 最新独立認証 | AQP：[PR #7066](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/7066)、[CI #45902581226](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45902581226) SUCCESS、正式統合前 |
| ビルド | 最新独立CI：11,608 / 11,608 Lake jobs 成功（定理数ではない） |
| 公理監査 | AQP 7 / 7、標準3公理のみ：`propext`, `Classical.choice`, `Quot.sound` |
| AQP Sandbox | 直接Lean 29.662秒・実Lean MCP 19.909秒、両方7 / 7、error / warning / sorryAx = 0 / 0 / 0 |
| Lean / mathlib | `leanprover/lean4:v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| 文書 | `main` は公開文書ミラー。定理の状態は Formal のソース・実行記録を優先する。 |

## 2. 何を証明しているのか

元の有限周期4次元 Wilson 作用、コンパクト群の正規化 Haar 測度、Gibbs 測度、Gauss-law 物理 Hilbert 空間、真正 one-slab transfer を保持する。代理の作用素・独立 Haar に置換した相互作用模型・追加公理で質量ギャップを埋めない。

| 研究層 | 確立した成果と範囲 |
|---|---|
| 真正有限格子の物理 transfer | [AKL](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformTopOrthogonalCoercivityV5_PZ37AKL.lean)：体積に依存しない正の小結合区間で、正規化 transfer の全 top 固有空間の直交補上に収縮率 3071/3072、二次形式 coercivity 1/3072。完成OSや連続体の定理ではない。 |
| 真空・局所モード | [AOG](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformFirstModeMagnitudeV5_PZ37AOG.lean)：第一モードの重なりの体積一様上界。[AOU](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFirstRowRightSlopeLimitV5_PZ37AOU.lean)：固定体積での第一Haar行応答の右側極限。 |
| 真正 OS 境界像 | APL–APW：真空重み付き挿入の有限体積での厳密正値性、中心化 OS 像の構成、物理 sector 因子化と境界実現の条件付き接続。 |
| 時間移動の定義域 | [APZ](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalSupportBudgetTransportV5_PZ37APZ.lean)・[AQC](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSNullDescentV5_PZ37AQC.lean)：支持が正半領域内に留まる場合の局所時間移動、Gibbs反射内積、二重支持予算付き零方向降下。 |
| 真正相関の減衰 | [AQJ](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSConnectedGeometricV5_PZ37AQJ.lean)・[AQK](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSRelativeHorizonV5_PZ37AQK.lean)：Dobrushin 閾値・有限支持予算の下での幾何上界と、相対前因子が有界である場合の有限時間収縮。 |
| 具体的四辺の励起 | [AQN](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSFourEdgeCenteredRayV5_PZ37AQN.lean)：正の結合における非零の中心化 OS 像、支持辺数 ≤ 4、体積一様な分子ノルム上界、一次元方向上での単射性。 |
| 真正 OS 分母の定量化 | [AQO](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSQuantitativeEndpointTensorV5_PZ37AQO.lean)：端点テンソルによる具体的な有限体積下界。 |
| 試験ベクトルの一様下界 | [AQP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2b302a130419ec95d290bb472a4d3cd8ef992a43/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalVacuumWeightedProbeUniformNormV5_PZ37AQP.lean)：独立認証済み・未マージ。任意の有限体積と非負結合、実係数での真空重み付き二モードノルム下界。 |

## 3. 最新の数学的成果 — AQO / AQP

固定した有限体積 H と結合 β において、T を真正物理 one-slab 作用素、λ=‖T‖>0、Ω を正規化した真正物理真空、a_q を第一モード係数1・定数側係数 q の真正二モード観測量、w=a_q Ω を物理 Hilbert 空間の乗算像とする。U は真正 Gibbs 中心化 OS 境界像である。

**AQO（正式統合）** — [PR #7062](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/7062)、[CI #45894555500](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45894555500)、11,607 / 11,607 jobs、13 / 13 公理監査。APP の正しい中心化係数 q=q_C を使用して、真正境界 Haar L² 端点テンソルとの内積 J を構成した。β>0 で

$$ J=c_H\,\lambda_H^H\langle T_H w_H,w_H\rangle>0,\qquad (J/\|w_H\|)^2\leq\|U_H\|^2. $$

ここで c_H は真正 Wilson 分配関数の逆平方根である。独立認証済み leaf の正式統合 tree は認証 tree と一致し、[CI #45897012142](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45897012142) で再ビルドなしの成果物引継ぎも成功した。

**AQP（独立認証・統合待ち）** — [PR #7066](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/7066)、Sandbox [CI #45901268256](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45901268256)、独立 [CI #45902581226](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45902581226)。真正四辺 cyclic holonomy の一辺 Haar 更新、真空の局所 Harnack 比、積 Haar 更新恒等式を接続し、β≥0・任意 q について

$$ \boxed{\|w_{H,\beta,q}\|^2\geq e^{-16\beta}(1+q^2)\geq e^{-16\beta}} $$

を検証した。固定 β（または β の有界区間）で H に依存しない正の下界であり、真空密度全体を体積一様な定数に置換していない。ただし w の下界だけから U の体積一様な下界は得られない。

## 4. 現在のボトルネック

β>0・q=q_C の AQO の等式を次の3因子に分ける。

$$ \frac{J_H}{\|w_H\|}=\underbrace{c_H\lambda_H^{H+1}}_{P_H}\underbrace{\frac{\langle T_Hw_H,w_H\rangle}{\lambda_H\|w_H\|^2}}_{R_H}\underbrace{\|w_H\|}_{N_H}. $$

| 因子・証明義務 | 現況 |
|---|---|
| N_H：真空重み付きノルム | AQP 独立認証済み。固定 β で N_H ≥ exp(-8β)。 |
| R_H：相対転送二次形式 | 各有限体積の厳密正値性は AQO/APL。H 一様な正の下界は未証明。AQR の研究候補。 |
| P_H：分配関数正規化因子 | 真正分配関数を保った H 一様な正の下界は未証明。 |
| U_H：真正 OS 初期相関 | 有限 H の非零性・下界は AQO。H 一様な正の下界は未証明。 |
| 完成OS・連続体 | 非自明性、正しい定義域・半群、体積/格子間隔の極限と Hamiltonian gap の最終接続は未解決。 |

3因子それぞれの一様下界は十分条件となる研究経路であり、必要条件とは断定しない。積全体を直接下から評価する別経路も残す。

## 5. 保存している no-go 定理

- [APX](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalPositiveTimeHalfTurnObstructionV5_PZ37APX.lean)・[APY](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalCompletedOSVacuumLineObstructionV5_PZ37APY.lean)：有限周期格子で同じ正半領域代数への全非負整数時間移動共変性を課すと、完成境界像が真空線へ退化する条件付き障害。
- [AQG](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSReflectedCorrelationThresholdV5_PZ37AQG.lean)：Haar 作用素ノルム上界単独では非零初期値の厳密収縮閾値を認証できない。
- [AQK](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSRelativeHorizonV5_PZ37AQK.lean)：絶対幾何減衰上界とlog-convexityだけでは、初期相関に対する一様な相対収縮を導けない（スカラー反例）。
- [AQL](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSRelativeAmplitudeFiberV5_PZ37AQL.lean)・[AQM](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSCenteredNullFiberV5_PZ37AQM.lean)：定数シフト・存在する場合の非零OS零方向は中心化相関を保存しても raw 振幅を非有界にできる。有限次元の選択部分空間での coercivity は境界readの単射性と同値。

これらは使用した仮定・界面・評価法に対する定理であり、Yang–Mills 自体の不可能性を示すものではない。

## 6. 検証方法と研究の進め方

固定ソース・既存定理の型と依存の照合 → CodeAI 候補 → GitHub 隔離 Sandbox の直接Lean・公理監査 → 実Lean MCP → 合格した同一blobを別runnerの独立CIで再認証 → exact source/test-merge tree 照合 → Formal統合 → 認証済み成果物の安全な引継ぎ。

候補失敗・インフラ障害・未認証・認証済み・正式統合を区別する。仮定を弱めない。新規公理・sorry/admitを導入しない。公開rootに未認証の定理を追加しない。文書のみの変更にLean再ビルドは要求しない。CIの成功は監査した定理の範囲に限られ、外部の専門家による査読済みを意味しない。

- [ROADMAP — 次の証明義務](ROADMAP.md)
- [Formal ソース（観測時の固定HEAD）](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/d401555b432add745150c1c28d3e54a0fae59e64/MGAP4D/MathlibAnalytic)
- [AQP 独立認証済みソース（未マージ）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2b302a130419ec95d290bb472a4d3cd8ef992a43/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalVacuumWeightedProbeUniformNormV5_PZ37AQP.lean)
- [従来 README 全文の保存コピー](docs/archive/2026-11-27-pre-refresh/README.md) / [更新前の固定版（元の相対リンク付き）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/bcea883b55142c8c53c51271bb8861107813519b/README.md)

研究記録は削除せず、旧文書は内容・Git blobを変えずに保存した。本ページは現況の入口として再構成した。

# P4-Q2-PZ37AJH — 真正元Wilson transfer反復による全top／追加top残余の厳密上界

2026年11月10日 JST。機械検証の唯一の定理正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。この文書はLean4の形式証明そのものではなく、機械検査とsource来歴の記録である。

- [定理PR #6596](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6596)：**MERGED**。
- [統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/76bca4c6b505dc5506696c95dbd0d71ea422fe8c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceTransferPowerTopBudgetV5_PZ37AJH.lean)。
- 新規Lean leaf：`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceTransferPowerTopBudgetV5_PZ37AJH.lean`。**304行追加、既存ファイル変更・削除0**。元の物理定義・source・β仮定・Haar測度・Hilbert空間・正規化Wilson transfer・top eigenspace・選択top固有ベクトル、Lean/mathlib pin・公開root・CI workflowはすべて不変。

## 1．元対象と条件

各有限 `H : ℕ`、`β : ℝ`（`0 < β`）に対し、同じ真正SU(2) Gauss-law物理Hilbert空間上の元中心化ZW源 `f₀,H`、正規化物理one-slab Wilson transfer `S_H,β`、その**全**top固定固有空間 `F_H,β = ker(S_H,β − I)`、正準直交射影 `Q_H,β`、既存選択単位top固有ベクトル `Ω_H,β`、真正Haar定数単位ベクトル `c_H` をそのまま使用する。

既存証明から使用する事実は、transferの実Hilbert対称性、全top eigenspaceの固定点性、正準Hilbert直交射影の縮小性、AJFの全top二乗ノルム分解、AJGのHaar定数方向中心化である。**top一次元性やc_H∈F_H,βは仮定しない。** 既存作用素は正・コンパクト・ノルム1であり、full-top直交補の有限体積縮小率は1未満であるが、後者をH一様とは扱わない。

## 2．新たにLean4で形式証明した評価

任意の自然数 `n` と元source `f₀,H` について：

\[
\boxed{ Q_{H,\beta}(S_{H,\beta}^{n}f_{0,H})=Q_{H,\beta}f_{0,H} }
\]
\[
\boxed{ \|Q_{H,\beta}f_{0,H}\|^2 \le \|S_{H,\beta}^{n}f_{0,H}\|^2. }
\]

全top射影の反復不変性は、単一の選択top固有ベクトルだけでなく**全**真正top空間について成り立つ。

AJFの追加top残余
\[
r_{H,\beta}=Q_{H,\beta}f_{0,H}-
\langle f_{0,H},\Omega_{H,\beta}\rangle\Omega_{H,\beta}
\]
についても、任意の `n` で
\[
\boxed{\|r_{H,\beta}\|^2 \le
\|S_{H,\beta}^{n}f_{0,H}-
\langle f_{0,H},\Omega_{H,\beta}\rangle\Omega_{H,\beta}\|^2}
\]
を証明した。これは**真正元Wilson作用素に依存する上界**であり、`r=0` や任意のH一様に小さいことの証明ではない。

一方、AJGの選択top定数偏差
\[
D_{H,\beta}=1-|\langle\Omega_{H,\beta},c_H\rangle|^2
\]
に関して形式証明できる作用素依存情報は
\[
\boxed{1-\|S_{H,\beta}^{n}c_H\|^2\le D_{H,\beta}.}
\]
**向きは下界である。** したがって選択top方向とHaar定数方向の*近さ*を結論する上界ではない。下界を上界として誤用しない。

## 3．AJA真正正Haar-L²証明書との接続・未達部分

既存AJAの真正正証明書
\[
C_{H,\beta}=m_{H,\beta}^2\operatorname{Measure.real}\mu_H
\{B:u_{H,\beta}(B)<-m_{H,\beta}\}>0
\]
を変更せず、**別途実際に**
\[
\|S_{H,\beta}^{n}f_{0,H}\|^2<C_{H,\beta}
\]
が得られた場合に限って、元ZW正規化source像の全top直交成分が非零という条件付き定理を追加した。

この厳密不等式を満たす `n` または数値的・解析的上界は**構成していない**。とりわけ `n=1` の条件は、元AJAの `C≤‖S f₀‖²` と両立しない。有限反復の上界が既存のHaar証明書より小さいことを証明しない限り、無条件の励起sector非零性には昇格できない。元のAJG予算 `‖f₀‖²D+‖r‖²<C` 自体も未証明のまま保持する。

## 4．実際の新規Lean宣言・公理監査

| 宣言suffix | 内容 |
|---|---|
| `realHilbert_symmetric_fixedSubspace_starProjection_power_eq` | 全top固定空間への射影が全自然数冪で不変 |
| `realHilbert_symmetric_fixedSubspace_projection_norm_sq_le_power` | 全top射影二乗ノルムの反復source上界 |
| `realHilbert_symmetric_fixedSubspace_power_inner_eq` | 任意のtop証拠との内積保存 |
| `realHilbert_fixedUnit_deviation_ge_transferPower_norm_deficit` | 真空偏差の反復ノルム欠損による下界 |
| `p4Q2PZ37AJH_originalSourceTop_eq_transferPowerTop` | 真正source全top射影の反復不変性 |
| `p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower` | 真正source全topの上界 |
| `p4Q2PZ37AJH_selectedVacuum_deviation_ge_constantPowerNormLoss` | 選択top真空偏差の必要条件 |
| `p4Q2PZ37AJH_extraTop_norm_sq_le_transferPower_selectedResidual` | 真正追加top残余の上界 |
| `p4Q2PZ37AJH_originalOrthogonal_ne_zero_of_transferPower_budget` | 真正Haar証明書に対する条件付き非零性 |

**全9宣言に実際の `#print axioms`** を配置。9／9とも `propext`、`Classical.choice`、`Quot.sound` の標準3公理のみ。新規 `sorryAx` はない。

## 5．source／test-merge／squash受領とCI

| 対象 | 検査結果 |
|---|---|
| Exact-source CI | [#42704315781](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42704315781)、completed／SUCCESS |
| Scoped Lean dependency closure | **11,422／11,422 SUCCESS** |
| 新規宣言の公理監査 | **9／9、標準3公理のみ** |
| 変更Lean warning/error | **0／0** |
| 新規sorryAx | なし |
| 独立completion receipt | completed／SUCCESS。source_result=success、exact headとrun一致 |
| 認証source HEAD | `55160801c2dd9b9ec728bb6b20a08cefb9fcc3b5` |
| test-merge HEAD | `439915e6ae192dcf3e138e7206fe9ded45e9b487` |
| 正式定理squash／formal HEAD | `76bca4c6b505dc5506696c95dbd0d71ea422fe8c` |
| 3者の**共通Git tree** | `82a90be5f9336bbd60af44566370d73d58271a53`、完全一致 |
| 統合後push CI | [#42705520744](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42705520744)、**結果は別途完了観測まで未認証** |

Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。追加sourceだけを新leafとし、既存Lean証明・原始定義の削除も改変もなし。独立receiptはLean kernelの二つ目の証明ではなく、正確なCI完了通知である。

## 6．AJI以降に残す障害

- `D_{H,β}` の真正**上界**は未認証（AJHが与えたのは下界）。
- `E_{H,β}=‖r_{H,β}‖²` には反復sourceからの上界を得たが、AJA予算を下回る数値的・解析的証人は未構成。
- 全top eigenspaceの一次元性、元ZW源の無条件top直交性、無条件励起sector非零、正の体積一様下界、全物理Hilbert coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapはいずれも**未証明**。
- 次段は厳密な元Wilson kernel/正性/対称性/コンパクト性/積分のもとで、有限反復上界の数値的制御と、偏差上界を保証する追加*証明*が得られるかを調べる。仮定追加・緩和は禁止。

append-only／tighten-only／overwrite-forbidden／same-root。

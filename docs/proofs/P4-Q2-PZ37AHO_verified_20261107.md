# P4-Q2-PZ37AHO — 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。運用は append-only／tighten-only／overwrite-forbidden／same-root。元の完全 SU(2) Wilson one-slab kernel、元 ZW Gauss-law-centered physical source、元空間積 Haar 測度、固定結合 `beta0`、既存 AHN の source L¹・二次モーメント下界、全 Lean/Type 値証拠履歴を一切置換しない。

## 正本・実際のLean4検証

| 項目 | 結果 |
| --- | --- |
| [AHO定理PR #6460](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6460) | **MERGED** |
| 継承元AHN正本HEAD | `b2316d7300e24d23c3bb1ec7e849198f2e695345` |
| 最終AHO source HEAD | `e3209c2e791d44653903e87fdac697ac35e6013b` |
| test-merge SHA | `662960502dba9850a267afd4ea82ed5c3ccd9799` |
| AHO定理 squash SHA | `e985726a1acf71b5937f4fdd5f229ace7c9cb625` |
| source/test-merge/squash 共通 Git tree | `f09b020820523a87179704078b10463148db3087` |
| [Exact-source CI #42361194049](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42361194049) | **completed / SUCCESS** |
| Changed Lean job | `128369756933` completed / SUCCESS |
| 独立completion receipt | `128371244868` completed / SUCCESS |
| Lean依存閉包 | **11,376 / 11,376 SUCCESS** |
| 新規定理公理監査 | **4定理**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx`／変更AHO Lean warning/error | **なし／0／0** |
| 変更 | 新規Lean1ファイル、233追加行。過去Lean/物理定義/公開root/workflow変更0 |

固定 Lean は `v4.30.0-rc2`、mathlib は `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。GitHub MCP経由で実際の `lean-fast-check-log` artifact `13570101911` を回収し、`lean-fast.log` の末尾 `Build completed successfully (11376 jobs).`、4定理の `#print axioms`、`sorryAx` 0件、変更AHOファイルのwarning/error 0/0を解析した。依存元の既存warningを変更ファイルのwarningとして数えない。independent receiptの完了もGitHub MCPで確認した。新PRにより定理正本HEADは上記squash SHAへ更新された。

## CLOSED — 完全元Wilson核の結合定数Lipschitz

正本の原物理模型を一切変更しない。

```text
Cfg_H  = original finite spatial SU(2) slice
mu_H   = original normalized spatial product Haar
f_H    = original ZW Gauss-law-centered physical L² source
Msrc_H = integral_C |f_H(C)| dmu_H(C)
p_H    = original spatial plaquette count
C_H    = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
K_beta(A,B) = exp(-beta * originalFullOneSlabAction(A,B))
T_beta(B)   = original complete one-slab transfer of f_H at coupling beta
beta0       = log(3/2) / 64
```

`C_H` は既存 `PeriodicHypercubicEvenSpecialUnitaryOneSlabKernelBetaLipschitz` が厳密に証明した、両端空間 Wilson half-weight を含む**元の完全 one-slab 作用**の有限H上界である。元kernelの `beta` 微分と平均値定理で得られた**既証明の**点ごとの不等式

\[
|K_\gamma(A,B)-K_\beta(A,B)|\le C_H|\gamma-\beta|
\quad (\beta,\gamma\ge0)
\]

を元物理sourceの真正Haar積分に適用した。 `AEV_real_signedWeightedIntegral_absVariation` を使い、符号付きsourceを `|f_H|` で上から押さえる。したがって任意の有限H、任意の元空間境界B、任意の `beta,gamma≥0` について

\[
\boxed{
|T_{H,\gamma}(B)-T_{H,\beta}(B)|
\le C_H|\gamma-\beta|M_{\rm src,H}
\le {p_H C_H\over2}|\gamma-\beta|
}
\]

がLean4で形式証明された。後半は AHJ の元Haar source `Msrc_H≤p_H/2` によるものである。AHNの既証明 `(3p_H/8)\,\kappa(1/96)^{p_H}\le Msrc_H` と二次モーメント下界も保持されるが、**これらだけからtransfer下界を新たに主張しない**。

## CLOSED — 真正符号付きsource–transfer積の結合定数感度

元AGNの点ごとの `|f_H(B)|≤p_H/2` を上式に合成し、

\[
\boxed{
|f_H(B)T_{H,\gamma}(B)-f_H(B)T_{H,\beta}(B)|
\le L_H|\gamma-\beta|,\qquad
L_H={p_H\over2}\,C_H M_{\rm src,H}
}
\]

を証明した。正部分への置換や別のkernelは行っていない。

## CLOSED — 固定結合の近傍で同じ真正境界の符号整合が持続

元AHKの既証明で、`beta0>0` において

\[
\exists B\in\mathrm{Cfg}_H,\qquad
a_H(B):=f_H(B)T_{H,\beta_0}(B)>0.
\]

この**同じB**を固定して

\[
q={a_H(B)\over2}>0,\qquad
\delta={q\over 1+L_H}>0
\]

と置く。結合定数 Lipschitz 不等式を用いると、**すべての** \(\gamma\ge0\) について

\[
\boxed{
|\gamma-\beta_0|<\delta
\Longrightarrow
f_H(B)T_{H,\gamma}(B)>q>0
}
\]

となる。したがって固定正結合の近傍で、符号整合が**同じ真正空間境界B**において保持される。これは有限Hの局所的な強化である。B、q、delta は実際の元物理量により定義できるが、このLean定理から**実行済みの数値境界や数値transfer符号枝は抽出されていない**。

## OPEN — 元sourceの二次モーメントからtransferの数値下界へ

AHNで得た真正source二次モーメントの正の具体的下界は、source自体が消えないことを保証する。しかし AHО は元Wilson核の結合定数の変動上界と、既存AHKの**定性的な** \(f_H T_{\beta_0}>0\) witness を組み合わせたものであり、\(a_H(B)\)、\(q\)、\(\delta\) の絶対数値評価には到達していない。

次段は、元完全Wilson核の明示的な小結合展開・元source Haar平均0・真正二次モーメント・時間方向crossing作用の共分散・高次残差評価を、元模型を保持したまま区別して形式化する。その際、source二次モーメントを**根拠なくtransfer下界へ乗じない**。真正AGP符号表の実数値実行、正負両符号殻、H一様coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills質量ギャップはいずれも未証明である。

[AHO Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e985726a1acf71b5937f4fdd5f229ace7c9cb625/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullKernelBetaStabilityV5_PZ37AHO.lean)。

この正式記録は新規Markdown1件のみの追補であり、旧README/ROADMAPや全過去定理を改変しない。Docs-onlyのためStrict Leanを起動しない。

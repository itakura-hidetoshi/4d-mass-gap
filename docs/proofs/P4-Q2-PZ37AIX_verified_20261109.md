# P4-Q2-PZ37AIX — 元の正規化余裕の正結合window一様減衰

2026年11月9日 JST。正本: `itakura-hidetoshi/4d-mass-gap` / `formal/real-hilbert-uniform-coercive-strong-limit`。

Lean形式成果物: [定理PR #6566](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6566)（MERGED）、[統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/84b822848e825c8aa46aefc416af3864b1b39259/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedMarginCouplingWindowV5_PZ37AIX.lean)。説明文は形式定理を越えた証明の代替ではない。

## 1. 元の物理対象と条件

元の完全SU(2) Wilson作用、両端の空間halfweight、真正空間リンクHaar確率、符号付きZW物理L²源、AIGの元の負余裕とその厳密負領域、既存のGauss-law物理transferを一切変更していない。新しい物理作用素・新規測度・新しい源・共通Hilbert空間を導入しない。Hにより境界空間と物理Hilbert空間は異なる。

元の有限Hについて

\[
p_H=24(H+1)^3,\qquad
P_{H,\beta}=\text{既存の物理one-slab transfer},\qquad
\lambda_H(\beta)=\|P_{H,\beta}\|>0,
\]
\[
m_H(\beta)=
\frac{\delta_H(\beta)}{\lambda_H(\beta)}
\quad\text{（既存AIG余裕の既存物理ノルム正規化）}
\]

とする。新規leafは7件の定理のみ、定義の追加は0件である。

**量化条件:** 固定した実数 \(a>0\)、有限の実数 \(b\) と、各有限Hで \(a\le\beta\le b\) を満たす実結合 \(\beta\)。非空windowを用いるときは通常 \(a\le b\)。固定区間から外れる任意の \(\beta_H\) には今回の結論を適用しない。

## 2. 新しく形式証明した定理

AIWで証明済みの真正正規化余裕

\[
0<m_H(\beta)
\le \frac{\beta}{8}p_H^2e^{-\beta p_H},
\qquad\beta>0
\]

を使う。元のplaquette数 \(p_H>0\) と指数の単調性から、**同じHで許される全結合について**

\[
\boxed{
0<m_H(\beta)\le\frac b8 p_H^2e^{-a p_H}
\qquad (a\le\beta\le b,\ a>0)
}
\]

を得る。上界のH依存は既存AITの \(p_H^2e^{-a p_H}\to0\) から消失するため、

\[
\boxed{
\forall\eta>0\;\exists N\;\forall H\ge N\;
\forall\beta\in[a,b],\qquad 0<m_H(\beta)<\eta.
}
\]

特に**体積依存結合列** \(\beta:\mathbb N\to\mathbb R\) がすべてのHについて \(a\le\beta_H\le b\) を満たすなら、

\[
\boxed{m_H(\beta_H)\to0}
\]

であり、この同じ元の証明書について体積一様な正の下限は存在しない。これは固定結合だけを個別に選んだ結果ではなく、同一window全体の共通cutoffを構成した結果である。

またこの共通cutoffで、**既存の**正規化物理作用素 \(N_{H,\beta}=P_{H,\beta}/\lambda_H(\beta)\) は \(\|N_{H,\beta}\|=1\) を保ち、

\[
\left\{B:
  \frac{T_{H,\beta}f_{0,H}(B)}{\lambda_H(\beta)}
  <-m_H(\beta)\right\}
 =
\{B:T_{H,\beta}f_{0,H}(B)<-\delta_H(\beta)\}
\]

が元の境界空間の集合として正確に一致する。ここでの点wise評価はAIWで固定した連続積分代表についてであり、L²同値類の任意代表に点wise等式を与えない。

一方、全境界で証明できる真正源像上界は

\[
\left|\frac{T_{H,\beta}f_{0,H}(B)}{\lambda_H(\beta)}\right|
\le\frac{p_H}{2}e^{\beta p_H}
\le\frac{p_H}{2}e^{b p_H}
\]

であり、これは体積とともに増大し得る。**実際の正規化源像の一様減衰は導かない。**

## 3. 未認証と障害の保持

今回証明したのは **元のAIGのnormalized certificate-scale** の正結合windowにおける一様消失である。以下は別の未解決課題として維持する。

- \(\beta_H\to0\) を含む任意体積依存結合への拡張（下限 \(a>0\) がない）。
- 上限 \(b<\infty\) のない結合列への本評価の拡張。
- \(\beta_H\) が変化しても元の全余裕負領域が一様に半Haarを占めるかどうか（AITは固定結合のeventual結果であり、ここへ無条件に貼合しない）。
- 正規化源像の実振幅の消失、より深い負領域の不存在、top固有空間と元の源の関係、励起sectorの正規化coercivity、Hをまたぐ共通Hilbert空間極限、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gap。

局所証明が自動的に大域のスペクトル結論を与えるわけではない。

## 4. Lean形式宣言の全7件

元の名前空間: `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`。

| 定理suffix | 内容 |
|---|---|
| `p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope` | window共通上界 |
| `p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope_tendsto_zero` | 真正体積関数の極限 |
| `p4Q2PZ37AIX_originalNormalizedMargin_window_eventually_small` | 全結合に共通cutoff |
| `p4Q2PZ37AIX_originalNormalizedMargin_couplingSchedule_tendsto_zero` | 任意のwindow内結合列の減衰 |
| `p4Q2PZ37AIX_originalNormalizedMargin_couplingSchedule_noPositiveFloor` | 元の証明書に正の体積一様下限なし |
| `p4Q2PZ37AIX_originalNormalizedMargin_window_with_physicalOperator` | 同じcutoffでノルム1・元の負領域保存 |
| `p4Q2PZ37AIX_originalNormalizedSource_windowAmplitudeEnvelope` | 実源像の正直な非減衰上界 |

各定理について完全修飾名の `#print axioms` を実行し、source全文と公理出力を照合した。使用公理は `propext`、`Classical.choice`、`Quot.sound` のみ。新規公理、未証明プレースホルダー、unsafeの導入はない。

## 5. 固定環境と独立ファイル

- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- `autoImplicit false`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。
- 新規leaf: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedMarginCouplingWindowV5_PZ37AIX.lean`。
- 直接import: `MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSpatialMeanNormalizationV5_PZ37AIW` のみ。
- 新規leafは206行追加／削除0、7定理・追加定義0。元のLeanファイル・imports先・公開root・manifest・toolchain・workflowは変更していない。

## 6. Exact-sourceと統合後pushの独立実認証

| 項目 | Exact-source | squash後自動push |
|---|---|---|
| CI run | [42579467910](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42579467910) | [42580324130](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42580324130) |
| event / conclusion | pull_request / SUCCESS | push / SUCCESS |
| exact checkout源 | `12519eb5e3fc2b3e6b146ae7b85c652717d6203a` | `84b822848e825c8aa46aefc416af3864b1b39259` |
| 主Lean job | `129034518628` SUCCESS | `129037228662` SUCCESS |
| 独立receipt job | `129036169010` SUCCESS | `129038890166` SUCCESS |
| 依存閉包 | 11,412 / 11,412 SUCCESS | 11,412 / 11,412 SUCCESS |
| 公理出力 | 7/7、標準3公理のみ | 7/7、標準3公理のみ |
| error / sorryAx / 新規warning | 0 / 0 / 0 | 0 / 0 / 0 |
| GitHub artifact ID | `13657140695` | `13656393744` |
| ZIP bytes | 133,142 | 132,948 |
| ZIP SHA256 | `9005690e52a99a67f6b3b0141de7085cc1743305839528eeec7793bb85361fb8` | `ce4afd72e697b264b2b8633d894b52c81baf0fa467b00da69d026eda91d1cde3` |
| 展開log bytes | 1,995,492 | 1,995,488 |

GitHub MCPで主jobの完了実ログと独立receiptを照合し、artifact ZIPを実際に取得してSHA256を検算し、展開した `lean-fast.log` の全7公理出力・ビルド成功・エラー・warningを再走査した。依存warning 624行と新規leaf warning 0件は区別する。補助監査は別kernelによる新規証明を意味しない。

```text
[mcp-receipt] event=pull_request exact_sha=12519eb5e3fc2b3e6b146ae7b85c652717d6203a source_result=success run=42579467910 attempt=1
[mcp-receipt] event=push exact_sha=84b822848e825c8aa46aefc416af3864b1b39259 source_result=success run=42580324130 attempt=1
```

## 7. Git来歴と同一性

| 項目 | SHA |
|---|---|
| 開始canonical formal HEAD | `a60ee07d3acb8f983ef9ffae19616c5e7a07f54f` |
| 認証source | `12519eb5e3fc2b3e6b146ae7b85c652717d6203a` |
| 実test-merge | `be500806e19a9651a2990ca67b6c693717a925ea` |
| 定理squash | `84b822848e825c8aa46aefc416af3864b1b39259` |
| 共通Git tree | `28ecc5480bfde0da3625da11c18bf24c520762a4` |
| 新規Lean Git blob | `c5d76d268f8932a031c27c21c331b68528ef671e` |

Source/test-merge/squashのtree一致、全新規Lean bytesとblob一致、squash親が開始formal HEADであること、base→squash差分が追加ファイル1件のみであることを照合した。以後のformal/docsとmain/docsは定理の同一性を保持する追記のみとし、文書専用PRからStrict Leanを手動起動しない。

## 8. 次段

AIY候補: 実際の正規化ZW源像の真正L²振幅を、元の積分代表・既存Gauss-law physical norm・測度に接続して評価する。top固有空間への直交性や、変動結合の半Haar一様性は必要な証拠なしに仮定しない。

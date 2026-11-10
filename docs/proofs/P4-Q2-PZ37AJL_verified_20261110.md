# P4-Q2-PZ37AJL — 真正Wilson有限冪の選択top偏差と二種類の追加top残余への厳密収束

2026年11月10日 JST。Lean4定理の唯一の正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。本書は一次ソース・実検証・Git来歴の記録であり、記録本文そのものを証明とは扱わない。

[AJL定理PR #6610](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6610) **MERGED**。[統合済みLean leaf](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/a2fc5d9f25d8e551364812d2375fbb59bf8ee636/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPowerSelectedTopResidualLimitV5_PZ37AJL.lean)。

## 1. 元の物理的定義・固定条件

固定有限体積H∈ℕとβ>0の元の完全SU(2) Wilson one-slab、Gauss-law実物理Hilbert、両端halfweight、積Haar、正規化元物理transfer S、元の中心化符号付きZW源 f₀、Haar定数単位方向c、選択top単位ベクトルΩを保持する。全top固定空間 F=ker(S−I)、その正準射影Q、直交補制限Rは元の物理定義のまま。

AJIの固定H,βにおける実証済み `‖R‖<1` と `Sⁿx→Qx` を利用する。top一次元性、`Sc=c`、追加top残余の消失、体積一様の収縮率を仮定しない。根拠はAJI/AJJ/AJKのLean定理であり、本文の直観は形式結果と区別する。

## 2. 認証済み数学的結果

二つの別個の残余を

```text
rᶜ = Qc − ⟨c,Ω⟩ Ω
rᶠ = Qf₀ − ⟨f₀,Ω⟩ Ω
```

とする。AJLは、実Hilbertの一般定理とその真正元Wilson物理への適用として、任意の固定H,β>0に対して

```text
lim_{n→∞} ‖S^(n+1)c  − ⟨c, Ω⟩ Ω‖ = ‖rᶜ‖
lim_{n→∞} ‖S^(n+1)f₀ − ⟨f₀,Ω⟩ Ω‖ = ‖rᶠ‖
```

および、両辺の **ノルム二乗** を取った列の同じ対応する極限を形式証明した。

一般Hilbertにおける証明の経路は、AJIの全top射影 `Qx` への強収束から固定ベクトル `⟨x,ω⟩ω` を引く写像の連続性、ついでノルム／二乗の連続性を適用すること。物理適用ではHaar定数cと元中心化ZW源f₀を個別に指定し、既存AJJ・AJFの**異なるType値残余定義**へ一致させる。

**重要な非主張：** 極限は一般には0ではない。`‖rᶜ‖=0` や `‖rᶠ‖=0`、`F` の一次元性、元AJA厳密Haar-L²予算を満たす有限冪の存在、H一様coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapを証明していない。

## 3. Lean成果物と6宣言の監査

新規Lean leaf 1件：`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPowerSelectedTopResidualLimitV5_PZ37AJL.lean`。**207行追加・既存ファイル変更削除0**。Lean v4.30.0-rc2、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、root、物理source/kernel、workflowは不変更。

| 宣言suffix | 論理内容 |
| --- | --- |
| `realHilbert_selectedPowerDeviation_norm_tendsto_ajl` | 一般実Hilbertの選択方向を引いた有限冪ノルムの全top残余への収束 |
| `realHilbert_selectedPowerDeviation_sq_tendsto_ajl` | 同ノルム二乗の収束 |
| `p4Q2PZ37AJL_originalHaarConstant_powerDeviation_norm_tendsto` | 元Haar定数側の極限 |
| `p4Q2PZ37AJL_originalSource_powerDeviation_norm_tendsto` | 元中心化ZW源側の極限 |
| `p4Q2PZ37AJL_originalHaarConstant_powerDeviation_sq_tendsto` | 元定数側の二乗ノルムの極限 |
| `p4Q2PZ37AJL_originalSource_powerDeviation_sq_tendsto` | 元ZW源側の二乗ノルムの極限 |

全6宣言の実行時`#print axioms`を設置。修正済みCIの実公理出力は `propext`、`Classical.choice`、`Quot.sound` の標準3公理のみ。新規`sorryAx`なし。

## 4. 失敗・修正の形式来歴

初回source `e0f84237d98267e17a7b96e33204ec34e9946dfa` に対する [CI #42743082760](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42743082760) は **completed／FAILURE**。実ログには42行などの `Unknown identifier Tendsto` と、後続の `H` 未束縛、unknown free variable連鎖が出た。Leanの`autoImplicit=false`では未開放名を勝手な暗黙変数として補完できない。

AJIの依存Leanファイル全文中の名前空間使用と比較し、新規leafの `open Filter` 欠落を原因として特定した。**定理文・証明本体・仮定は不変更**のまま `open MeasureTheory` の直後に `open Filter` 一行を追加し、後続の連鎖エラーも解消した。初回の`#print axioms`が定理未成立のまま「does not depend on axioms」と表示した情報は、証明認証として採用しない。

## 5. Exact-source CIとマージ認証

| 項目 | 現在の認証 |
| --- | --- |
| 修正source | `49a7d20aff1483e84129e40bfb6b3dae64383732` |
| Exact-source | [CI #42743773415](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42743773415) completed／SUCCESS |
| Lean依存閉包 | **11,426／11,426 SUCCESS** |
| 実公理監査 | **6／6、標準3公理のみ** |
| 変更Lean warning／error | **0／0** |
| 新規sorryAx | なし |
| 独立completion receipt | completed／SUCCESS、exact sourceとrun一致 |
| 定理PR | [#6610](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6610) MERGED |
| 正式定理merge commit | `a2fc5d9f25d8e551364812d2375fbb59bf8ee636` |
| source vs merge | 比較で追加1コミット・**変更ファイル差分0** |
| 定理統合後push CI | **独立完了認証保留**。後段で再観測する |

CI completion receiptは原Lean kernel証明とは別種の運用上の確認記録として扱う。

## 6. AJMへ残す真正obstruction

AJLは**二つの追加top残余が残る正確な極限を同定**したが、それらがゼロか非ゼロか、十分小さいかを決めていない。元Wilsonの固有ベクトル選択と全topの追加多重度を混同できない。AJMでは、有限冪による予算判定の**逆方向の必要条件**、特に追加top残余の大きさが厳密AJA証明書の予算を不可能にするかを調べ、未知の真値をNO_DATAのまま保持する。

元AJA有限冪の厳密数値証人、励起sector無条件非零、体積一様coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapはOPEN。append-only／tighten-only／overwrite-forbidden／same-root。

## 7. 統合後push CIの独立再観測（追記）

定理PR #6610で正式統合したcommit `a2fc5d9f25d8e551364812d2375fbb59bf8ee636` について、[push CI #42755310628](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42755310628) は **completed／SUCCESS**。GitHub MCPで両ジョブと実ログを独立に確認した。

- `Changed Lean fast check` completed／SUCCESS。Lean依存閉包は **11,426／11,426 SUCCESS**。AJL新規6宣言の実公理出力は `propext`、`Classical.choice`、`Quot.sound` のみ、変更Lean warning/error 0／0、新規`sorryAx`なし。
- `Publish MCP CI completion receipt` completed／SUCCESS。実ログの受領書は `event=push exact_sha=a2fc5d9f25d8e551364812d2375fbb59bf8ee636 source_result=success run=42755310628 attempt=1`。同一コミットへの `chatgpt-ci-receipt/PR Lean Fast Check` は `state=success`。
- 第5節の「統合後push CI保留」は当時の観測であり、上の独立再観測により **認証済み**となった。receiptは別個のLean定理ではない。

AJLが同定した二つの追加top残余の極限がゼロ・十分小さいという主張、AJA厳密予算証人、top一次元性、H一様coercivity、Hamiltonian spectral gap、4D連続体mass gapは、いずれもなお **OPEN**。

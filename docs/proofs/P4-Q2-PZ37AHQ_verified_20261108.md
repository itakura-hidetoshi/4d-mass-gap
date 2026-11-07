# P4-Q2-PZ37AHQ — 正式証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。`main` は文書ミラー。運用：append-only／tighten-only／overwrite-forbidden／same-root。

## 正本とexact-source実検証

| 項目 | 確認結果 |
| --- | --- |
| [AHQ定理 PR #6466](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6466) | **MERGED** |
| 継承元AHP HEAD | `b4ed45d1c68e53a9e61277c3d93bc05d6c6667aa` |
| 最終source HEAD | `0f441c801ff9a4d92323f1617061d37960dea275` |
| 最終test-merge SHA | `c55d87719ab91d18f7c9e3c4ca27ab4f0051af67` |
| 定理squash／正本HEAD | `2320d2b768b0e8401c377696a1fc3ec6bf791bf2` |
| source/test-merge/squash Git tree | `b12d95ff46a4f3b2f10b8863178f6cd36fd03b29`（完全一致） |
| [最終exact-source CI #42396566781](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42396566781) | **completed / SUCCESS** |
| Changed Lean job | `128475157868` completed / SUCCESS |
| 独立completion receipt | `128476332174` completed / SUCCESS |
| Lean依存閉包 | **11,378 / 11,378 SUCCESS** |
| AHQ新規定理 | **14件**。標準公理 `propext`／`Classical.choice`／`Quot.sound` のみ |
| `sorryAx`／変更AHQ warning／error | **なし／0／0** |
| 実ログartifact | `13584200677` — `lean-fast.log` |
| 新規変更 | Lean1ファイルのみ。既存Lean／元物理source／Wilson核／Haar測度／root／workflow／pinsは不変更 |

固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。GitHub MCPで実際のCIジョブ完了、独立receipt、および最終artifactの全文ログを検証した。ログ末尾 `Build completed successfully (11378 jobs).`、AHQ全14件の `#print axioms` は標準公理のみ、`sorryAx` 0、変更AHQファイル warning/error 0/0。変更対象外の既存Lean warningは今回の変更warningに含めない。

## CLOSED — 真正crossing作用の中心化とHaar相関上界

元のSU(2) one-slab crossing作用 `Cross_H(A,B)` は、正規の空間リンク上のWilsonエネルギーの和である。元AHIの同一真正キャリア濃度 `card(Link_H)=p_H` および各一リンクWilsonエネルギーの既証明範囲から、全元配置 `A,B` で次を形式証明した。

```text
0 <= Cross_H(A,B) <= 2*p_H
|Cross_H(A,B) - p_H| <= p_H
```

元AHPの証明済み `integral_A f_H(A) dmu_H(A)=0` を使い、同じ元sourceと同じ元Haar積測度のもとで定数背景を**厳密に**引くことができる。

```text
X_H(B) = integral_A f_H(A) * Cross_H(A,B) dmu_H(A)
       = integral_A f_H(A) * (Cross_H(A,B)-p_H) dmu_H(A)
```

AEVの元signed-weighted-integral variation不等式と真正source L1質量 `Msrc_H` により、全有限H・全真正右境界Bで

```text
|X_H(B)| <= p_H * Msrc_H <= p_H^2/2
```

を形式証明。AHJの元source `Msrc_H <= p_H/2` を使用した。**`X_H(B)=0`、正負符号、独立Haar確率法則、仮想的なpositive sourceは一切仮定しない**。単純に `0 <= Cross <= 2p` の大きさを用いる評価と比べ、中心化により誤差上界の係数を半分にした。

## CLOSED — 元完全Wilson transferの一次近似と固定結合の有理予算

元AHPで証明された `|T_{H,beta}(B)+beta*(V_H+X_H(B))| <= E_H(beta)` を変更せずに継承し、上の真正相関上界から、全 `beta>=0`・全元境界Bで

```text
|T_{H,beta}(B)+beta*V_H| <= E_H(beta)+beta*p_H*Msrc_H
                              <= E_H(beta)+beta*p_H^2/2
```

を証明した。既存AHIの固定結合 `beta0 <= 1/128` を使って

```text
|T_{H,beta0}(B)+beta0*V_H| <= E_H(beta0)+p_H^2/256
```

を形式証明。`E_H(beta)` は元の完全one-slab作用の既証明 global budget `C_H` を使う真正二次Taylor残差 `(beta*C_H)^2*Msrc_H/2` そのもの。元AHNの正の二次モーメント下界 `F_H <= V_H` を残し、`T_{H,beta}(B) <= -beta*F_H + beta*p_H*Msrc_H + E_H(beta)` も証明した。

## Lean4エラーの構造と修正履歴

初回HEAD `47f47a65a4d02d52eb5d24410f84361fb4cdd3b8` のCI `#42373943927` は4エラー。ファイル全文・imports・依存定理・固定mathlibのAPIを確認して、(1) `simp`が `Finset.toList`と局所`Fintype`の濃度表示を異なる形まで展開した、(2) `abs_sub_le`は中間点を含む3引数型、(3)(4) `add_le_add_left`と`add_le_add_right`の加算順を混同したことを特定した。証明目標や物理sourceを変更せず修正。

2回目HEAD `ca6eecbdf341a3d69b2f15a2b79a2036a7e278a1` のCI `#42396028879` では後者3エラーが消え、唯一の残差は `Fintype.card Link = Fintype.card Link` の**異なる局所インスタンス**の同一視問題だった。既存AGNと同じ `Fintype.card_eq_nat_card` で両方を共通 `Nat.card` へ正規化して修正。3回目の最終HEAD `0f441c801ff9a4d92323f1617061d37960dea275` はLean・全14公理監査・変更warning/error 0/0を通過した。修正で公理・追加仮定・`sorry`・物理定義差し替えは導入していない。

## OPEN — 真正Haar直交性と固定β0の符号

今回示したのは `|X_H(B)|` の**一様上界**であり、真正4リンク空間プラケットと時間1リンクcrossing項のHaar直交性 `X_H(B)=0` は未証明。`p_H^2/256` と二次残差の和がAHNの正の二次モーメント項より小さいことも未確認であり、固定β0での元transfer符号、両符号殻、数値評価済みAGP真Haar表、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは証明していない。

次段AHRは、元空間プラケットの4リンクType値とcrossing一リンクの同時Haar積分において、残る未積分リンクを明示し、真正な独立性／Haar直交性の範囲とobstructionを証明する。元物理作用や元Haar法則を別の模型に置き換えない。

[AHQ Lean正本全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2320d2b768b0e8401c377696a1fc3ec6bf791bf2/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCenteredCrossingHaarBudgetV5_PZ37AHQ.lean)

この記録は新規Markdown1件のdocs-only追補であり、Strict Leanを新たに起動しない。

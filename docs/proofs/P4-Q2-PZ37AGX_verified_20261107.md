# P4-Q2-PZ37AGX 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラー。

## Exact-source検証

| 項目 | 確定 |
| --- | --- |
| 定理PR | [#6409](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6409) **MERGED** |
| 検証source HEAD | `7336525b72476c900cfd2ea3ed1a8670e4553ee3` |
| test-merge SHA | `b2de7b4609b4a65b8fe40bd3d93608888374742f` |
| canonical squash SHA | `ae20f39068fc0c3282b68ec3ca256cb261303bf3` |
| 共通Git tree | `635250d72a630d93fd18537f4f12e5fe0d3b8b35` |
| [exact-source CI #42297186825](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42297186825) | workflow completed/SUCCESS |
| Changed Lean job | `128165389119` completed/SUCCESS |
| Lean依存閉包 | **11,359/11,359 SUCCESS** |
| 新規公理出力 | **6宣言：`propext`・`Classical.choice`・`Quot.sound` のみ** |
| `sorryAx`／変更Lean warning/error | **なし／0/0** |
| 独立completion receipt job | `128168101270` completed/SUCCESS |
| 変更 | **新規Leanファイル1件、146行追加・削除0** |

固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。既存Lean・物理量・workflow・公開root・pinは変更しない。今回の検証はChanged Lean依存閉包であり、別のStrict Lean/Governance workflowの実施を意味しない。

## CLOSED — 真正Borel格子に有限最大値が存在する

AGU `precisionGridData H R eps` が保持する**同じ**元AGH空間Borel格子について、元物理的SU(2)の定数単位配置を与える。その格子の `hPartition` からセル添字 `Fin grid.n` の存在を得て、`(Finset.univ : Finset (Fin grid.n)).Nonempty` を構成した。空のセル添字集合に対して捏造した最大値を仮定しない。

AGWで既に証明された、元AGNの実際の各中心値幅の厳密な有理式

`width_i = |s_H(C_i)|*(kernelWidth_i+floorWidth/2)`

をその有限添字集合で `Finset.sup'` し、

`etaMax_H,d,B,m,n = max_i width_i`

を定義した。格子d・右境界B・m,nに依存する**実際の中心誤差**であり、新たな精度oracleではない。

## CLOSED — 各元AGN中心値幅を同じ最大値が包含

既存AGWの厳密な中心幅等式と、固定mathlibの `Finset.le_sup'` から、

`forall i, (AGN_originalIntegrandInterval center_i B).upper - .lower ≤ etaMax_H,d,B,m,n`

を証明。さらにAGNの元中心値区間は真正original continuous integrandの実値を挟むため、各幅は非負。格子の実際の非空添字を取り、`etaMax≥0` を得た。式は元B・source・kernel・floorを保持している。

## CLOSED — 外部eta仮定なしで元AGP raw／AGU final区間幅へ

AGVの既証明区間幅評価に、上記の実際の `etaMax` とその証拠をそのまま渡した。任意H、正有理R,eps、元AGL有理座標を持つ右境界B、m,n（n>0）に対して、選択された同じAGUデータに関し、

[
\boxed{
\mathrm{width}(I_H)\le
\eta_{H,R,\varepsilon,B,m,n}^{\max}
+2L_H(m)R+2M_H(m,n)\varepsilon
}
]

を形式証明。前段AGVの外部 `forall center, widthCenter≤eta` 入力は**AGXの定理の仮定ではなくなった**。元signed transfer、真正Haar法則、cellwise min/max、tighten-only交差を変更せず、余分なセル数倍率を含まない**最大値**で評価する。

## OPEN — etaMaxの任意精度化、計算性、物理的符号

`etaMax` は真正選択格子上の有理数だが、格子の選択は一般に古典的・非計算的であり、定義だけから数値表が実行済みとは言えない。**etaMax→0は未証明**。AGWの厳密分解 `|s|*(kernelWidth+floorWidth/2)` を使い、AGK結合幅・AGJ Taylor指数幅・AGM clipped kernel幅・AGN floor幅を全中心で一様に制御するのが次のAGY以降の課題。真のtransferの非零符号、二閾値殻、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップ、具体的大体積数値表はいずれも未解決。

[AGX Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/ae20f39068fc0c3282b68ec3ca256cb261303bf3/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFiniteCenterMaximumV5_PZ37AGX.lean)。

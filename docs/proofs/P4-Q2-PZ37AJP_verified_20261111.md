# P4-Q2-PZ37AJP — 真正元Wilson二時点残余推定区間の漸近的鋭さ

2026年11月11日 JST。Lean4形式定理の唯一のcanonical正本は \`itakura-hidetoshi/4d-mass-gap\` の \`formal/real-hilbert-uniform-coercive-strong-limit\`。本書は形式定理と認証来歴の説明記録であり、文章自体はLean証明ではない。

## 1. 変えなかった物理構造

固定有限 H∈ℕ と β>0 ごとに、元SU(2) Wilson両halfweight one-slabから構成した正規化物理transfer \`S\`、真正Gauss-law実Hilbert空間、符号付き中心化ZW物理源 \`f₀\`、既存の選択単位top固有ベクトル \`Ω\`、**全**top固有空間 \`F\`、その正射影 \`Q\`、全top直交補への元制限作用素 \`R\` を維持する。\`q=‖R‖<1\` は各固定H・βについて既に証明されている事実であり、Hに一様な条件には置き換えない。

元AJAの正のHaar-L²予算 \`B=m²·Measure.real μ({u<−m})\` も既存のまま利用する。以下はすべて真正元中心化ZW源についての表現であり、代用源・代用測度・新規物理仮定を導入しない。

## 2. 今回の形式証明の数学的到達点

\`α=inner ℝ f₀ Ω\`、\`r²=‖Qf₀−α•Ω‖²\`、\`D_n=‖S^n f₀−α•Ω‖²\` と置く。AJOとAJNの正規直交分解およびAJIの真正全top射影への収束から、新たに

\`\`\`text
L_n = (D_(n+2) - q² D_(n+1)) / (1-q²)
L_n ≤ r² ≤ D_(n+2)                        (n≥0)
lim_(n→∞) D_(n+2) = r²
lim_(n→∞) L_n = r²
\`\`\`

をLean核で形式証明した。\`1−q²>0\` は既存の固定有限体積の縮小定理から従い、推定量の分母は正である。

元AJA厳密予算の \`‖Qf₀‖²=α²+r²\` に対し、以下の**条件付き**判定が得られる。

- \`‖Qf₀‖²<B\` が独立に成立するとき、十分大きな自然数nについて必ず \`α²+D_(n+2)<B\`。
- \`B<‖Qf₀‖²\` が独立に成立するとき、十分大きな自然数nについて必ず \`B<α²+L_n\`。

ここで「十分大きい」は \`∀ᶠ n in atTop\` の形式定理であり、具体的な数値nやそれを成立させる物理的証人は構成していない。**等号境界 \`B=‖Qf₀‖²\` は未決定**である。上側・下側の極限が一致しても、r=0やtop一次元性を証明したことにはならない。

## 3. 新規Lean4ファイルと依存

[定理PR #6628](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6628) MERGED。認証済み新規Lean leafは
\`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTwoStepAsymptoticBudgetV5_PZ37AJP.lean\`。
新規ファイルのみ（修正版304行）、既存Lean・物理定義・仮定・toolchain・workflow・rootは不変更。

新規2定義は \`p4Q2PZ37AJP_originalSourceSelectedSquare\` と \`p4Q2PZ37AJP_originalSourceTwoStepLower\`。新規5定理は以下。

1. \`p4Q2PZ37AJP_originalSource_selectedSquare_succ_tendsto_extra\` — 真正source有限冪残余二乗の極限
2. \`p4Q2PZ37AJP_originalSource_twoStep_posterior_interval\` — 真正二時点上下区間
3. \`p4Q2PZ37AJP_originalSource_twoStepLower_tendsto_extra\` — 下側二時点推定の極限
4. \`p4Q2PZ37AJP_originalSource_strictSmall_eventually_upperBudget\` — 厳密小予算からの後続十分判定
5. \`p4Q2PZ37AJP_originalSource_strictLarge_eventually_lowerObstruction\` — 厳密大予算からの後続必要障害

7宣言すべてに \`#print axioms\` を設置した。importsはAJO・固定Mathlibの\`Mathlib.Analysis.InnerProductSpace.Projection.Basic\`・\`Mathlib.Tactic\`。既存AJI/AJN/AJOの署名と物理接続を保持する。

## 4. 初回Lean failureと修正の構造理由

初回source \`467f82c87b2de03f6e88ffaff7dbd6cfb5ba7ad8\` の [Exact-source CI #42902166859](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42902166859) はFAILURE。真正大規模物理定義を含む二時点区間の証明で \`simpa\` が多数の定義を展開し、Lean \`whnf\` の390万heartbeat上限超過を生じた（145行）。エラーによる一時的な未完成証明を認証済みとは認めない。

新規AJP leafの当該証明部分のみを修正し、元のWilson作用素・Ω・Rを型付きの局所\`let\`として導入、\`change\`で対象を明示して、最後の交換法則の計算のみ\`ring\`へ限定した。定理文、物理仮定、元の元源、既存Leanファイルおよび固定環境は変更していない。

## 5. Exact-source認証・Git来歴

- 修正source HEAD: \`765126110300d387e9402f688c07ab27bacf3fa3\`。
- [Exact-source CI #42904188256](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42904188256): completed／SUCCESS。
- 実ログで変更Lean依存閉包 **11,430／11,430 SUCCESS**。
- 新規定義2＋定理5の **7／7公理監査**は \`propext\`、\`Classical.choice\`、\`Quot.sound\` のみ。
- 新規\`sorryAx\`なし、変更Lean warning／error 0／0。
- 同じHEADの独立completion receiptはcompleted／SUCCESS、GitHub status \`chatgpt-ci-receipt/PR Lean Fast Check\` success。
- PR #6628は**MERGED**。正式squash HEAD \`57cbb9c8dc338e54014bb2748bff1cc75781cf17\`。
- 認証sourceと統合後の新規Lean **Git blob**は同一 \`124591833461c10b50566cbb49650f98f764029a\`。
- 統合後push [CI #42905294183](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42905294183) は本節の記録時点でin_progress。ジョブcompleted／SUCCESS、実ログ、公理監査、独立receiptの再観測までは**統合後独立認証を保留**する。

固定Lean \`v4.30.0-rc2\`、mathlib \`5450b53e5ddc75d46418fabb605edbf36bd0beb6\`。独立receiptは二つ目のLean kernelによる別証明ではなく、実行完了受領である。

## 6. OPEN／研究の境界

(1) 元AJA正予算に対する具体的な真正有限冪の数値的証人、(2) 元ZW源の追加top残余の独立数値評価・消失、(3) \`B=‖Qf₀‖²\`等号境界の判定、(4) 全top一次元性、(5) 無条件励起sector非零性、(6) H一様coercivity、(7) Hamiltonian spectral gap、(8) 4次元連続体Yang–Mills質量ギャップは未証明。

次段AJQでは、数値的証人または等号境界に踏み込む独立の物理入力・署名・測定条件が存在するかを監査し、未知量を仮定で置き換えない。append-only／tighten-only／overwrite-forbidden／same-root。

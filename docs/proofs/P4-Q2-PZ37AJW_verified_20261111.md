# P4-Q2-PZ37AJW — 元Wilson AJA証明書とAJV q-free上界の真正比較障害

2026年11月11日 JST。**形式Lean4定理認証済み・canonical formalへMERGED**。同じ元のSU(2) Wilson/Haar模型で、各有限 `H : ℕ` と `β>0` のみについて述べる。

## 1. 正本・認証・来歴

- Repository: `itakura-hidetoshi/4d-mass-gap`。
- 唯一の定理正本: `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。
- Lean4定理 [PR #6643](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6643) **MERGED**（squash）。
- 認証source HEAD: `a7bad255ae2c080a9f78d0077975d3677d8babb5`。
- [Exact-source CI #42988068487](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42988068487) completed／SUCCESS。Lean依存閉包 **11,437／11,437**。変更ファイルwarning/error **0／0**。5件の`#print axioms`はすべて `propext`、`Classical.choice`、`Quot.sound` のみ。新規`sorryAx`なし。独立 `Publish MCP CI completion receipt` job completed／SUCCESS、exact source commit status `chatgpt-ci-receipt/PR Lean Fast Check` success。
- 正式formal squash HEAD: `c2b2c769dc31375768767cffc60469956ad9ede2`。
- 認証source／実test-merge／formal squash の共通 Git tree: `4108358f9c044f614dcc8436a184f5b22454500d`。
- 認証／mergeで同一の新規Lean blob: `2c555dbd368ff78051a45704f407d1e9a4746e1d`。
- 新規leaf `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAJAQFreeBudgetObstructionV5_PZ37AJW.lean`。GitHub差分 **221行追加・削除0**、Lean宣言5件、監査命令5件。既存Leanの内容、源、測度、root、workflow、toolchain・mathlib pin不変更。
- 統合後push [CI #42988868560](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42988868560) は、この文書の初版起草時点では独立最終照合待ち。認証source成功とは区別する。

## 2. 元模型・真正量

同一の元の物理空間で、
- `p_H>0`: 元plaquette数。
- `V_H=‖f_{0,H}‖²>0`: 元の中心化ZW符号付き源の真正Haar分散。
- `v_H>0`: AIKの元Haar箱有理分散下界。`0<v_H≤V_H≤p_H²/4`。
- `S_{H,β}`: 既存の元正規化SU(2) Wilson一時点transfer。
- `m_{H,β}>0`: AIWの**元**正規化負余裕。
- `u_{H,β}`: 既存の連続Haar積分代表。
- `R_{H,β}={B:u_{H,β}(B)<-m_{H,β}}`: 既存AIG/AIWの真正厳密負領域。
- `B_{H,β}=m_{H,β}²·Measure.real μ_H(R_{H,β})>0`: 元AJA Haar-L²証明書。
- `d_H(β)=βe^{−βp_H}v_H>0`: AJUが保持するAJT由来の真正物理一時点L²欠損下界。
- `c_{H,β}=(d_H(β)/2)²`: AJVのq-free分散補正。

## 3. 形式認証された比較

`t=βexp(−βp_H)` とする。固定mathlib `Real.add_one_le_exp` より `tp_H≤1`。AIWから `m≤tV_H/2`、AIKから `v_H≤V_H`、AISから `V_H≤p_H²/4`、真正Haar確率から `Measure.real μ_H(R)≤1`。従って `d=tv≤tV_H` であり、真の元AJA予算・AJV補正について

```text
B_H,β + (d_H(β)/2)^2
  ≤ (t V_H / 2)^2 + (t V_H / 2)^2
  = t^2 V_H^2 / 2
  ≤ V_H / 8
  < V_H.
```

が **全有限 H、全 β>0** について成立する。

よって厳密な**逆向き**比較

```text
B_H,β < V_H − (d_H(β)/2)^2
```

と、AJVで十分条件として使っていた

```text
V_H − (d_H(β)/2)^2 < B_H,β
```

の否定を**元の同一H、同一β、同じHaar・同じAJA予算**でLean4形式証明した。前者の厳密性は `V_H>0` から得る。元のAJA証明書が正である事実とは矛盾しない。

Lean新規5宣言:
1. `real_margin_defect_budget_eighth_bound_ajw`: 独立の実数代数予算補題。
2. `p4Q2PZ37AJW_originalNegativeRegion_realMeasure_le_one`: 真正Haar確率の上界。
3. `p4Q2PZ37AJW_originalAJA_add_qfree_le_eighth_variance`: 同じ元量での `B+c≤V/8`。
4. `p4Q2PZ37AJW_originalAJA_strictly_below_qfree_upper`: 厳密逆比較。
5. `p4Q2PZ37AJW_originalAJV_qfreeAJA_threshold_impossible`: 特定AJV十分条件の否定。

## 4. 実際の障害の意味・未証明範囲

この結果は、AJVの**粗い全top射影上界** `‖Qf₀‖²≤V_H−c` だけから元AJA小条件を導く方法が、元証明書に対して**決して成功しない**ことを確定する。しかし実際の `‖Qf₀‖²` がもっと小さい可能性は残る。

**証明していないこと：**
- `B_H,β≤‖Qf₀‖²`、あるいは真正有限Wilson冪 `‖S^nf₀‖²<B_H,β` の不存在。
- 真正有限冪 `n` の無条件数値証人、AJUの別個の`q`依存`n=2`十分条件の真偽。
- 真正追加top残余ゼロ、top一次元性、無条件転送後励起sector非零性。
- 体積一様coercivity、Hamiltonian spectral gap、非自明連続体4次元Yang–Mills質量ギャップ。

**次段案:** AJXでは上界 `V_H-c` に依存しない、真正 `‖Qf₀‖²` または有限冪ノルムの直接的Haar積分／spectral評価を目標とする。今回の不可能性を無条件の質量ギャップ結論へ「降下」させない。

## 5. CI失敗と型付き修正の経路

初回commit `28afc539b3dbae7509539f04132f600f0d568f83` の [CI #42987088393](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42987088393) はFAILURE。新規leaf54行の`sq_le_sq₀`が生成した目標`(b*p)^2≤1^2`と宣言`(b*p)^2≤1`の間で`one_pow`簡約が必要だった。初回の失敗から回復した宣言に`sorryAx`が出ているため初回を認証扱いしない。

最終修正版では対象行で`simpa only [one_pow]`を明示し、**定理文・物理仮定・元依存署名・既存ファイルは変更せず**、新規leaf内の証明手順だけ修正。再実行source `a7bad255…` は固定Lean/kernelの11,437件すべて成功、5公理監査が標準3のみ、独立受領書成功。

Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

append-only／tighten-only／overwrite-forbidden／same-root。

## 6. AJW統合後pushの独立追認（同日追記）

[CI #42988868560](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42988868560) は `event=push`、`head_sha=c2b2c769dc31375768767cffc60469956ad9ede2`、**completed／SUCCESS**。正式mergeを正本として変更Lean依存閉包 **11,437／11,437 SUCCESS**。新規5/5公理監査は標準 `propext`、`Classical.choice`、`Quot.sound`のみ、`sorryAx`なし、変更AJW warning/error 0/0。独立の `Publish MCP CI completion receipt` jobはcompleted／SUCCESS、当該merge HEAD上の `chatgpt-ci-receipt/PR Lean Fast Check` statusもsuccess。前節の「push追認待ち」は起草時点の履歴として残し、本追記で完了を記録する。

この独立受領書はLean kernel証明自体ではなく、同一正式sourceが検証された実行時の来歴である。元AJA予算の正値と、AJV十分条件が全有限H・β>0で不可能という定理の射程を分離する。

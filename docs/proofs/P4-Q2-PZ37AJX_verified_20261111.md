# P4-Q2-PZ37AJX — 真正AJA Haar証明書の1/16上界と元Wilson有限冪の必要角度条件

2026年11月11日 JST。**Lean4形式定理認証済み・formal正本へMERGED**。各固定有限 `H : ℕ` と全 `β>0` の元SU(2) Wilson/Haar模型に限る。以下の記録は形式定理とCI来歴の説明であり、それ自体を形式証明としない。

## 1. 唯一の定理正本とCI

- Repository: `itakura-hidetoshi/4d-mass-gap`。
- Canonical branch: `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。
- 新規Lean leaf: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAJAAbsoluteSixteenthSectorCriterionV5_PZ37AJX.lean`。**326行追加・削除0**、既存Leanファイルを変更せず、9宣言・9 `#print axioms`。
- [定理PR #6646](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6646) **MERGED**。
- 最終認証exact-source HEAD: `8d0394673bbd7ab20c35e39a6ca4f6709cd61b00`。
- [Exact-source CI #42993769844](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42993769844) **completed／SUCCESS**。Lean依存閉包 **11,438／11,438**、9/9新規公理監査は `propext`、`Classical.choice`、`Quot.sound` のみ。新規`sorryAx`なし、変更AJX Lean warning/error 0/0。独立 `Publish MCP CI completion receipt` job completed／SUCCESS、exact-source commit status `chatgpt-ci-receipt/PR Lean Fast Check` success。
- 正式formal squash HEAD: `e552961d3533df32f653b4213443144120f413c2`。
- source、GitHub実test-merge、squashの共通 Git tree `e70ced55c1d6786da137728716e16d4ac7be953c`。同一AJX Lean blob `098176c09ba56886d388d1602ac3d07bb4806e9b`。
- 統合後push [CI #42994602655](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42994602655) は起草時点で独立追認待ち。exact-source成功とは区別して後続追記する。

固定Lean `v4.30.0-rc2`、固定mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。元のWilson one-slab物理作用素、両halfweight、Haar、中心化ZW源、AJA負領域とmargin、既存source・root・workflowはいずれも不変更。

## 2. 原物理量・新しい厳密上界

`p_H>0`: 元plaquette数。
`V_H=‖f_{0,H}‖²>0`: 元中心化ZW物理L²源の真正Haar分散。
`m_{H,β}>0`: 元AIW正規化負margin。
`R_{H,β}={B:u_{H,β}(B)<-m_{H,β}}`: 元AIG/AIWの同一Haar可測負領域。
`B_{H,β}=m_{H,β}²·Measure.real μ_H(R_{H,β})>0`: 元AJA真正正Haar-L²証明書。

既存AIWより `m≤(β exp(−βp_H))·V_H/2`。既存AISより `V_H≤p_H²/4`。元Haar確率は `Measure.real μ_H(R)≤1`。固定mathlib `Real.add_one_le_exp` から `βp_H exp(−βp_H)≤1`。これらを同じ有限H・β・元測度で合成して

```text
0 < B_H,β ≤ V_H / 16
```

を**無条件に**Lean4で形式証明した。AJWの `B+(d/2)²≤V/8` と別の、AJA予算単独についての上界である。こちらはAIK有理Haar分散下界 `v_H` もAJVのq-free源上界も必要としない。

## 3. 真正有限冪の必要条件（存在主張ではない）

元正規化Wilson transferを `S`、その**全**固定top空間を `F`、正準直交射影を `Q`、選択単位top方向を `Ω`、追加top残余を `r=Qf₀-⟨f₀,Ω⟩Ω` とする。

**別途、実際の真正元Wilson冪**で

```text
∃ n≥1, ‖S^n f₀‖² < B_H,β
```

が独立に立証された場合に限り、

```text
‖S^n f₀‖² < V_H/16,
‖Q f₀‖² < V_H/16,
⟨f₀,Ω⟩² < V_H/16,
‖r‖² < V_H/16,
‖Q⊥ f₀‖² > 15 V_H/16.
```

が同じ元物理Hilbert空間で成立する、と形式証明した。最後は元源の真正Pythagoras `V_H=‖Qf₀‖²+‖Q⊥f₀‖²` から導く。選択Ωと全topの同一視、top一次元性、追加top残余の消去は行わない。

また、**実際に** `V_H/16≤‖Qf₀‖²`、または同値な `‖Q⊥f₀‖²≤15V_H/16` が独立に立証された場合、同じ元AJA予算を下回る有限冪証人は不可能と形式証明した。

これは元Wilson有限冪の**必要な強い角度条件（源エネルギーの93.75%超がtop直交側）**であって、その角度条件が実際に成立するという無条件の物理主張ではない。仮に成立しても、それ単独で予算内証人は得られない。

## 4. Lean宣言9件・型検査経路

新規の一般実数代数補題 `real_margin_probability_budget_le_sixteenth_ajx` に続き、真正元量について `p4Q2PZ37AJX_originalAJA_certificate_le_sixteenth_variance`、power/spectral projection/selected overlap/extra top/excited energyの必要条件5件、および二つの条件付きno-witness障害定理を新規形式化した。

- 初回source `685062e668d4de787c43b3c05ebab2225488dbbc`、[CI #42991567848](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42991567848) FAILURE：直交Pythagoras箇所で巨大な物理定義を直接展開し、`whnf`が固定3900000 heartbeatに達した。後続unknown constantは派生エラーであり初回を認証しない。
- 2回目 `6c70e501b64b7bcf9d3cdc5140b64c4201584c4b`、[CI #42993022541](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42993022541) FAILURE：型付き局所 `S : Phys →L[ℝ] Phys` と `F : Submodule ℝ Phys` への分解によりタイムアウトを解消したが、`linarith`へ渡す`‖f₀−Qf₀‖²`と目的`‖Q⊥f₀‖²`の表記差が残存。
- 3回目 `8d0394673bbd7ab20c35e39a6ca4f6709cd61b00`：`F.starProjection_orthogonal_val`を明示して表記を接続。**[CI #42993769844](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42993769844) SUCCESS**、9宣言すべて標準3公理のみ、変更warning/error0/0。物理仮定も定理署名も一切弱めず、新規leafの証明手順だけ修正した。

## 5. 残るobstructionと次段

元AJAの `B≤V/16`、および有限冪証人の存在が**もたらす**必要な角度条件は認証済み。しかし実際の `‖Qf₀‖²<V/16` または `‖Q⊥f₀‖²>15V/16` が成り立つかは**NO_DATA／未認証**。したがって真正有限冪数値証人、追加top残余の無条件評価、top一次元性、無条件転送後励起sector非零、体積一様coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills質量ギャップはOPEN。

次段AJYは既存の粗い分散上界 `V−c` や必要条件の反復ではなく、元のWilson/Haar作用素・sourceの真の全top射影／有限冪ノルムを直接評価して `B_H,β` と比較する橋を優先する。

append-only／tighten-only／overwrite-forbidden／same-root。

## 6. 正式formal統合後pushの独立追認（同日追記）

[CI #42994602655](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42994602655) は `event=push`、`exact_sha=e552961d3533df32f653b4213443144120f413c2`、completed／SUCCESS。正式mergeを対象に **11,438／11,438 Lean依存閉包 SUCCESS**、AJX新規9/9公理監査は`propext`、`Classical.choice`、`Quot.sound`のみ、新規`sorryAx`なし、変更leaf warning/error 0/0。独立 `Publish MCP CI completion receipt` jobもcompleted／SUCCESS、exact-head commit status `chatgpt-ci-receipt/PR Lean Fast Check` はsuccess。この追記により第1節の当時の「push追認待ち」は完了した。receiptはLean証明自体とは別の実行時来歴である。

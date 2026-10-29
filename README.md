# MGAP4D

**Main-branch documentation mirror | 2026-10-29 JST.** Formalized four-dimensional Yang–Mills / genuine interacting Wilson SU(2) research in Lean 4 / pinned mathlib, by Hidetoshi Itakura.

## 最新の定理チェックポイント — 2026-10-29 JST · P4-Q2-PZ37ABO / ABO2 / ABO3 (#6016)

**文書ミラー同期元：** 正本の文書 [PR #6017](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6017)、squash [`3b168eb70e594c3719f3dac7f5fc9d6a76ae5600`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/3b168eb70e594c3719f3dac7f5fc9d6a76ae5600)。定理は引き続きformal正本上の #6016 に属する。

**唯一のLean定理正本：** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。[PR #6016](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6016) の検証sourceは [`511bd76e290972caec371b4672a210033436cfa7`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/511bd76e290972caec371b4672a210033436cfa7)、定理squashは [`75f0c61fb538bef71a34a6e544831f98e792bc2b`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/75f0c61fb538bef71a34a6e544831f98e792bc2b)。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。

**検証結果：** [exact-source CI #40869191576](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40869191576) は依存関係を含む対象ビルド **11005/11005 SUCCESS**。新規Lean 3ファイルのwarning/error **0/0**、公開定理17件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、独立completion receipt SUCCESS。既存Lean・元の物理模型・固定依存は変更しない。

CIのPR検証用checkout `a2f6b42bb211a9e56f9c90068efe1390d8699266` と検証sourceは、全ファイルtree `7145a3fdd255089ba3af1b1243fb42f2eb5193a2` が完全一致することも確認した。

### 真正四リンクの時間Wilson文字モードを導出

元の `χ=1−E_W=Re Tr/2`、`k_b=exp(−bE_W)`、正規化SU(2) Haar `μ`、ABNの実積分 `Z_b=∫k_b`・`N_b=∫k_bχ`・`r_b=N_b/Z_b` を用いる。4リンクで `ν=μ^4`、`W(x)=x₂⁻¹x₃⁻¹x₀x₁` とし、**実際の4個の時間因子** `K⁽⁴⁾_b(x,y)=∏ᵢ k_b(xᵢ⁻¹yᵢ)` に対して

`Q⁽⁴⁾_b f(y):=Z_b⁻⁴ ∫K⁽⁴⁾_b(x,y)f(x)dν(x)`

を考える。この `Z_b⁴` は4リンク時間因子のHaar質量であり、全物理転送ノルム `t` ではない。

4リンク上の中心化半エネルギーを `f₄(x)=(E_W(W(x))−1)/2`、実プラケットへの評価を `F_(H,p,b)(A)=(Q⁽⁴⁾_b f₄)(A∘edges_(H,p))` と定める。

| 閉じた結果 | 正確な範囲 |
| --- | --- |
| `∫k_b(x⁻¹y)χ(axc)dμ=N_bχ(ayc)`、逆向きには `χ(ax⁻¹c)→χ(ay⁻¹c)` | 任意の周囲のSU(2)群要素と全実数 `b`。Haar平行移動・文字の巡回性・反転不変性から証明。 |
| `∫K⁽⁴⁾_b(x,y)dν(x)=Z_b⁴`、従って `Q⁽⁴⁾_b1=1` | 同じ実時間因子と同じHaar質量で正規化。 |
| `∫K⁽⁴⁾_b(x,y)χ(W(x))dν(x)=N_b⁴χ(W(y))`、従って `Q⁽⁴⁾_b(χ∘W)=r_b⁴(χ∘W)` | 元の非可換な四辺の順序を保つ。固有関係を仮定せず、4回の真正一リンク積分から導出。 |
| 実際の任意の `H,p` で、空間Haarの `∫E_p=1`、`∫(E_p−1)²=1/4` | MYの真正四辺embeddingと元の向き付きWilsonエネルギー恒等式を使用。最小体積 `H=0` も含む。 |
| 実四辺で評価した伝送後文字は平均0・二乗モーメント `r_b⁸/4`、中心化半エネルギー `(E_p−1)/2` の伝送後は平均0・二乗モーメント `r_b⁸/16` | 完全な元の空間Haar参照測度上の恒等式。選んだ四辺の時間畳込みについての結果。 |
| `∫F_(H,p,b)(A)² dHaar_H(A)≥(b₀ exp(−2B)/4)⁸/16>0` | 指定した `0<b₀≤b≤B` で、全ての有限 `H` と真正 `p` に共通する下界。 |

証明ファイル：[ABO 一リンクの向き](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/75f0c61fb538bef71a34a6e544831f98e792bc2b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOneLinkCharacterConvolutionV5_PZ37ABO.lean)、[ABO2 四リンク積分](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/75f0c61fb538bef71a34a6e544831f98e792bc2b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFourLinkCharacterConvolutionV5_PZ37ABO2.lean)、[ABO3 真正プラケットへの輸送と分散](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/75f0c61fb538bef71a34a6e544831f98e792bc2b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPlaquetteTemporalHaarFloorV5_PZ37ABO3.lean)。

### 次のOPEN — 実際の相互作用する重みと符号付き物理GIへの接続

選択した四リンクの時間畳込み恒等式は閉じた。次に、全空間リンクにわたる時間因子の積からこの四辺への正確な制限・積分表示、遠方変数を積分して得る元の空間Wilson相互作用の実重み、その体積一様比較・下界を閉じる必要がある。続いてPerron半密度と二つのinteracting posteriorの符号付き対比、および全物理源の他プラケットとの相殺を制御する。

このHaar二乗モーメントを完全pair-Haar上の `A_p` や `G` と同一視しない。固定 `b>0`／`0<b₀≤b(H)≤B` でも、一様 `A_p≥α>0`、全物理Hilbert coercivity、共通positive-fine区間、E/F、H1–H4、OS/Wightman、連続体Yang–Mills質量ギャップはOPEN。ABMの上限のみの結合条件に対する障害とABLの有限体積正値性を保持する。

**以下のABN以前の「最新」「現行」とOPEN記述は当時の履歴として保持する。** 現在の到達点と量化範囲は本節による。README/ROADMAPの同期はdocs-onlyであり、Strict Leanを起動しない。

---


## 最新の定理チェックポイント — 2026-10-29 JST · P4-Q2-PZ37ABN / ABN2 (#6013)

**唯一のLean定理正本：** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。[PR #6013](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6013) の検証sourceは [`e71a43d39c9ed71e93a33c6953ce39205aa90719`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/e71a43d39c9ed71e93a33c6953ce39205aa90719)、定理squashは [`1aa3b282399c534f2aba7f9f97307726d4c7f5e0`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/1aa3b282399c534f2aba7f9f97307726d4c7f5e0)。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。

**検証結果：** [exact-source CI #40859191626](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40859191626) は **11003/11003 SUCCESS**。新規Lean 3ファイルのwarning/error **0/0**、公開定理24件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、独立completion receipt SUCCESS。文書同期は定理を追加しない。

**文書ミラーの同期元：** 正本のdocs-only [PR #6014](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6014)、文書squash [`288d4381efdc92eef29d46d698b8a773cfd9e2c8`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/288d4381efdc92eef29d46d698b8a773cfd9e2c8)。mainへの追加はREADME/ROADMAPだけで、Lean定理は正本に保持する。

### 元の一リンク時間Wilson核から閉じた下界

元の正規化SU(2) Haarを `μ`、元のWilsonエネルギーを `E`、文字を `χ=1−E=Re Tr/2` とする。実際の時間因子 `k_b=exp(−bE)` から、`Z_b=∫k_b dμ`、`N_b=∫k_bχ dμ`、`r_b=N_b/Z_b` を定義する。ここで `Z_b` は一リンクHaar質量であり、全物理転送ノルム `t` と区別する。

| 閉じた結果 | 正確な範囲 |
| --- | --- |
| `∫χ=0`、`∫χ²=1/4` と元の指数核から `b exp(−2b)/4≤N_b`、`b exp(−2b)/4≤r_b≤1` | `b≥0`。`b>0` なら `r_b>0`。`r_b` は全実数上連続で `r_0=0`。 |
| `T_bχ(a):=Z_b⁻¹∫k_b(g)χ(g⁻¹a)dμ(g)=r_bχ(a)` | 実際のSU(2)行列恒等式とHaar反転不変性から証明した一リンク畳込み恒等式。固有関係を仮定しない。 |
| `∫T_bχ=0`、`∫(T_bχ)²=r_b²/4` | 同じ元のHaar上での転送後文字モードの正確な分散。 |
| `c₀:=b₀ exp(−2B)/4>0`、`r_b≥c₀`、`∫(T_bχ)²≥c₀²/4>0` | 指定した `0<b₀≤b≤B` 全域に共通する明示的下界。体積パラメータを含まない一リンク量についての結果。 |
| `mλ‖v‖≤‖Q(W(v−cu))‖` とその二乗版 | 別の抽象補題。対称線形写像 `Q`、直交 `u,v`、`Qu=u`、`Qv=λv`、`0≤λ≤1`、`m≥0`、`⟨Wx,x⟩≥m‖x‖²` を明示した条件付き転送評価。 |

証明ファイル：[ABN係数](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1aa3b282399c534f2aba7f9f97307726d4c7f5e0/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTemporalCharacterTransmissionV5_PZ37ABN.lean)、[ABN2固有恒等式・分散](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1aa3b282399c534f2aba7f9f97307726d4c7f5e0/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTemporalCharacterEigenlawV5_PZ37ABN2.lean)、[二モード重み付き転送補題](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1aa3b282399c534f2aba7f9f97307726d4c7f5e0/MGAP4D/MathlibAnalytic/SymmetricTwoModeWeightedTransmission.lean)。

### 次のOPEN — 真正四リンクと相互作用する物理応答への接続

実際のプラケット四辺の時間畳込みへの固有恒等式の拡張、空間相互作用を積分した実重みの体積一様下界、Perron因子・二つのinteracting posteriorの符号付き対比との接続、全物理源の他プラケットとの相殺制御が残る。抽象補題の固有関係・重み下界を、完成した物理GIの事実として扱わない。

従って固定 `b>0`、または `0<b₀≤b(H)≤B` でも、元の完全pair-Haar上の一様 `A_p≥α>0` と、それによる一様 `G` の正の下界はOPEN。ABMの「上限のみの結合条件では一様絶対重なりを保証できない」という実モデル内の障害を保持する。全物理Hilbert coercivity、共通positive-fine区間、E/F、H1–H4、OS/Wightman、連続体Yang–Mills質量ギャップもOPEN。

**以下のABM以前の「最新」「現行」見出しとOPENは各時点の履歴として保持する。** 現在の到達点と量化範囲は本節による。元のWilson核・Perron真空・Gauss-law物理源・二つのposterior・完全pair-Haar・実転送ノルムと、全ての既存no-goを保持する。本同期はdocs-onlyでStrict Leanを起動しない。

---

## 最新の定理チェックポイント — 2026-10-29 JST · P4-Q2-PZ37ABM (#6010)

**唯一のLean定理正本：** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。ABMの記録は [PR #6010](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6010)、検証対象source [`965054a69cf1be2c66830648ea90cf81fb85db47`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/965054a69cf1be2c66830648ea90cf81fb85db47)、[exact-source CI #40853685655](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40853685655)。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。

**ABMの検証結果：** [exact-source CI #40853685655](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40853685655) は **11177/11177 SUCCESS**、変更Leanファイル1件のwarning/error **0/0**、新規公開定理12件の公理依存は `propext`・`Classical.choice`・`Quot.sound` の範囲、`sorryAx`なし、独立completion receipt SUCCESS。検証sourceと異なる定理squashは [`cf3d40e1dba4c2d8f718fb4525aa519351bc897c`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/cf3d40e1dba4c2d8f718fb4525aa519351bc897c)。後続の文書同期は定理を追加しない。

**文書ミラーの同期元：** 定理正本のdocs-only [PR #6011](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6011)（[README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2a56ce70aeb18fe85934a289fd26df2a5d8cbe69/README.md)・[ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2a56ce70aeb18fe85934a289fd26df2a5d8cbe69/ROADMAP.md)）。定理squashと文書同期SHAを区別し、mainへの追加は文書のみです。

### ABG以後の検証済み到達点 — ABH〜ABL

元のWilson核、Perron真空、Gauss-law物理源、実転送ノルム `t>0`、二つの相互作用するposterior、完全な元のpair-Haar `μ_H` を保持する。`C_p=t Δ_full Δ_local,p`、`c_p=∫C_p=tK_p`、`A_p=∫|C_p|`、`N_p=∫max(-C_p,0)` とし、`G=∫Δ_full²`、`Mcomp_p=∫(tΔ_local,p)²`、`E_b=exp(8b)(exp(16b)−exp(−16b))` を用いる。

| 段階 | 閉じた数学的内容 | 残る条件・範囲 |
| --- | --- | --- |
| [ABH #6003](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6003) | 真正の符号付き密度の連続性・積分恒等式と、完全な負部分を含む `c_p≥ρδ−η`。 | `H` 一様な事象質量 `ρ`、振幅 `δ`、負tail上界 `η`、正の余裕は別途必要。 |
| [ABI #6006](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6006) | `0<b(H)≤B` から実際の `E_b≤E_B` を証明。共通 `c_p≥κ>0` があれば `G≥4κ²/E_B²`。 | 結合上限が閉じるのはスケール上界。一様な正の交差相関は未導出。 |
| [ABJ #6007](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6007) | 真正の全プラケットBessel評価から `Σ Mcomp_p≤6E_b²`、`Σ c_p²≤6E_b²G`、`Σ N_p²≤6E_b²G`。 | 最初のbudgetは体積非依存。交差・負tailの評価には元の `G` が残る。 |
| [ABK #6008](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6008) | `A_p=c_p+2N_p`、`A_p²≤G Mcomp_p`、`Σ A_p²≤6E_b²G` と正確な相殺費用 `4N_p(N_p+c_p)≤G Mcomp_p−c_p²`。 | 独立の十分条件 `A_p≥α>0` が一様なら `G≥4α²/E_B²`。その証人の一様存在は別問題。 |
| [ABL #6009](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6009) | 真の二次モーメント `J_p=∫C_p²≤G(E_b/2)²`、`ΣJ_p≤6E_b²G`。各有限 `H,b>0` で正の `A_p` の証人を選び、開事象 `U_p={A_p/2<abs(C_p)}` を構成し `μ_H(U_p)≥A_p²/(E_b²G)>0`。 | 同じ事象でfull/localの両GI応答が非零。一様な事象質量や一様な `A_p` は未証明。 |

ABLは [CI #40849967415](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40849967415) が11,176/11,176 SUCCESS、変更Lean warning/error 0/0、7公開定理の `#print axioms` が標準3公理 `propext`／`Classical.choice`／`Quot.sound` のみ、`sorryAx` なし、独立completion receipt SUCCESS。検証sourceは `1352fa52f2068d4a420fb959bea05ddeea786f95`、squashは `10c81d79d36008cfff20cb53e0adc5d5e5292e5f`。

### ABM — 結合上限だけでは一様な絶対重なりを保証できない

`P_H` を真正のプラケット数、`M_H` を元の有限スラブ作用budgetとする。実際の応答の和と実転送ノルムの下界から、全ての真正の `e,p` について

`0≤A_(H,b,e,p)≤Q_H(b):=P_H exp(b M_H)(E_b/2)²`

を得る。体積因子は省略しない。固定した有限 `H` ごとに**このスカラー上界**は連続で `Q_H(0)=0` となるため、任意の `B>0` に対し、一つの厳密に正の結合族 `b(H)` を選んで

`0<b(H)≤min(B,1/(H+1))`、かつ `∀H,e,p, A_(H,b(H),e,p)<1/(H+1)`

とできる。従って、この族では `∃α>0, ∀H, ∃e,p: α≤A_(H,b(H),e,p)` が成立しない。一方、**同じ族の各有限体積にはABLの正の証人が存在する**。有限体積での正値性から共通の正の下限へ進む推論が、実際の相互作用するモデル内で破れる。

**更新されたOPEN：** 固定 `b>0`、または明示した `0<b₀≤b(H)≤B` の領域で、真正Wilsonから必要な一様下界を独立に導出する課題が残る。結合の正の下限を仮定するだけでは証明は閉じない。ABLの有限体積の正の事象比 `A_p²/(E_b²G)` は保持され、`A_p` の小ささだけではその比や事象質量の極限は決まらない。全物理Hilbert coercivity、共通positive-fine区間、E/F、H1–H4、OS/Wightman、連続体Yang–Mills質量ギャップはOPEN。

**以下のABG見出しにある「Latest」・「Current」および旧OPEN記述は、その時点の履歴として保持する。** 現行の到達点・量化範囲は本節による。旧PZ37ZAのno-goと全ての先行証明・履歴を残す。この文書同期はdocs-onlyであり、Lean定理を追加せず、Strict Leanを起動しない。

---

## Current authoritative theorem MIRROR — ABG / PR #6002 (2026-10-29 JST)

**This default `main` is documentation only.** The sole Lean theorem-bearing branch remains [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). Its current docs-only checkpoint was squash-merged by [#6004](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6004) at `46e70e32ab3af2b0506c0a9b57f0520d8e192b02`; **this is not a theorem-bearing SHA**. The latest *verified Lean theorem-bearing* [PR #6002 / PZ37ABG](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6002) was MERGED with tested source `f752141618f07a5d0c2b1cfd51c5cc2e60bb34d4`, theorem squash `6f68bc2989b7b46b2c3ef1702d521982ed37e521`. [Exact-head CI #40831840574](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40831840574): **11,171/11,171 SUCCESS**, changed Lean warning/error **0/0**, five public axioms reports with only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, independent completion receipt **SUCCESS**.

**New finite-volume ORIGINAL interacting Wilson facts after ABE:** [ABF/ABF2 #6001](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6001) proves `G=K_p+Σ_(q≠p)K_q` with the full signed residual and an actual plaquette `0<G/|P_H|≤K_p`. For the authentic physical one-slab transfer norm `t_(H,b)>0`, the local Gauss-law physical response satisfies `|t Δ_local,p|≤E_b/2` and complete original pair-Haar squared moment `Mcomp≤(E_b/2)²`; `E_b=exp(8b)(exp(16b)−exp(−16b))` depends on coupling, not spatial volume. [ABG #6002](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6002) proves genuine Cauchy–Schwarz `(tK_p)²≤G Mcomp≤G(E_b/2)²`, hence `G≥(tK_p)²/(E_b/2)²`, with an actual strictly positive certificate for EACH finite volume.

**CRITICAL OPEN:** no independently proved H-uniform `κ>0` with `tK_p≥κ`, and thus no uniform positive `G` yet. Positive local open Haar regions, same-sign events, and finite-volume `K>0` do not supply common amplitude, mass or control of the entire signed negative remote contribution. Remaining all-physical-Hilbert coercivity, common positive-fine interval, E/F, H1–H4, OS/Wightman and continuum 4D Yang–Mills mass gap remain OPEN. Historical PZ37ZA no-go remains. **No Lean files transferred to main.** The older ABE mirror checkpoint below is history; this docs-only mirror must not run Strict Lean.

---

## Historical Lean theorem mirror snapshot (2026-10-29 JST · PZ37ABE)

**This `main` branch is a documentation-only mirror, NOT the Lean theorem-bearing branch.** The sole authoritative Lean theorem source is [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). The authoritative [README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c570350ea9e876fb4e11f6fd947d1b759d5ab7c8/README.md) and [ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c570350ea9e876fb4e11f6fd947d1b759d5ab7c8/ROADMAP.md) were updated by **docs-only** [PR #5999](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5999); this docs SHA is **not** a new mathematical theorem.

| Verified source/evidence | Grounded conclusion |
| --- | --- |
| Latest **theorem-bearing PR** | [#5998 P4-Q2-PZ37ABE](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5998) **MERGED**, following [ABA/ABA2 #5994](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5994), [ABB/ABB2 #5995](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5995), [ABC/ABC2 #5996](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5996), and [ABD/ABD2 #5997](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5997), all MERGED on the theorem branch |
| Actual exact tested **PR source** SHA | [`25b6cc2bc6171603bfbb909a23918be3a25586b4`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/25b6cc2bc6171603bfbb909a23918be3a25586b4) |
| Last **theorem-bearing squash** SHA | [`75bee4a633cb1296a47a85624cd65a0917fddc8d`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/75bee4a633cb1296a47a85624cd65a0917fddc8d), confirmed equal to the authority HEAD immediately after PR #5998 squash |
| [Exact-source-head CI #40827511993](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40827511993) | **11,168 / 11,168 Lean SUCCESS**, changed Lean warning/error **0/0**, three new public `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, independent receipt **SUCCESS** |
| Latest authoritative **docs-only** squash | [`c570350ea9e876fb4e11f6fd947d1b759d5ab7c8`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/c570350ea9e876fb4e11f6fd947d1b759d5ab7c8) via #5999, advancing the document HEAD without modifying Lean sources |
| Pinned environment | Lean `v4.30.0-rc2` / mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

**Proven genuine finite-volume Wilson results:** ABA independently bounds the actual interacting-posterior FX variance by `(e^(16b)-e^(-16b))²`, without inherited JL `native_decide` axioms. At every finite `H,b>0`, the unchanged centered Gauss-law physical Wilson GI gap has a strictly positive genuine full pair-Haar unweighted squared moment on some real link. ABB constructs genuine positive-mass open pair-Haar GI events and two-sided comparison with GB's actual physical source projection. ABC splits the original GI gap exactly into all genuine centered spatial-plaquette contributions **without discarding the signed full residual**. ABD turns every selected centered plaquette into an actual Gauss-law physical Hilbert source and proves a same-sign positive-mass open context with the full source. ABE proves **`Σ_p K_(H,b,e,p)=G_(H,b,e)>0` on a selected actual link**, where `K=∫(original full physical GI gap)(actual centered local plaquette physical GI gap)d(original full pair-Haar)`. Hence at each finite volume some authentic plaquette has a strictly positive **integrated signed global physical cross-response**.

**Still OPEN:** `inf_H G_(H,b(H),e_H)>0`, a fixed-support original Wilson/Perron local response cylinder with a common positive Haar mass/amplitude, control of signed nonlocal remaining-plaquette response, all-Gauss-law physical-Hilbert coercivity, common positive-fine interval, matching endpoint E/F, all-depth H1–H4, OS/Wightman reconstruction and continuum 4D Yang–Mills existence with mass gap. For `0<b(H)≤B`, ABA has **already closed** the common *upper FX cap* `q_B=(e^(16B)-e^(-16B))²>0`, not the uniform positive GI moment. The PZ37ZA no-go concerns a **different compensated two-context quantity** and is retained.

**No Lean theorem files are moved to `main`.** Historical AAZ2 and earlier receipts remain below, explicitly retained as past checkpoints.

---

## Historical main-mirror checkpoint — AAZ2 (#5991), 2026-10-29

**Only authoritative theorem branch:** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). The default **`main` is a documentation mirror, not the theorem carrier**. In particular, merging documentation into this root cannot be interpreted as merging the current Lean proof library into `main`.

The complete current, audited repository-root documents on the **theorem branch** are:
- [Authoritative README — theorem-branch docs checkpoint `93a6a06c...`](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/93a6a06c18c7a66f9e29353ea7e2b034b90c0a33/README.md).
- [Authoritative ROADMAP — genuine outstanding analytic gates](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/93a6a06c18c7a66f9e29353ea7e2b034b90c0a33/ROADMAP.md).
- [Latest verified theorem-bearing PR #5991 (AAZ / AAZ2)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5991), preceded by [#5990 AAY](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5990) and [#5989 AAX / AAX2](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5989).

| Evidence / pin | Verified value |
| --- | --- |
| Latest **theorem-bearing squash** | [`20f910f54791d662b687965af231842a27f093b6`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/20f910f54791d662b687965af231842a27f093b6), equal to the theorem branch HEAD immediately after #5991 was merged |
| Exact **PR-source SHA** tested (different from squash) | [`d769e275d016b6645e924a116acb0d7653f7e9a0`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d769e275d016b6645e924a116acb0d7653f7e9a0) |
| [Exact-head CI #40814241452](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40814241452) | **11,159 / 11,159 SUCCESS**, both changed Lean files **0 warnings / 0 errors**, eight `#print axioms` with only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; independent completed MCP CI receipt **SUCCESS** |
| Pinned toolchain / mathlib (theorem branch) | Lean `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Current **docs-only** theorem-branch HEAD | [`93a6a06c18c7a66f9e29353ea7e2b034b90c0a33`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/93a6a06c18c7a66f9e29353ea7e2b034b90c0a33), PR [#5992](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5992); a later docs-only HEAD does **not** replace the theorem-bearing checkpoint |

### Precisely what is established

All of the following refer to the **original** finite-volume interacting Wilson SU(2) model with unchanged positive Perron vacuum, Gauss-law physical Hilbert source, **both actual normalized interacting one-link conditional posterior laws**, and original outer boundary pair-Haar integration. No independent-Haar posterior or artificial physical source is substituted.

For every finite volume `H` and frozen coupling `b>0`, let `V_H` be the original centered Gauss-law source, `C_H=4‖V_H‖²>0` its reference-Haar covariance, `e` an actual spatial link, `Δ_{H,b,e}(z)` the genuine signed GI expectation gap under the two interacting Wilson posteriors, and `Q_{H,b,e}(z)>0` their actual FX Haar-`L²` density-contrast variance. Define the **raw** one-link response and the **source-specific** Rayleigh value:

```text
J_(H,b,e) = ∫ [Δ_(H,b,e)(z)^2 / Q_(H,b,e)(z)] dμ_H(z)
R_(H,b)   = (4 / C_H) Σ_e J_(H,b,e)
G_(H,b,e) = ∫ Δ_(H,b,e)(z)^2 dμ_H(z)   (unweighted GI-gap moment)
```

**CLOSED, at each fixed finite `H,b>0`:** `R_(H,b)>0`, an actual `e` has `J_(H,b,e)>0`, and — newly in [AAZ #5991](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5991) — the centered `Δ` for some actual link is **not zero pair-Haar-almost everywhere**. Previous AAU results give genuine Wilson spatial-translation covariance, second-moment bound `M₂≤3R²` and positive link participation fraction `≥1/3`. These are *qualitative or relative* finite-volume results, not a volume-uniform positive Rayleigh constant.

**CLOSED combinatorial / conditional analytic steps:** The genuine spatial plaquette count equals link count (`P_H=L_H`), and `C_H≤24L_H`. Hence `J_e≥ε≥0 ⇒ R≥ε/18`. A measurable genuine pair-Haar event with mass `≥ρ`, `|Δ|≥δ` and `0<Q≤q` yields `J_e≥ρδ²/q`. AAZ2 further proves that under a pointwise actual FX upper bound `Q≤q`, the original unweighted square is automatically integrable and `G_e≤qJ_e`; consequently a **common** `G_e≥m>0` and **common** `q>0` would imply the **conditional** bound `R≥m/(18q)>0` across all volumes.

**OPEN and central:** Independently construct a positive volume-uniform `m` for the **actual GI unweighted second moment** on one authentic link per volume, and establish an appropriate common genuine FX upper bound `q` for the chosen frozen coupling schedule. Finite-`H` non-a.e.-zero `Δ` does **not** establish a uniform `m`. The existing JL fixed-coupling genuine FX bound has **five inherited legacy finite-grid `native_decide` axioms** in its original proof and is not silently imported into the standard-only AAZ2 theorem dependency path.

Even source-specific `R≥c` would not, alone, imply uniform coercivity for **all** Gauss-law Hilbert vectors; the common positive-fine interval, same physical endpoint E/F, all-depth results, H1–H4 and continuum 4D Yang–Mills existence/mass gap remain **OPEN**. The older [PZ37ZA #5935](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5935) disproved a **different** bounded compensated **two-context** `Q_GI/N_H` density floor; this is **not** a no-go for genuine full-link, full-boundary-pair-Haar physical GL mass.

**Recommended workflow:** read the fresh theorem-branch HEAD and its complete Lean sources/imports and authoritative exact-head CI receipts first; use the theorem-branch [ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/93a6a06c18c7a66f9e29353ea7e2b034b90c0a33/ROADMAP.md) for next mathematical gates. A documentation-only root update must not trigger or imply a new Strict Lean validation.

---

## Historical root documentation (2026-10-04; preserved)

The following original `main` README documents a prior #5077/#5078 stage. References below to “current” or “next” were true **at that dated checkpoint**, but are superseded as present-day status by the section above. Historical mathematical achievements, no-go statements and exact-head receipts are preserved, not deleted.

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

## Historical theorem status — through merged PRs #5077 and #5078 (2026-10-04)

The finite-volume positive-coupling transfer-gap route remains closed with the explicit volume/rank/scale-uniform constants

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||.
~~~

The q0 estimate is available on the full completed physical pair non-top sector.

The main change since the #5061 documentation checkpoint is that the old completed H1-D5 seam has not been revived. Instead the repository now has two weaker post-no-go routes:

1. a canonical projected/local-coefficient route (#5063--#5076), and
2. a stronger finite-dimensional SU(2) Gram--Schmidt route opened by #5077.

The second route is now the preferred next target because it can avoid any vacuum/top fidelity assumption. PR #5078 has already closed its pure finite-dimensional core: two real scalar constraints on a unit vector in Euclidean R^3 have a common normalized solution by rank-nullity.

A complete continuum four-dimensional Yang--Mills existence theorem and Wightman mass-gap theorem are not yet claimed.

## Authority checkpoint — 2026-10-04 JST

| Item | Authoritative value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing merge | 426ad4fe783d030a61687fbb123aca00b90a3d1d |
| Latest theorem-bearing branch tip | merge 426ad4fe783d030a61687fbb123aca00b90a3d1d; #5077 merged after #5078 and contains both theorem lines |
| #5077 | all SU(2) Wilson-energy Gram--Schmidt modes realized as physical endpoint pairs |
| #5077 validation | head aaa6d50c2da21461a76a6a0e6e2f9ee72b518998; run 37157037971 success; exact-head receipt success |
| #5078 | abstract Fin 3 two-functional unit-kernel selector |
| #5078 validation | head 61acb9b380ee3822e5574c1e9fd56e61cba5d64f; run 37156892868 success; exact-head receipt success |
| Pinned Lean | v4.30.0-rc2 |
| Pinned mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

The default branch main is not theorem authority. It is a documentation mirror.

Authority order is fixed:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

README / ROADMAP-only commits are docs-only and do not replace the latest theorem-bearing snapshot.

## Current claim boundary

### Closed

- beta = 0 physical transfer gap equals 1;
- positive-beta finite-volume coercivity;
- volume/rank/scale-uniform transfer-gap floor 1/3072;
- q0 = 3071/3072 and uniform q0^m decay;
- q0^m decay on the full completed physical pair non-top sector;
- one-dimensional finite physical top eigenspace;
- one-dimensional completed pair top-top block;
- scale-coherent projective L2 carrier;
- explicit SU(N) Wilson two-mode boundary representatives;
- H1-D4:
  independent endpoint gauge-fixed pair sector equals the completed physical pair carrier;
- positive-coupling SU(2) completed H1-D5 no-go;
- canonical projection of the actual centered pair to the physical non-top sector;
- theorem-generated nonzero projected centered excitation at every finite scale;
- common-projective embedding of projected non-top modes;
- fixed-mode infinite-subsequence extraction;
- exact rank-one top subtraction formula for projected common images;
- canonical-sign OS vacuum pair common-projective image equals constant one at every scale;
- pair-top convergence reduced to the scalar vacuum/top overlap criterion;
- stronger projected convergence criterion using only the local top coefficient;
- exact canonical OS-vacuum pair coefficient factorization through normalized positive-half transfer;
- exact one-slice formula for the local projected-top coefficient;
- all SU(2) Wilson-energy Gram--Schmidt modes realized as physical one-slice modes and physical endpoint pairs;
- the entire SU(2) Gram--Schmidt endpoint-pair family is orthonormal in pair Haar L2;
- the pure finite-dimensional #5078 selector: any two real linear functionals on Euclidean R^3 admit a common unit vector in both kernels.

### Not yet closed

- model-facing instantiation of the #5078 selector with the #5077 three-mode pair synthesis, OS-vacuum pairing and pair-top pairing;
- proof that the synthesized selector has exact unit pair norm and belongs to the completed pair non-top sector;
- projective strong convergence of that scale-dependent selected combination;
- coherence / strong convergence of evolved finite q0-controlled states;
- identification of a limiting discrete-time physical transfer on the nonzero continuum excitation;
- spacing-scaled physical-time dynamics;
- final OS Hamiltonian lower bound;
- Wightman / energy-momentum mass-gap theorem.

## 1. Finite-volume gap route

The finite-volume transfer analysis has already reached

~~~text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f),

1/2304 <= kappa_12(s,beta),

1/3072 <= physical transfer gap,

q0 = 3071/3072.
~~~

The corresponding top-orthogonal natural-power estimate is volume/rank/scale uniform.

The pair theory upgrades this to the full completed physical pair non-top sector.

This part is not the present bottleneck.

## 2. H1-D4 is closed

PRs #5022--#5029 prove

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

Consequences:

- the canonical-sign finite OS vacuum pair is in the completed physical pair carrier;
- independent endpoint gauge fixedness is no longer an assumption;
- pair-carrier membership does not need the old H1-D5 compatibility.

## 3. The old H1-D5 seam is formally refuted

PRs #5031--#5061 expose the old completed compatibility as far too strong.

The chain is

~~~text
completed H1-D5
  -> finite Wilson path identity
  -> one-slab power identity
  -> vanishing top-orthogonal restriction
  -> rank-one normalized one-slab transfer
  -> two-mode Wilson Gram degeneracy
  -> nontrivial feature-analysis kernel.
~~~

PRs #5058/#5059/#5061 prove that the concrete positive-coupling SU(2) two-mode sector has strictly positive crossing quadratic form and an injective physical feature-analysis map.

Therefore

~~~text
beta(n) > 0
  ->
not completed H1-D5 at scale n.
~~~

Do not reintroduce the old compatibility, or an equivalent vacuum/top alignment statement, under a new name.

## 4. Post-no-go projected route — #5063--#5069

### #5063

The actual vacuum-normalized centered pair receives an exact scalar top-pair expansion.

This gives a strictly weaker excitation-level scalar seam than H1-D5.

### #5064

The old SU(2) global vacuum/top alignment route is explicitly excluded.

### #5065

Define the canonical completed TopTop and nonTop projections of the actual centered pair.

The projected vector is unconditionally:

- in the completed physical pair carrier;
- top-top orthogonal;
- therefore controlled by the existing q0^m estimate.

### #5066/#5067

Nonzero projected excitation is reduced to a finite OS-vacuum / physical-pair-top overlap.

That overlap is theorem-generated strictly positive.

Hence at every finite scale at least one selected projected centered Wilson mode is nonzero and already receives q0^m decay.

### #5068/#5069

The projected modes are embedded into one common projective continuum L2 carrier.

An infinite increasing subsequence can be chosen on which one fixed mode label remains nonzero.

This closes the finite nonzero-q0 excitation existence problem without H1-D5.

## 5. Projective strong-convergence reduction — #5070--#5074

### #5070

The projected common image has the exact form

~~~text
centered image
  -
<top image, centered image> * top image.
~~~

Therefore no independent scalar-convergence proof is required if both moving vectors converge.

### #5071

The uncentered Wilson pair common image is eventually exactly one fixed continuum mode.

Centered convergence is reduced to the OS-vacuum pair image and pair-top image.

### #5072

The canonical-sign OS-vacuum pair common-projective image is exactly

~~~text
1
~~~

at every scale.

Thus the vacuum part of centered convergence is completely closed.

### #5073

For unit pair-top common images,

~~~text
pair-top image -> 1 strongly
  iff
finite vacuum/top overlap -> 1.
~~~

This yields one valid conditional route, but it is stronger than necessary.

### #5074

A weaker Hilbert-space lemma removes the need for convergence of the moving top direction:

~~~text
c_n -> c,
||t_n|| = 1,
<t_n,c_n> -> 0
  ->
c_n - <t_n,c_n> t_n -> c.
~~~

Therefore it is enough to prove the finite local projected-top coefficient tends to zero.

This local criterion is the preferred interpretation of the #5070 projection formula.

## 6. Local coefficient factorization — #5075/#5076

### #5075

For arbitrary physical one-slice endpoint vectors x,y,

~~~text
<v_OS, x tensor y>
  =
<v_OS, omega tensor omega>
  *
<S_half x, y>,
~~~

where S_half is the normalized positive-half physical transfer and omega is the normalized one-slice top mode.

The finite partition normalization cancels exactly.

No H1-D5 compatibility or vacuum/top alignment is used.

### #5076

For the explicit primary Wilson two-mode pair f_k tensor 1, the local projected-top coefficient has the exact one-slice form

~~~text
a_k
  =
alpha_k * delta
  -
gamma^2 * m_k,
~~~

with

~~~text
alpha_k = <omega, f_k>,
delta   = <omega, 1>,
gamma   = <v_OS, omega tensor omega>,
m_k     = <S_half f_k, 1>.
~~~

This removes pair-Haar geometry from the local-coefficient problem.

It is useful diagnostically, but the next preferred route no longer needs to prove gamma -> 1.

## 7. #5077 — infinite SU(2) Gram--Schmidt family realized as physical pairs

PR #5077 extends the kinematic input from two special modes to the full theorem-generated SU(2) Wilson-energy Gram--Schmidt family.

For every mode index k and finite scale n, the repository now has:

- an explicit primary-spatial-plaquette continuous Wilson Gram--Schmidt observable;
- a gauge-invariant physical one-slice L2 vector;
- an exact ordered endpoint-pair identification with a decomposable physical pair;
- membership in the completed physical pair carrier;
- orthonormality of the whole endpoint-pair family after transport to pair Haar L2.

Schematically,

~~~text
u_{k,n}
  in PhysicalPairCarrier,

<u_{i,n},u_{j,n}> = delta_ij.
~~~

This is the kinematic input needed for the new three-mode route.

## 8. Preferred next route: instantiate the #5078 selector on three #5077 pair modes

Take the first three orthonormal physical pair modes at scale n:

~~~text
u_0,n, u_1,n, u_2,n.
~~~

For coefficients c in R^3 define

~~~text
X_n(c) = sum_{k<3} c_k u_k,n.
~~~

Define the two real linear functionals

~~~text
L_vac,n(c) = <v_OS,n, X_n(c)>,

L_top,n(c) = <Omega_pair,n, X_n(c)>.
~~~

Combine them into

~~~text
L_n : R^3 -> R^2.
~~~

PR #5078 already proves the abstract rank-nullity statement needed here: two real scalar functionals on Euclidean R^3 have a common unit kernel vector. Therefore, after packaging L_vac,n and L_top,n as the two functionals required by #5078, one obtains c_n with

~~~text
L_vac,n(c_n) = 0,
L_top,n(c_n) = 0,
||c_n|| = 1.
~~~

Then

~~~text
x_n := X_n(c_n)
~~~

has all of the desired finite properties at once:

~~~text
||x_n|| = 1                 by orthonormality,

<v_OS,n, x_n> = 0           by construction,

<Omega_pair,n, x_n> = 0     by construction,

x_n in PhysicalPairCarrier  by #5077,

x_n in PairNonTop           by one-dimensional TopTop,

||S_pair,n^m x_n||
  <= q0^m ||x_n||
  = q0^m.
~~~

Because the vacuum coefficient is already zero, vacuum centering does not change x_n.

The remaining work in this section is model-facing: define the three-mode synthesis map from #5077, prove its exact norm formula from orthonormality, and instantiate #5078 with the two physical pairings.

This avoids:

- completed H1-D5;
- vacuum/top alignment;
- gamma_n -> 1;
- decay of the #5076 fidelity defect.

## 9. Expected projective compactness step after the three-mode selector

The coefficient vectors c_n lie on the unit sphere in R^3.

Finite-dimensional compactness should provide a subsequence

~~~text
c_{n_j} -> c_infinity,
||c_infinity|| = 1.
~~~

The SU(2) Gram--Schmidt projective-cylinder machinery already gives coherent continuum realizations of every fixed mode.

For the first three fixed continuum modes U_0,U_1,U_2, one should then obtain

~~~text
Embed(x_{n_j})
  ->
sum_{k<3} c_infinity,k U_k
~~~

strongly.

Because the continuum modes remain orthonormal,

~~~text
||sum c_infinity,k U_k|| = 1.
~~~

So the limiting excitation is automatically nonzero.

This is stronger than the older fixed-two-mode pigeonhole route because nonzero norm is built into the coefficient normalization.

## 10. What the three-mode route does not yet solve

Even after the initial nonzero strong limit is constructed, the dynamical identification remains open.

The finite estimate

~~~text
||S_n^m x_n|| <= q0^m
~~~

does not by itself define a continuum operator T or prove

~~~text
||T^m x|| <= q0^m ||x||.
~~~

The evolved finite states must first be shown to live coherently in the same projective carrier, or otherwise converge strongly to an identified limiting discrete-time dynamics.

This is the next H1-C3 layer after the three-mode selection and compactness steps.

## 11. H1-C3 — projective dynamics

Required sequence:

1. theorem-generate the three-mode unit selector c_n;
2. construct the exact finite non-top unit pair x_n;
3. extract a coefficient-convergent subsequence;
4. prove the projective image of x_n has a nonzero strong limit;
5. prove coherence / strong convergence of the evolved sequence S_n^m x_n for fixed m;
6. identify a limiting discrete-time operator T;
7. transport

~~~text
||S_n^m x_n|| <= q0^m
~~~

to the continuum limit.

Only after this step does finite q0 become a theorem about actual continuum discrete-time dynamics.

## 12. H2 — physical-time scaling

The fixed discrete factor q0 is not itself the continuum mass.

If lattice spacing a_n tends to zero, then for fixed t > 0,

~~~text
q0^floor(t/a_n) -> 0.
~~~

That is an instantaneous-collapse scaling, not a nontrivial strongly continuous physical-time semigroup.

The continuum-time layer needs a spacing-sensitive statement such as

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent generator / Dirichlet lower bound.

Existing rate and scaling modules remain downstream tools for this stage.

## 13. H3/H4 — OS Hamiltonian and Wightman mass gap

After projective dynamics and physical-time scaling provide actual continuum model data, the remaining route is

~~~text
continuum physical Hilbert space
  ->
strongly continuous contraction semigroup
  ->
self-adjoint Hamiltonian
  ->
vacuum-orthogonal spectral lower bound
  ->
positive mass gap
  ->
Wightman / energy-momentum mass-gap theorem.
~~~

Generic functional-analytic infrastructure is already substantial, but these model-facing identifications are not yet closed.

## 14. Lean / CI engineering rules

Current repository rules:

- fresh exact theorem-carrier SHA has highest authority;
- pinned Lean v4.30.0-rc2 and pinned mathlib API take precedence over current-master examples;
- inspect every changed Lean file, not only the first compiler error;
- distinguish theorem-bearing commits from docs-only commits;
- use exact-head CI receipts before theorem PR merge;
- do not rerun strict Lean for an unchanged exact head that is already GREEN;
- docs-only changes do not require a redundant strict-Lean rebuild;
- prefer explicit named parameters when section-variable inference is fragile;
- prefer direct theorem terms / simpa using when rw cannot match through coercions;
- avoid brittle change steps across definitional aliases;
- preserve the direction of inner-product symmetry lemmas explicitly.

## 15. Recent milestone ledger

| PR | Status | Contribution |
| --- | --- | --- |
| #5061 | merged | positive-coupling SU(2) completed H1-D5 no-go |
| #5062 | merged | docs refresh through #5061 |
| #5063 | merged | centered-pair scalar replacement for the failed seam |
| #5064 | merged | exclude old SU(2) vacuum/top alignment route |
| #5065 | merged | canonical physical non-top projection of centered pairs |
| #5066 | merged | reduce projected nonzero to finite vacuum/top overlap |
| #5067 | merged | prove projected centered excitation nonzero at every scale |
| #5068 | merged | common projective embedding of projected modes |
| #5069 | merged | fixed nonzero mode on an infinite increasing subsequence |
| #5070 | merged | projected strong-convergence factorization |
| #5071 | merged | centered-image convergence reduced to OS vacuum pair |
| #5072 | merged | canonical OS vacuum pair projective image is exactly one |
| #5073 | merged | pair-top convergence iff vacuum/top overlap tends to one |
| #5074 | merged | local top-coefficient convergence criterion |
| #5075 | merged | OS vacuum pair coefficient = overlap times normalized half-transfer coefficient |
| #5076 | merged | exact one-slice local projected-top coefficient formula |
| #5077 | merged | full SU(2) Gram--Schmidt Wilson family realized as physical orthonormal endpoint pairs |
| #5078 | merged | abstract Euclidean R^3 two-functional common unit-kernel selector |

## 16. Restart checkpoint

Latest theorem-bearing baseline before this docs refresh:

~~~text
426ad4fe783d030a61687fbb123aca00b90a3d1d
~~~

Latest theorem PR evidence:

~~~text
PR #5077 exact head:
  aaa6d50c2da21461a76a6a0e6e2f9ee72b518998

PR Lean Fast Check:
  run 37157037971
  completed / success

exact-head receipt:
  success
~~~

Read these files first for the current frontier:

1. PhysicalYangMillsWilsonVacuumNormalizedProjectedLocalTopCoefficientCriterion.lean — #5074
2. PhysicalYangMillsWilsonVacuumNormalizedPairPositiveHalfTransferRatio.lean — #5075
3. PhysicalYangMillsWilsonVacuumNormalizedLocalTopOneSliceFormula.lean — #5076
4. PhysicalYangMillsWilsonSU2GramSchmidtPairPhysical.lean — #5077
5. RealEuclideanFinThreeTwoFunctionalKernel.lean — #5078
6. SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt.lean
7. PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtCylinder.lean
8. PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadout.lean
9. the full physical pair non-top q0 receiver from #5006

Current restart target:

~~~text
THREE COHERENT ORTHONORMAL PHYSICAL PAIR MODES (#5077)
  +
ABSTRACT TWO-FUNCTIONAL UNIT-KERNEL SELECTOR (#5078)
  ->
instantiate with
  [vacuum pairing, pair-top pairing]
  ->
exact finite unit non-top excitation
  ->
existing q0^m receiver
  ->
coefficient-sphere subsequence
  ->
nonzero projective strong limit

THEN:
  evolved projective coherence
  ->
continuum discrete-time q0 dynamics

THEN:
  spacing-scaled physical-time rate

LATER:
  OS Hamiltonian
  ->
spectral / Wightman mass gap.
~~~


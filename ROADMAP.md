# MGAP4D mainロードマップ文書ミラー — ABX–ABY（2026-10-31 JST）

**唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。このmain文書追補は正本README・ROADMAP [#6038](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6038) の `344e3a857bea068a83e071d787cfcde56a42b9db` に基づき、ABX #6036およびABY #6037の形式化のscopeとOPENを同期するだけである。元のmain本文・全Lean・Wilson模型・正規化・pinは変更しない。

---

# MGAP4D — 最新定理正本ロードマップ（2026-10-31 JST／P4-Q2-PZ37ABX・ABY）

- **定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。
- **最新定理：** [ABX #6036](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6036)／[ABY #6037](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6037) **ともにMERGED**。ABX squash `72ea17713148f75bc59be714e0211a8b710e5a6d`。最新ABY squash＝マージ直後正本HEAD `e9641c02a2830455ac8fec3ce288561acf589914`。exact-source `6070d795822f9908b359d3e58bca63c43ca3b10a` のtree `49c34e6dbdc33a8b6f00fad606dd0ead73da35d1` と完全一致。
- **証明検証：** ABX [CI #41162615381](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41162615381) Lean **11,166/11,166 SUCCESS**、10公開定理、標準3公理のみ、sorryAx 0／warning・error 0/0、独立receipt [124424290535](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41162615381/job/124424290535) SUCCESS。ABY [CI #41165349729](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41165349729) Lean **11,168/11,168 SUCCESS**、16公開定理、標準3公理のみ、sorryAx 0／warning・error 0/0、独立receipt [124432651768](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41165349729/job/124432651768) SUCCESS。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` pin不変。

## CLOSED — 原模型におけるABX局所符号整合

AAZで証明済みの元の中心化Gauss-law物理源の固定有限体積での非零GIをABTの厳密な二点表示へ輸送。すべての有限H、b>0に対し、ある元リンクe、符号 `s=±1`、外側真正pair-Haarの開領域 `A` と補助内側二コピーHaar開領域 `V`、`η,κ>0` が存在し、`μ_H(A)>0`、`ν(V)>0`、`∀z∈A,w∈V, s(F_z(g)-F_z(h))≥η ∧ c_b(g,h)≥κ`、`∫_V sΦ_z≥ηκe^{-32b}ν(V)>0`。その存在性には新しい受信器整合仮定を追加していない。しかし開領域・下界はH,b依存であり、ABV固定capの質量1/64を使えない。

## CLOSED — ABY全符号付きtailの正確な模型内比較

真正interacting posteriorの交差行列式の実正係数分解 `D_b=k_b c_b`、`e^{-32b}≤k_b≤e^{32b}` をLeanで証明。全補助二コピーHaarで `Ψ_s=s(F(g)-F(h))c_b`、`M_s=∫max(Ψ_s,0)dν`、`M_{-s}` を**本当の不整合積分**として定義すると

`e^{-32b}M_s ≤ ∫max(sΦ,0) ≤ e^{32b}M_s`、
`e^{-32b}M_{-s} ≤ ∫max(-sΦ,0) ≤ e^{32b}M_{-s}`、

`[e^{-32b}M_s-e^{32b}M_{-s}]/2 ≤ sΔ_GI ≤ [e^{32b}M_s-e^{-32b}M_{-s}]/2`。

ABXの長方形で `M_s≥ηκν(V)` を加えると、`sΔ_GI≥[e^{-32b}ηκν(V)-e^{32b}M_{-s}]/2`。この形は**全負tailを隠さない**が、`M_{-s}` が小さいことをまだ示さない。

## OPEN — ABZ候補：全物理不整合の減衰・体積一様な開領域の抽出

1. 固定有限Hで、元のjoint物理受信器とWilsonエネルギー変化の順序・共分散を正確に解析し、`M_{-s}` が正寄与より十分小さいかを実証する。元のsourceに依存する符号不整合を都合よく削除しない。
2. ABXの `A,V,η,κ` のH・b依存性を解析し、可能なら元の局所Wilson幾何に基づく固定support cylinder／量的Haar質量・振幅を証明する。ABV固定cap `U` とABX選択領域 `V` の同一視は禁止。
3. 元の外側境界pair-Haar `μ_H` と補助内側二コピーHaar `ν`、真のPerron／GI source、両方のinteracting posteriorsを厳格に分離。ABSのHaar-centered絶対誤差、ABM・PZ37ZA no-go、遠方相殺の障害を追跡。
4. 全物理Hilbert coercivity、common fine-positive、同一endpoint、H1–H4、OS/Wightman、4D連続体の陽な質量ギャップは**OPEN**。正部分局所の存在を一様mass gapへ昇格しない。

GitHub MCPでexact theorem source→完全Lean本文／imports／dependent signatures／固定mathlib→workflow・job・Lean step completed→全`#print axioms`と独立receipt→squash SHA／正本HEAD一致→docsの順で判定。docs-onlyのStrict Leanは不要。

**以下のABW以前の各節は証明時点の履歴として、そのまま保持する。**

---

# MGAP4D — mainロードマップ文書ミラー（P4-Q2-PZ37ABW・2026-10-31 JST）

**唯一の定理正本**：`formal/real-hilbert-uniform-coercive-strong-limit`。mainのこの文書追補は [正本docs-only #6034](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6034) 統合 `7c6b3f093fa17939d6a54b8c3827bb4d6a620053` を反映する。ABWの証明・CIはcanonicalの [#6033](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6033)／[CI #41159498041](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41159498041) に属し、mainは文書ミラーであって定理正本ではない。元の二posteriors・Gauss-law源・物理受信器は置換していない。

---

# MGAP4D — 証明ロードマップ最新追補（2026-10-31 JST／P4-Q2-PZ37ABW）

## 唯一の定理正本と検証

- Repository: [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap)
- Authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。
- **最新定理 PR [#6033 ABW](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6033) MERGED**。マージ直後の定理squash HEAD `f37f4fceb0ee6b74d3d30e63be9cb1006e3c1e4e`。source `405aae45e47501ca868bad5258ead2c0fa7efd7e`、同一tree `bc481a3ac39226e8a9426436f83cc67222c5c88c`。
- [CI #41159498041](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41159498041)：completed / SUCCESS、Lean **11,008/11,008**、新規Lean warning/error **0/0**、新規8定理の公理依存は標準3公理のみ、`sorryAx`なし、独立receipt [#124415047421](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41159498041/job/124415047421) SUCCESS。
- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。

## CLOSED — 新しいABWの正確な条件付き接続

ABV #6030 が元のSU(2) Haarで `(μ×μ)(U)≥1/64`、`D_b≥2b exp(-32b)` を無条件に証明した。ABWはABTの実Gauss-law物理sourceの `Φ=(F(g)-F(h))D_b` に対して以下を追加した。**受信器の `F(g)-F(h)≥η≥0` を領域 `U` の全点で仮定**することにより、`∫_U Φ≥η b exp(-32b)/32`、全正部分 `∫max(Φ,0)≥η b exp(-32b)/32` が成立する。

別途 **全負部分** `∫max(-Φ,0)≤N`、または **真の符号付き補集合** `∫_(Uᶜ)Φ≥-N` の一方が実モデルで成立すれば、

`Δ_GI≥(η b exp(-32b)/32-N)/2`。

`b>0`、`N<η b exp(-32b)/32` の場合は、同一物理GI応答 `Δ_GI>0` の条件付き定理も証明済み。これは `F` やposteriorを人工的なものへ置換したのではなく、**元の真正定理の明示的な前提と帰結**である。

## OPEN — ABX以降の独立した物理的阻害条件

1. **元のFF受信器の符号整合を実証する。** 真のjoint physical receiverの二つの右リンク更新値の差と、正のjoint半密度×逆Perron分母から、`F(g)-F(h)` の符号および元の `U` 上の下界を定量化する。点の正値性、連続性、posterior密度の符号だけでは `η>0` 一様性は出ない。任意物理sourceに符号整合を無条件に仮定しない。
2. **真の全負tail・補集合を制御する。** `N` を元の相互作用模型の全変数と真正物理sourceから評価し、正寄与との量的余裕を証明する。他プラケット相殺とABSのHaar中心化粗絶対誤差obstructionを消去しない。
3. **元の外側物理pair-Haarへの輸送。** ABWの `μ×μ` は補助二コピーHaarであり、実外側境界pair-Haar `μ_H` の体積一様な `A_p/G` を意味しない。必要な局所入力、遠方descent、同一endpointを実証する。
4. **全物理Hilbert・4D連続体。** source-specific下界から共通positive-fine／全深さ／E/F／H1–H4／OS/Wightman／質量ギャップへ別の証明が必要。ABMとPZ37ZAのno-goの量化範囲を変更しない。

GitHub MCPで正本HEAD→Lean全ソース・imports・dependent signatures→exact-source CI→公理・sorryAx→docs/historyの順に再観測。Lean変更は8定理を同じpinで検証済み。今後のdocs-only変更ではStrict Leanを起動しない。

**以下のABVまでの過去節は当時の数学的状態を示す履歴として原文保持する。**

---

# MGAP4D — 証明ロードマップ追補（2026-10-31 JST／P4-Q2-PZ37ABR–ABV）

**この `main` は文書ミラーであり、Lean定理正本ではない。** 唯一の定理正本は [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。この追補は正本の検証済み結果を文書として反映する。Lean定理を `main` へ移したという意味ではない。

**文書ミラー同期元：** 正本のdocs-only commit [`e30f72afe94c8023cc7d185ee059a1a08a58bc88`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/e30f72afe94c8023cc7d185ee059a1a08a58bc88) の [README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e30f72afe94c8023cc7d185ee059a1a08a58bc88/README.md)／[ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e30f72afe94c8023cc7d185ee059a1a08a58bc88/ROADMAP.md)。この文書同期SHAとABVの検証source・定理squashを区別する。

**この追補の検証済み基準点：** [ABV #6030](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6030) の定理squash [`3b0974b18ad4d7843298ce92be2365fd1e2409e6`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/3b0974b18ad4d7843298ce92be2365fd1e2409e6)、exact-source [`af809652c2ee4d77949fea7c9881c3aada45bacf`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/af809652c2ee4d77949fea7c9881c3aada45bacf)。ABR #6026、ABS #6027、ABT #6028、ABU #6029、ABV #6030は全て定理正本へMERGED。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。後続docs-only commitと実際に検証したPR source SHAを混同しない。

## CLOSED — ABQ2以後に進んだ厳密な元のsource・posterior解析

### ABR #6026：元のsourceと真のPerron周辺密度を区別

元のsourceの遠方積分 `S_B(x)=∫hW(A[x,r])K_rem(r,B)dμ_rem(r)` と、ABQ2の `R_B(x)=∫hW(A[x,r])Ω(A[x,r])K_rem(r,B)dμ_rem(r)` を別々に保持する。両者の正値性・必要な連続性／可積分性と、正の補正 `V_B=S_B/R_B` を証明した。`V_B=1` とする置換を行わない。

`M_B=∫K₄(x,B_four)R_B(x)dμ⁴(x)`、`d_B=K₄R_B/M_B` に対し、`M_B>0`、`d_B>0`、`∫d_B=1`、`hW(B)M_B=t_(H,b)Ω_b(B)`。従って、元のsourceの正確な表示は

`∫K_b(A,B)f(A_four)dHaar_H(A) = t_(H,b)Ω_b(B)∫d_B V_B f dμ⁴`

である。正負部分の分解でもこの補正と真の物理正規化を保持する。元のsourceに新たなPerron因子を挿入して問題を変えていない。

### ABS #6027：相対比較と符号付き誤差の正確な費用

`b≥0` で、元の真正四辺について `exp(-24b)S_B(y)≤S_B(x)≤exp(24b)S_B(y)`、`exp(-80b)V_B(y)≤V_B(x)≤exp(80b)V_B(y)` を証明した。前者は四つの真正リンクの空間半重み比較、後者はその前者とABQ2の `exp(56b)` 比較を組み合わせる。

`I_f(B)=∫K_b(A,B)f(A_four)dHaar_H(A)` とすると、元の全遠方時間因子を残して

`|I_f(B)-hW(B)S_B(y)∫K₄(x,B_four)f(x)dμ⁴| ≤ hW(B)S_B(y)(exp(24b)-1)∫K₄(x,B_four)|f(x)|dμ⁴`

を証明した。可積分性を示した上での符号付き評価であり、Leanのtotal integralの規約だけに依存していない。

**この経路の限界。** Haar中心化 `∫f=0`、`q=K₄`、`J=∫qf`、`L=∫q|f|` なら `exp(-8b)≤q≤1` から `|J|≤(exp(8b)-1)L≤(exp(24b)-1)L`。従ってこの粗い誤差予算を使う厳密十分条件 `(exp(24b)-1)L<J` は成立しない。これはABSのPRで明示した解析的帰結であり、ABSの新しいLean定理として数えない。元の符号付きsourceの消滅や一般のGI不可能性も意味しない。次段階では符号付き相関を保存する。

### ABT #6028：二つの元のinteracting posteriorによる厳密pairing

同じ物理受信器 `F`、二つの実際の正規化Wilson posterior `p₀,p₁`、正規化SU(2) Haar `μ` を用いる。

`D_b(g,h)=p₀(g)p₁(h)-p₁(g)p₀(h)`、`Φ(g,h)=(F(g)-F(h))D_b(g,h)`。

連続性・可積分性、

`Δ_GI=(1/2)∫_(μ×μ)Φ=(1/2)(∫Φ₊-∫Φ₋)`、`Δ_GI>0 ↔ ∫Φ₋<∫Φ₊`

を証明した。正部分の質量下界 `P` と全負tail上界 `N` が別途与えられれば `(P-N)/2≤Δ_GI` が成立するが、`P>N` はここでは無条件に証明していない。実log weight `L₀,L₁` と実partition `Z₀,Z₁` を用いた行列式の正確な指数表示・符号判定も閉じた。受信器差の符号はこの判定からは決まらない。

`μ×μ` は一リンク群の**二つの補助コピー**の参照Haarである。二つの元のposterior密度は両方とも積分内に残り、posterior独立性、独立リンク近似、元の外側物理境界pair-Haarの置換を導入しない。

### ABU #6029：実posterior密度行列式の一様な点ごとの下界

元のidentity／`R(π)`の左値に対する時間Wilson energy crossing `c_b(g,h)` は、定義上 `H`・選択リンク・右背景の引数を持たない。`b≥0` の全有限 `H`、実リンク、右背景で

`D_b(g,h)=p₁(g)p₀(h)(exp(c_b(g,h))-1)`、`exp(-32b)≤p₁(g)p₀(h)≤exp(32b)`、

`D_b≥0 ↔ c_b≥0`、`c_b≥0 ⇒ exp(-32b)c_b≤D_b`、`exp(-32b)|c_b|≤|D_b|`

を証明した。`c_b(1,R(π))=4b` なので、`b>0` では `D_b(1,R(π))≥4b exp(-32b)>0`。`H=0` を含み、実際の密度積を定数1へ置き換えていない。

**ABU単独で閉じたのは密度行列式の点ごとの評価。** 次のABVはその先の固定正Haar測度領域と制限積分を閉じる。ABTの物理signed pairに下界を移すときは、元の `F(g)-F(h)` の符号・振幅を別の条件として残す。全域の整合や無条件GI正値性は未証明。

### ABV #6030：真正SU(2) capのHaar質量と実行列式の制限積分

`E` は元のSU(2) Wilsonエネルギー、`μ` は元の正規化compact Haarとする。結合・体積・リンク・右背景を引数に持たない実際の集合

`A={g:E(g)≤1/2}`、`C={h:3/2≤E(h)}`、`U=A×C`

を用いる。元のpi rotation `R(π)` と真正の中心負単位元の一致、および `E(R(π)⁻¹g)=2-E(g)` を証明した。

**八つの元のHaar平行移動による定量質量。** 既存の真正quaternion軌道から、`χ=1-E` に対して `Σ_(j<4)χ(q_j g)²=1`。どの `g` でも一つの平行移動後の指標の絶対値が `≥1/2` なので、四つの `q_j` とその中心反転を合わせた八つの左平行移動による `A` の逆像が全SU(2)を覆う。元のHaar不変性と有限和の測度評価により `1≤8μ(A)`、従って `μ(A)≥1/8`。中心平行移動で `μ(C)=μ(A)≥1/8`、積測度で `(μ×μ)(U)≥1/64`。これらの可測性も証明し、有限群の別Haarや未証明のcap質量を導入しない。

**元の時間crossingの正確な変動。** 全実数 `b` で `c_b(g,h)=2b(E(h)-E(g))`、両群変数について連続。`b≥0` で

`|c_b(g,h)-4b|=2b(E(g)+2-E(h))`。

`U` は `(1,R(π))` の近傍で、`E(g)<1/2`、`E(h)>3/2` の開近傍を含む。`U` 自体の定義は非厳密不等式を使う可測集合である。`U` 上では `E(h)-E(g)≥1`、従って `c_b(g,h)≥2b`。

**実際の二posterior行列式の積分。** ABUの同じ正規化相互作用posterior密度を保ち、全有限 `H`（`H=0` を含む）、全実リンク、全右背景、`b≥0` について

`D_b(g,h)≥2b exp(-32b)`（`(g,h)∈U`）、

`∫_U D_b(g,h)d(μ×μ)≥2b exp(-32b)(μ×μ)(U)≥b exp(-32b)/32`

を証明した。実行列式の連続性・可積分性を示してから制限積分の評価を適用し、`b>0` で同じ積分が厳密に正になることまで閉じた。定数は `b` に依存するが、`H`・リンク・右背景には依存しない。

定理本文：[Haar capと八平行移動](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/3b0974b18ad4d7843298ce92be2365fd1e2409e6/MGAP4D/MathlibAnalytic/SpecialUnitaryTwoWilsonEnergyHaarCapsV5_PZ37ABV.lean)／[正領域と実posterior行列式積分](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/3b0974b18ad4d7843298ce92be2365fd1e2409e6/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPosteriorPositiveHaarRegionV5_PZ37ABV.lean)。

**ABVの境界。** 閉じたのはABTの補助的な二コピーHaar上の `∫_U D_b` である。物理signed pairには元の `F(g)-F(h)` が掛かる。従って受信器の整合、全負tail、他プラケット相殺、元の外側境界pair-Haarへの一様輸送をABVの結果だけで閉じない。

## OPEN — 次に必要な独立の解析入力

1. **ABW候補：元の物理受信器整合を明示した条件付き移送。** ABVの同じ `U` と実際のGauss-law物理sourceの元の `F` について、`F(g)-F(h)≥η≥0` を `U` 上の明示的条件として、`∫_U Φ≥η b exp(-32b)/32` へ接続することが次の形式化対象。さらに全負部分 `∫Φ₋≤N` と組み合わせた目標は `Δ_GI≥(η b exp(-32b)/32-N)/2`。これらは次段階の条件付き目標であり、ABVで新たに閉じた定理とは数えない。条件の実際の成立、一様な `η>0` の構成、正の余裕の証明は独立のOPEN入力である。
2. **全負tailと他プラケット相殺。** ABTの `∫Φ₋` を元の全受信器と全変数で制御し、正部分の寄与との厳密な正の余裕を示す。選んだ点／領域以外の寄与、元のsourceに含まれる他プラケット、遠方変数を捨てない。ABSの成立しないHaar中心化粗十分条件を前提に戻さない。
3. **元の完全外側pair-Haarへの一様輸送。** 補助的な一リンクpairingと元の外側境界pair-Haarを区別し、真正 `A_p`／`G` の体積一様正下界まで必要な振幅・測度・積分降下を証明する。正の密度事象または有限体積の定性的正値性だけではこのゲートは閉じない。
4. **全物理Hilbertと同一endpoint。** 特定sourceの正下界から全Gauss-law物理Hilbert coercivityへの拡張、共通positive-fine区間、同じendpoint E/F、任意深さの一様評価を独立に閉じる。
5. **4D連続体。** H1–H4、強極限と物理時間、OS/Wightman再構成、非自明な4D Yang–Mills構成とmass gapは引き続きOPEN。

ABMの「`0<b(H)≤B` だけでは一様絶対重なりを保証できない」という量化付き障害、ABK／ABLの条件付き評価・有限体積結果、PZ37ZAの別の補償済み二文脈量のno-goを保持する。新たな下界のために元のWilson核、Perron真空、Gauss-law源、二つの相互作用posterior、Haar測度、真の物理転送正規化を置換しない。

## 検証記録と文書の権限

| 段階 | exact source SHA | 定理squash SHA | 完了した検証 |
| --- | --- | --- | --- |
| [ABR #6026](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6026) | `08c5d63bafa0e344ac1e7c34812f427d1cfcadea` | `bb6c8559693dd7bb48806408829b42c79828477a` | [CI #41139912350](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41139912350)、11,012/11,012、18公開定理 |
| [ABS #6027](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6027) | `b448b6c183142433720a9450e0c0e3d47db1a831` | `59814cd69781b6ebae9bcf605e79441dad4b88bf` | [CI #41150355205](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41150355205)、11,014/11,014、10公開定理 |
| [ABT #6028](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6028) | `4933d4f0dd7e8e3155d15c73b7fafb795a467893` | `dd5409990c522ec7dc86e2042e469521d8d718bc` | [CI #41153079696](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41153079696)、10,652/10,652、17公開定理 |
| [ABU #6029](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6029) | `105023f814c64e6044263ea965a43e155634ad35` | `39b481be7bc2e64e406c66414f0a4224048727ef` | [CI #41155882313](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41155882313)、10,654/10,654、14公開定理 |
| [ABV #6030](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6030) | `af809652c2ee4d77949fea7c9881c3aada45bacf` | `3b0974b18ad4d7843298ce92be2365fd1e2409e6` | [CI #41157968798](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41157968798)、11,007/11,007、27公開定理 |

各runは **completed / SUCCESS**。変更Leanのwarning/error **0/0**、全新規公開定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、別のexact-source completion receipt **SUCCESS**。ABVの別receiptは [job #124410035502](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41157968798/job/124410035502)。ABRの古いPR本文の「pending」ではなく、完了したrunとreceiptが最終検証状態を表す。ABRに含まれるoptional direct diagnosticのflag修正は必須Lake検証を弱めていない。ABS–ABVでは既存ファイル・模型・前提・pin・public root・workflowを変更していない。

**README/ROADMAP同期はdocs-only。** 新しいLean証明の代わりにはならず、`main` を定理正本にしない。この文書変更だけを理由にStrict Leanを再実行しない。次の定理変更では、その完全source・imports・依存signatures、exact-source CI、変更ファイル診断、公理監査、別completion receiptを実際に確認する。結果と表記の要約は[正本README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/formal/real-hilbert-uniform-coercive-strong-limit/README.md)。

## 歴史的記録 — ABQ2以前のロードマップ（原文保持）

**この見出し以降の題名、「最新」「現行」「Current」「OPEN」とSHAは各記述時点の履歴である。** ABQ2およびそれ以前の到達点と旧候補を原文のまま残す。現在の検証済み範囲と未解決入力は上記追補による。

---

# MGAP4D — 証明ロードマップ追補（2026-10-31 JST／P4-Q2-PZ37ABQ2）

**正本** `formal/real-hilbert-uniform-coercive-strong-limit`／[PR #6023](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6023) **MERGED**／正本 HEAD = squash SHA [`26632456e8c74d3f36453b4242a67cdbd9ae26a7`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/26632456e8c74d3f36453b4242a67cdbd9ae26a7)。`main` は文書ミラー、唯一のLean定理正本ではない。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を固定。

[exact-source CI #41132500130](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41132500130)：検証source `9efc3034670654289f3ddb147f23f7562b9ada33`、**11,010 / 11,010 SUCCESS**、変更Lean 2ファイル warning/error **0/0**、標準3公理（`propext`／`Classical.choice`／`Quot.sound`）のみ、`sorryAx` なし、独立completion receipt SUCCESS。

## CLOSED — 真正四辺の全リンク再構成と元の物理核

1. **実座標と全補集合。** 実際の周期格子 `L_H` の MY 真正四辺 `e : Fin 4 ↪ L_H` と補集合 `R_(H,p)` を用いて、選択・遠方座標から全配置を再構成する。両座標の復元、連続性、有限積分のFubiniを証明（汎用Lean5定理）。全有限 `H`、`H=0` を含む。
2. **相互作用を捨てない遠方重み。** 元の空間Wilson半重み、元の連続正値Perron代表、元の遠方全時間因子を正規化SU(2)積Haarで積分する `R_(H,p,b,B)(x)` を定義。積分関数の可積分性、`R(x)>0`、`exp(-56b) R(y)≤R(x)≤exp(56b) R(y)` を真正 `p`、全有限 `H`、`b≥0` で証明。係数は体積に依存しないが、**絶対質量の一様下界ではない**。
3. **元のone-slab核を保存する積分恒等式。** すべての連続四辺テスト `f` について `∫Ω(A)K(A,B)f(A∘e)dHaar_H(A)=hW(B)∫K₄(x,B∘e)R(x)f(x)dμ⁴(x)` を証明。空間半重みとPerron代表を除去していない。遠方の独立性・posterior置換を仮定しない。
4. **真の物理質量。** `f=1` の定理から `hW(B)∫K₄(x,B∘e)R(x)dμ⁴(x)=t_(H,b)Ω(B)` を導く。`Z_b^|L_H|`／`Z_b⁴` と真の物理転送ノルム `t_(H,b)` は区別する。
5. **型検査障害の構造的解決。** 汎用の `Fintype.decidableMemRangeFintype` が使う古典的 `DecidableEq` と、具体的リンクの構造的 `DecidableEq` が不透明な `Measure.pi` 内で一致せず、`whnf` に過剰な展開を起こしていた。元のモデルを変えず局所的な `Classical.propDecidable` に揃えて解消し、最終の公開定理2件を標準3公理のみで閉じた。

## OPEN — 次の独立した物理入力

1. **真正の符号付きGI応答。** `R(x)>0` と相対比較を、元の二つのinteracting posterior／符号付き受信器に定量的に接続し、全物理源の他プラケット寄与と負tailを制御する。符号付き応答の正下界は今回まだ導いていない。
2. **体積一様な完全pair-Haar `A_p`／`G` 正下界。** 定量的な負側相殺・補償を含む新しい入力が必要。既存の局所Haar二乗モーメント、遠方重みの正値性・相対比較だけでは不十分。
3. **全物理Hilbert coercivity と4D連続体。** 共通positive-fine区間、同一endpoint E/F、任意深さ、H1–H4、OS/Wightman、4D Yang–Mills continuum mass gap は依然OPEN。ABK・ABL・ABM・旧no-go履歴は維持し、仮定の弱化やDobrushin系の早期再構築は行わない。

**以下の過去節は履歴として保持する。最新の証明正本・未解決範囲は本追補に従う。**

---

# MGAP4D — 証明ロードマップ追補（2026-10-29 JST／P4-Q2-PZ37ABP）

**文書ミラー同期元：** 正本の文書 [PR #6020](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6020)、squash [`170030b4503ca5f7b50c6fd144a68195bee1d463`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/170030b4503ca5f7b50c6fd144a68195bee1d463)。

## CLOSED — 元の全リンク時間核から真正四辺へのHaar制限

[PR #6019](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6019)、exact-source [`85617e213deb0cb8101fde98f656d096b7f47899`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/85617e213deb0cb8101fde98f656d096b7f47899)、定理squash [`d3879ed7352b68f68af0f1b467369f91cab11f19`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d3879ed7352b68f68af0f1b467369f91cab11f19)。唯一の定理正本は [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。

[Exact-source CI #40878551912](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40878551912)：依存関係を含む対象ビルド **11,007 / 11,007 SUCCESS**、変更Lean warning/error **0/0**、公開定理11件の標準3公理のみ、`sorryAx`なし、独立completion receipt SUCCESS、独立最終レビューPASS。CI実checkout `e6ec3bf2ee7006c103127bf2e4d7268d09dd607e` とsourceの全ファイルtreeは `ad2fcf3d82a810dbbbb8578d350ba4de000ca231` で一致。

1. 一般有限積を、embeddingの像と補集合の実際の積測度へ測度保存同型で分解した。選択座標に依存するテストの重み付き積分は、選択積分と遠方一座標質量の積に等しい。
2. 元の `TemporalGaugeCrossingKernel` のcanonical link listに重複がなく、そのfinsetが実際の全リンク集合であることを使い、元のlist積を全有限積へ接続した。
3. 各時間因子の質量はABOの真正 `Z_b>0`。全質量 `Z_b^|L_H|` と、元の `B_e` を保持した遠方質量 `Z_b^|R_(H,p)|` を導いた。
4. `k_b/Z_b` の各質量が1であることから、全リンクで正規化した積分が、真正四辺の同じ積分を `Z_b⁴` で割ったものに厳密一致する。全有限 `H`、全真正プラケット `p`、全実数 `b` が対象で、`H=0` を含む。
5. 元の全リンク時間積分による中心化半エネルギー伝送が `r_b⁴(E_p−1)/2` と同定され、参照Haar二乗モーメント `r_b⁸/16` と指定した正結合区間の一様正下界を継承した。連続テストの通常の可積分性も証明した。

## OPEN — 次の独立入力（ABQ候補）

1. **元の空間Wilson重み。** 既存の一リンクincidence・作用変動評価を再利用して、完全one-slab核の両端spatial half-weightを保持して、選択四辺を変えたときに作用する実プラケットの有限集合と遠方積分の厳密表示を構成する。体積全体に比例する粗いBoltzmann比較を、一様下界の証明として扱わない。
2. **Perronと二つのinteracting posterior。** 既存のPerron局所Harnackを保持・再利用し、真の正規化を維持して、四辺の遠方重みと元の二つのposteriorの符号付き受信器を結ぶ必要な比較を証明する。時間Haarのtensor構造だけからposterior独立性やPerron重なりを推論しない。
3. **全物理源の相殺。** 他プラケット寄与と負tailを定量的に制御する。局所の二乗Haar下界を全符号付き対比の正下界へ直接置き換えない。四辺周辺分布の正の密度比較が得られても、それだけでは符号付きGI応答の下界や他プラケットとの相殺制御は導かない。
4. **完全pair-Haar下界。** 真正 `A_p` または `G` の体積一様正下界を元の物理模型内で導く。ABKの十分条件を新しい仮定付き命題だけで閉じない。

ABKの十分条件、ABLの各有限体積での真正正値性、ABMの上限のみの結合条件に対するno-go、旧PZ37ZAの補償済み二文脈に対するno-goは保持する。全物理Hilbert coercivity、共通positive-fine区間、同一endpoint E/F、任意深さ、H1–H4、OS/Wightman、連続体4D Yang–Mills質量ギャップはOPEN。

**以下のABO以前の題名・「現行」・旧OPENは当時の履歴として原文を保持する。** 現在の到達点は本追補による。README/ROADMAPだけの同期はdocs-onlyであり、Lean CIを起動しない。

---

# MGAP4D — 証明ロードマップ追補（2026-10-29 JST／P4-Q2-PZ37ABO・ABO2・ABO3）

**文書ミラー同期元：** 正本の文書 [PR #6017](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6017)、squash [`3b168eb70e594c3719f3dac7f5fc9d6a76ae5600`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/3b168eb70e594c3719f3dac7f5fc9d6a76ae5600)。定理は引き続きformal正本上の #6016 に属する。

## 現行の到達点 — 真正四リンク時間畳込みと実プラケットのHaar下界

唯一の定理正本は [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。[PR #6016](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6016)、exact-source [`511bd76e290972caec371b4672a210033436cfa7`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/511bd76e290972caec371b4672a210033436cfa7)、定理squash [`75f0c61fb538bef71a34a6e544831f98e792bc2b`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/75f0c61fb538bef71a34a6e544831f98e792bc2b)。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。

[Exact-source CI #40869191576](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40869191576)：依存関係を含む対象ビルド **11005/11005 SUCCESS**、新規Lean 3ファイルのwarning/error **0/0**、公開定理17件の標準3公理のみ、`sorryAx`なし、独立completion receipt SUCCESS。

CIのPR検証用checkout `a2f6b42bb211a9e56f9c90068efe1390d8699266` と検証sourceは、全ファイルtree `7145a3fdd255089ba3af1b1243fb42f2eb5193a2` が完全一致することも確認した。

### CLOSED — ABOの真正一リンクの両向き積分

ABNの元のWilson時間因子 `k_b=exp(−bE_W)` と実Haar積分 `Z_b`、`N_b` を保持する。Haar左平行移動 `x=yg`、Wilsonエネルギーの反転不変性、文字の巡回性、ABN2の既証畳込み則から、任意の周囲の群要素 `a,c` に対して

`∫k_b(x⁻¹y)dμ(x)=Z_b`、
`∫k_b(x⁻¹y)χ(axc)dμ(x)=N_bχ(ayc)`、
`∫k_b(x⁻¹y)χ(ax⁻¹c)dμ(x)=N_bχ(ay⁻¹c)`

を証明した。SU(2)の非可換な積の順序を保ち、前提として固有関係を置かない。

### CLOSED — ABO2の真正四リンク時間畳込み

実4リンクの積Haar `ν=μ^4` と元の巡回プラケット語 `W(x)=x₂⁻¹x₃⁻¹x₀x₁` を用いる。有限積座標の測度保存変換とFubiniにより、`K⁽⁴⁾_b(x,y)=∏ᵢk_b(xᵢ⁻¹yᵢ)` の実積分を4回の一リンク積分へ分解する。その結果、

`∫K⁽⁴⁾_b(x,y)dν(x)=Z_b⁴`、
`∫K⁽⁴⁾_b(x,y)χ(W(x))dν(x)=N_b⁴χ(W(y))`。

従って `Z_b⁴` で割った同じ4リンク畳込みに `Q⁽⁴⁾_b1=1` と `Q⁽⁴⁾_b(χ∘W)=r_b⁴(χ∘W)` が成立する。これは選択四辺の時間因子についての恒等式であり、遠方の空間相互作用を落とした全物理核を新たに定義する操作ではない。`Z_b⁴` と元の物理転送ノルム `t` を区別する。

### CLOSED — ABO3の全H・全真正プラケットでの参照Haar下界

MYの真正四辺embeddingは `H=0` を含めて単射であり、元の向き付きWilsonプラケットエネルギーは巡回語のエネルギーと一致する。従って同じ完全空間Haarで、各実プラケットの `∫E_p=1`、`∫(E_p−1)²=1/4` が成立する。

`f₄(x)=(E_W(W(x))−1)/2` と `F_(H,p,b)(A)=(Q⁽⁴⁾_b f₄)(A∘edges_(H,p))` を定める。4リンク畳込みを実際の四辺に評価した文字は `r_b⁴(1−E_p)`。中心化半エネルギーの**実際の積分**は `r_b⁴(E_p−1)/2`。いずれも平均0で、二乗モーメントはそれぞれ `r_b⁸/4` と `r_b⁸/16` である。ABNの独立下界 `r_b≥c₀=b₀ exp(−2B)/4>0` を使い、指定した `0<b₀≤b≤B` の全域で

`∀H,p, ∫F_(H,p,b)(A)² dHaar_H(A) ≥ c₀⁸/16 > 0`

を得た。この下界は元の時間因子と参照Haarについて成立し、二つの相互作用するposteriorの符号付きGIに対する下界を仮定・導出したものではない。

### OPEN — 次の独立入力（ABP候補）

1. 全空間リンクにわたる時間因子の積から、選択した実四辺への厳密な制限・積分表示を閉じる。実際のL²作用素の対称性・定数モード・四辺モードの関係を同じ測度と正規化で接続する。
2. 遠方変数を積分して得る、元の空間Wilson相互作用を含む実重みを構成し、体積に依存しない比較・下界を証明する。ABNの抽象二モード補題の重み仮定を未証明の物理的事実として使わない。
3. Perron半密度と二つのinteracting Wilson posteriorを保持したまま、元の符号付き対比との重なりを制御する。NGの正規化因子と符号付き密度を残す。
4. 全物理源の他プラケットとの相殺を制御し、完全pair-Haarで一様 `A_p≥α>0` を導く。今回の空間Haarモーメントと完全pair-Haarの `A_p`・`G` は別の量である。

ABKの十分条件、ABLの有限体積の定量的同時非零事象、ABMの小正結合族による一様絶対重なりの障害を全て保持する。固定 `b>0`／`0<b₀≤b(H)≤B` の物理GI一様下界、全物理Hilbert coercivity、共通positive-fine区間、E/F、H1–H4、OS/Wightman、連続体Yang–Mills質量ギャップはOPEN。

**以下のABN以前の題名・「現行」・旧OPENは当時の履歴として原文のまま残す。** 現在の状態は本追補による。README/ROADMAPだけの同期はdocs-onlyであり、Strict Leanを起動しない。

---


# MGAP4D — 証明ロードマップ追補（2026-10-29 JST／P4-Q2-PZ37ABN・ABN2）

## 現行の到達点 — 元の一リンク時間Wilson文字モードの定量的非消滅

唯一の定理正本は [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。[PR #6013](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6013)、exact-source [`e71a43d39c9ed71e93a33c6953ce39205aa90719`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/e71a43d39c9ed71e93a33c6953ce39205aa90719)、定理squash [`1aa3b282399c534f2aba7f9f97307726d4c7f5e0`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/1aa3b282399c534f2aba7f9f97307726d4c7f5e0)。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。

[Exact-source CI #40859191626](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40859191626)：**11003/11003 SUCCESS**、新規Lean 3ファイルのwarning/error **0/0**、公開定理24件の標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、独立completion receipt SUCCESS。

**文書ミラーの同期元：** 正本のdocs-only [PR #6014](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6014)、文書squash [`288d4381efdc92eef29d46d698b8a773cfd9e2c8`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/288d4381efdc92eef29d46d698b8a773cfd9e2c8)。mainへの追加はREADME/ROADMAPだけで、Lean定理は正本に保持する。

### CLOSED — ABNの元の指数核からの係数下界

実際のSU(2) Haar上で `χ=1−E_W`、`k_b=exp(−bE_W)`、`Z_b=∫k_b`、`N_b=∫k_bχ`、`r_b=N_b/Z_b`。既存の真正Haar文字恒等式から `∫χ²=1/4` を得る。文字の正負それぞれで元の指数核に `b exp(−2b)χ²≤χ(k_b−exp(−b))` を証明し、`∫χ=0` で定数項を消す。

その結果、`b≥0` で `N_b≥b exp(−2b)/4`、`0<Z_b≤1`、`r_b≥b exp(−2b)/4`。全実数で `Z_b>0`、`r_b≤1`、連続性が成立し、`r_0=0`。指定した `0<b₀≤b≤B` では、入力下界を仮定せず `r_b≥c₀:=b₀ exp(−2B)/4>0` を導出した。

### CLOSED — ABN2の実際の畳込み固有恒等式と転送後分散

SU(2)の `g⁻¹+g=Tr(g)I` から、元の正規化実文字に `χ(g⁻¹a)+χ(ga)=2χ(g)χ(a)` が成立する。元のHaarの反転不変性と元のWilsonエネルギーの反転不変性を使い、

`∫k_b(g)χ(g⁻¹a)dμ(g)=N_bχ(a)`、従って `T_bχ(a)=r_bχ(a)`

を証明した。`T_b` はここで実際の**一リンク時間畳込みをそのHaar質量 `Z_b` で割ったもの**を指し、全物理転送ノルム `t` を1に設定する操作ではない。

同じHaar上で `∫T_bχ=0`、`∫(T_bχ)²=r_b²/4`。従って正の結合区間全域で `∫(T_bχ)²≥c₀²/4>0`。これは固有関係を仮定しない、元の一リンク時間因子の転送後変動についての下界である。

### CLOSED — 明示的前提を持つ二モード重み付き転送補題

実内積空間で `Q` が対称線形写像、`u⊥v`、`Qu=u`、`Qv=λv`、`0≤λ≤1`、`m≥0`、`⟨Wx,x⟩≥m‖x‖²` なら、全ての実数 `c` に対して `mλ‖v‖≤‖Q(W(v−cu))‖`、および対応する二乗下界が成立する。試験ベクトル `v−λcu` による対称性とCauchy–Schwarzの証明で、逆作用素や求めるGI下界を仮定しない。`W` の線形性や `u` の単位規格化も不要。

この補題の物理適用には、実際の作用素の固有恒等式と実際の重みの体積一様下界を独立に満たす必要がある。

### OPEN — 次の真正模型上の接続（ABO候補）

1. 既存MYの実四辺embeddingとHaar輸送を用い、真正プラケット四辺の時間畳込みに文字固有係数 `r_b⁴` を証明する。一リンクから四リンクへの拡張を未証明のまま使わない。
2. 遠方変数を積分して得る、元の空間Wilson相互作用を含む実重みについて、体積に依存しない比較・下界を導く。固定正結合の指定だけでこの解析入力は閉じない。
3. Perron半密度と二つのinteracting Wilson posteriorを保持し、実際の符号付き対比と転送された局所モードの重なりを制御する。既存NGの正規化因子と符号付き密度を省略しない。
4. 全物理源に含まれる他プラケットとの相殺を制御し、元の完全pair-Haarで `∃α>0, ∀H, ∃e,p: A_(H,b(H),e,p)≥α` を導く。この段階の一リンク分散を `A` や `G` と同一視しない。

ABKの `A_p` による十分条件、ABLの有限体積の定量的同時非零事象、ABMの小正結合族による一様絶対重なりの障害を全て保持する。固定 `b>0`／`0<b₀≤b(H)≤B` の完全な物理GI一様下界、全物理Hilbert coercivity、共通positive-fine区間、E/F、H1–H4、OS/Wightman、連続体Yang–Mills質量ギャップはOPEN。

**以下のABM以前の題名・「現行」・旧OPENは当時の履歴として原文のまま残す。** 現在の状態は本追補による。README/ROADMAPだけの同期はdocs-onlyであり、Strict Leanを起動しない。

---

# MGAP4D — 証明ロードマップ追補（2026-10-29 JST／P4-Q2-PZ37ABM）

## 現行の到達点と結合領域の再設定

唯一の定理正本は [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。ABMの確定記録：[PR #6010](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6010)、exact-source [`965054a69cf1be2c66830648ea90cf81fb85db47`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/965054a69cf1be2c66830648ea90cf81fb85db47)、[CI #40853685655](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40853685655)。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

**ABMの検証結果：** [exact-source CI #40853685655](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40853685655) は **11177/11177 SUCCESS**、変更Leanファイル1件のwarning/error **0/0**、新規公開定理12件の公理依存は `propext`・`Classical.choice`・`Quot.sound` の範囲、`sorryAx`なし、独立completion receipt SUCCESS。検証sourceと異なる定理squashは [`cf3d40e1dba4c2d8f718fb4525aa519351bc897c`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/cf3d40e1dba4c2d8f718fb4525aa519351bc897c)。後続の文書同期は定理を追加しない。

**文書ミラーの同期元：** 定理正本のdocs-only [PR #6011](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6011)（[README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2a56ce70aeb18fe85934a289fd26df2a5d8cbe69/README.md)・[ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2a56ce70aeb18fe85934a289fd26df2a5d8cbe69/ROADMAP.md)）。定理squashと文書同期SHAを区別し、mainへの追加は文書のみです。

### CLOSED — ABH〜ABLで追加された真正Wilsonの評価

全段階で元の核・Perron真空・Gauss-law物理源・実転送ノルム `t>0`・二つの相互作用するposterior・完全外側pair-Haarを保持する。以下、`C_p=tΔ_fullΔ_local,p`、`c_p=∫C_p=tK_p`、`A_p=∫|C_p|`、`N_p=∫max(-C_p,0)`、`G=∫Δ_full²`、`Mcomp_p=∫(tΔ_local,p)²`、`E_b=exp(8b)(exp(16b)−exp(−16b))`。

| 段階 | 証明された内容 |
| --- | --- |
| [ABH #6003](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6003) | 元の完全pair-Haarの符号付き積分を保持し、真正事象と全負tailから `c_p≥ρδ−η`。一様な正の余裕を入力とする十分条件。 |
| [ABI #6006](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6006) | `0<b(H)≤B` から `E_b≤E_B` を導出。真正の共通交差下界 `κ` があれば `G≥4κ²/E_B²`。 |
| [ABJ #6007](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6007) | 全プラケットのBessel budget `ΣMcomp_p≤6E_b²`、および `Σc_p², ΣN_p²≤6E_b²G`。 |
| [ABK #6008](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6008) | 絶対値を積分内に置いた `A_p=c_p+2N_p`、`A_p²≤GMcomp_p`、`ΣA_p²≤6E_b²G`、正確な相殺費用 `4N_p(N_p+c_p)≤GMcomp_p−c_p²`。一様 `A_p≥α>0` からの別のGI下界は条件付きで成立。 |
| [ABL #6009](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6009) | 真の二次モーメント `J_p=∫C_p²≤G(E_b/2)²`、`ΣJ_p≤6E_b²G`。毎有限 `H,b>0` の正の証人から `U_p={A_p/2<abs(C_p)}` を構成し、`μ_H(U_p)≥A_p²/(E_b²G)>0`。同じ開事象でfull/local両GI応答が非零。 |

ABLの独立確認：[CI #40849967415](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40849967415)、11,176/11,176 SUCCESS、変更Lean 0 warning/0 error、7公開定理の標準3公理のみ、`sorryAx` なし、completion receipt SUCCESS。検証source `1352fa52f2068d4a420fb959bea05ddeea786f95` とsquash `10c81d79d36008cfff20cb53e0adc5d5e5292e5f` を区別する。

### ABM — 上限のみの結合条件に対する実モデル内の障害

真正のプラケット数 `P_H` と有限スラブ作用budget `M_H` を残したまま、

`|tΔ_full|≤P_HE_b/2`、`t⁻¹≤exp(bM_H)`、`0≤A_(H,b,e,p)≤Q_H(b):=P_H exp(bM_H)(E_b/2)²`

を得る。固定 `H` で `Q_H` は連続かつ `Q_H(0)=0`。これはスカラー上界についての主張であり、Perron真空を結合について連続に選ぶ仮定を使わない。

この有限体積ごとの事実から、**任意の `B>0` に対し一つの結合族を構成**して

`∀H, 0<b(H)≤min(B,1/(H+1))`、`∀H,e,p, A_(H,b(H),e,p)<1/(H+1)`

とする。従って、その族では

`¬∃α>0, ∀H, ∃e,p: α≤A_(H,b(H),e,p)`。

同じ族の全有限体積で `∃e,p: A_(H,b(H),e,p)>0` はABLにより成立する。ABKの十分条件そのものは有効だが、**`0<b(H)≤B` だけから全ての許容族に一様な `α>0` を供給する方針は成立しない**。この結論は構成した結合族についてのものであり、量化範囲を拡大しない。

### OPEN — 次の独立入力

固定 `b>0`、または明示した `0<b₀≤b(H)≤B` の領域で、真正Wilsonから一様な絶対重なり、あるいは符号付き事象・全負tailの正の余裕を導く必要がある。結合下限の追加は対象領域の指定であり、一様下界の証明を代替しない。

ABLの事象質量の正の比 `A_p²/(E_b²G)` は有限体積で保持される。ABMの `A_p` の小ささからこの比や事象質量の極限は決まらず、その一様制御も未解決。固定支持cylinder、全物理Hilbert coercivity、共通positive-fine区間、同じE/F、H1–H4、OS/Wightman、連続体Yang–Mills質量ギャップはOPEN。

**以下のABG #6002の題名・「現行」見出し・旧OPENは、その時点の履歴として原文のまま保持する。** 現在の到達点と量化範囲は本追補による。旧PZ37ZAのno-go、先行定理、未解決課題の履歴を削除しない。本同期はREADME/ROADMAPだけのdocs-only変更であり、新規Lean定理を追加せず、Strict Leanを起動しない。

---

# MGAP4D Roadmap

**Current docs mirror (2026-10-29 JST).** This is the default `main` **documentation root**, **not** the theorem-bearing branch. The unique authoritative Lean theorem branch is [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). See its complete [README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/93a6a06c18c7a66f9e29353ea7e2b034b90c0a33/README.md) and [ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/93a6a06c18c7a66f9e29353ea7e2b034b90c0a33/ROADMAP.md). This root mirror does not synchronize Lean sources onto `main`.

## Current verified theorem mirror — ABG / #6002 (2026-10-29 JST)

This `main` is a documentation mirror ONLY; sole formal Lean theorem authority is [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). Source theorem [#6002 / ABG](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6002) MERGED: exact tested source `f752141618f07a5d0c2b1cfd51c5cc2e60bb34d4`, theorem squash `6f68bc2989b7b46b2c3ef1702d521982ed37e521`; [CI #40831840574](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40831840574) **11,171/11,171 SUCCESS**, changed Lean 0/0, five standard-only axioms reports, no `sorryAx`, independent receipt SUCCESS. Latest **theorem-branch docs-only** [#6004](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6004) squash `46e70e32ab3af2b0506c0a9b57f0520d8e192b02` is NOT a new theorem.

**CLOSED finite-volume:** [ABF/ABF2 #6001](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6001) true original pair-Haar `G=K_p+R_p` signed split; `0<G/|P_H|≤K_p` for an actual link/plaquette; actual transfer-compensated local physical GI `|tΔ_local,p|≤E_b/2` and `Mcomp≤(E_b/2)²`, with `t=||T||>0`, `E_b=exp(8b)(exp(16b)−exp(−16b))`. [ABG #6002](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6002) `(tK_p)²≤G Mcomp≤G(E_b/2)²`, hence a genuine finite-H positive G floor from one actual physical correlation. None of these is H-uniform.

**NEXT OPEN:** construct from the ORIGINAL Wilson kernel, true Perron vacuum, Gauss-law physical source, two distinct INTERACTING posteriors and full outer pair-Haar a `κ>0` with `∀H ∃e_H,p_H: t_(H,b(H))K_(H,b(H),e_H,p_H)≥κ`, without recycling unknown `G` or `R` bounds. Signed negative remote tail, local finite-support descent, uniform Haar event mass/amplitude are independent unresolved inputs. All-physical-Hilbert coercivity, common fine window, endpoint E/F, H1–H4, OS/Wightman and continuum mass gap remain OPEN. Preserve PZ37ZA no-go and old ABE/AAZ2 history. No Strict Lean on this docs-only root mirror.

---

## Historical theorem checkpoint and next analytic gate (2026-10-29 JST · ABE)

This **main** roadmap is a historical+current **documentation mirror only**. Unique Lean theorem authority: [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). Latest authoritative root [README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c570350ea9e876fb4e11f6fd947d1b759d5ab7c8/README.md) and [ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c570350ea9e876fb4e11f6fd947d1b759d5ab7c8/ROADMAP.md) are **docs-only** [#5999](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5999), not new Lean theorem commits.

| Checkpoint | Verified authority |
| --- | --- |
| [Latest theorem-bearing PR #5998 — PZ37ABE](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5998) | **MERGED** after #5994 ABA/ABA2, #5995 ABB/ABB2, #5996 ABC/ABC2, #5997 ABD/ABD2 |
| PR source head / squash distinction | tested `25b6cc2bc6171603bfbb909a23918be3a25586b4`; theorem-bearing squash `75bee4a633cb1296a47a85624cd65a0917fddc8d` (canonical authority HEAD immediately after #5998 MERGED) |
| [Exact-head Lean CI #40827511993](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40827511993) | **11,168 / 11,168 SUCCESS**; changed Lean 0 warnings / 0 errors; three standard-only axiom reports, no sorryAx, independent completion receipt SUCCESS |
| Pinned Lean/mathlib | `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

**New CLOSED:** actual FK-based FX cap for positive bounded coupling schedules (no JL legacy native_decide); strictly positive genuine unweighted GI gap moment on some link in every fixed volume; authentic positive original pair-Haar GI event; genuine source-projection two-sided sandwich; exact local plaquette source + full signed residual; original centered local Gauss-law physical Hilbert source; positive-mass same-sign full/local physical GI event; and `Σ_p ∫(GI_full·GI_local,p)dμ_H = G_(H,b,e)>0` with a genuine plaquette having strictly positive **full-Haar-integrated signed correlation**. All are finite-volume results. See authoritative documents for detailed statement scope and separate CI receipts.

**New primary OPEN gate:** prove an **H-independent positive lower bound** `∃m>0, ∀H, ∃e_H: G_(H,b(H),e_H)≥m` from the original interacting Wilson Gauss-law model, not from unknown Rayleigh. Need uniform finite-link genuine physical response/paired Haar mass and signed nonlocal residual cancellation estimates. Neither fixed-H `K>0` nor full-pair-Haar local positivity establishes a common `m`. For any coupling schedule with `0<b(H)≤B`, the genuine FX **upper** bound `q_B` is already proved in ABA; no independent JL axiom import. A uniform fine-zero *source-specific* Rayleigh would still not imply all physical-Hilbert coercivity, common fine window, E/F, H1–H4 or continuum mass gap.

PZ37ZA's impossibility for the **different compensated two-context local-minor quantity** remains valid and must not be generalized to true full-link GL mass. Old AAZ2 and earlier sections below are preserved as labeled historical checkpoints. This docs-only mirror update does not trigger Strict Lean and does not place Lean files on `main`.

---

## Historical main-mirror proof gates — AAZ2 (#5991), 2026-10-29 JST

| Verified evidence | Authority |
| --- | --- |
| Latest theorem-bearing merge | [P4-Q2-PZ37AAZ/AAZ2 #5991](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5991) **MERGED** |
| Tested **PR source** SHA | [`d769e275d016b6645e924a116acb0d7653f7e9a0`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d769e275d016b6645e924a116acb0d7653f7e9a0) |
| Theorem-bearing **squash** SHA | [`20f910f54791d662b687965af231842a27f093b6`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/20f910f54791d662b687965af231842a27f093b6), matching authoritative HEAD just after #5991 merged |
| [Exact-head CI #40814241452](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40814241452) | **11,159 / 11,159 SUCCESS**, AAZ/AAZ2 changed Lean warning/error **0 / 0**, all eight public `#print axioms` standard `propext` / `Classical.choice` / `Quot.sound` only, no `sorryAx`, independent CI completion receipt **SUCCESS** |
| Latest theorem-branch **docs-only** update | [#5992 MERGED](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5992), docs SHA [`93a6a06c18c7a66f9e29353ea7e2b034b90c0a33`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/93a6a06c18c7a66f9e29353ea7e2b034b90c0a33), **not** a new Lean theorem |
| Toolchain pin | Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

### CLOSED — authentic Wilson finite-volume results

The same **genuine** interacting SU(2) Wilson kernel, positive Perron ground state, Gauss-law physical centered source, both interacting one-link posterior laws and original boundary pair-Haar are preserved.

- **AAH–AAK:** for every finite `H,b>0`, the original centered source-specific Rayleigh `R_{H,b}>0` and a real spatial link has positive raw response `J_e>0`. This is not a volume-uniform lower bound.
- **AAU/AAV/AAW [#5986–#5988](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5988):** prove original spatial-translation covariance and relative link participation; one-link signal criteria **do not** themselves produce absolute uniform constants.
- **AAX/AAX2 [#5989](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5989):** actual spatial plaquette count equals spatial link count, original centered Haar covariance `C_H≤24L_H`, and if an original link's unnormalized response `J_e≥ε`, then `R≥ε/18`.
- **AAY [#5990](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5990):** a true measurable outer pair-Haar event with probability `≥ρ`, original interacting-posterior GI gap `|Δ|≥δ`, actual FX variance `0<Q≤q` gives `J_e≥ρδ²/q`.
- **AAZ/AAZ2 [#5991](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5991):** for each finite `H,b>0`, the centered Gauss-law GI expectation gap is **not pair-Haar-a.e. zero** on some actual link. Let `G_e=∫Δ_e²dμ_H` be its **unweighted** squared moment, and `Q_e` the genuine posterior density-difference FX variance. Given an explicit actual `Q_e≤q`, prove `G_e` automatically integrable and `G_e≤qJ_e`; common `G_e≥m>0` and `q>0` imply **conditionally** `R≥m/(18q)>0`.

### OPEN — next rigorous mathematical steps

**Gate A — Priority 1, prove an absolute genuine GI second moment:** construct one real Wilson spatial link `e_H` for *each* original finite volume and a single `m>0` such that

```text
G_(H,b(H),e_H) = ∫ |Δ_(H,b(H),e_H)(z;V_H)|² dμ_H(z) ≥ m   (all H).
```

Do not assume the unknown `R≥c` in this proof. Qualitative non-a.e.-zero at every finite `H` does **not** imply a positive uniform `m`. Candidate work: finite-support genuine pair-Haar cylinder events with volume-uniform probability; show their **actual GI receiver** responds nontrivially despite integration cancellations, and descend the remaining Haar variables without replacing the interacting conditional posterior by independent Haar.

**Gate B — prove a compatible true FX variance cap:** produce a common `q>0` for the chosen genuine frozen schedule `b(H)` and original `Q_{H,b(H),e_H}(z)≤q`. The earlier [JL #5658](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5658) fixed-`b` bound `Q≤(e^{16b}-e^{-16b})²` has **five inherited legacy finite-incidence `native_decide` axioms**. An independently audited standard-axiom proof or explicit dependency account is required; do **not** silently import that legacy chain into AAZ2. AAZ2 proves integrability *conditional on the cap*, not the cap's uniform existence.

**Gate C — apply the already Lean-proved conditional criterion** only after real `m,q` are established: `R_{H,b(H)}≥m/(18q)>0`. The implication is CLOSED; the existence of uniform witnesses is OPEN. This still controls only the one particular **centered** Gauss-law physical source.

**Gate D — source-wide coercivity and positive fine:** all-source Hilbert frame/coercivity, common positive fine-coupling interval, compatible same physical endpoint E/F across scales, arbitrary depths and strong Hilbert limits require separate results. Coefficient-ℓ² frame degeneracy `t↓0` does not settle a source-normalized physical Rayleigh lower bound.

**Gate E — continuum:** H1–H4, Osterwalder–Schrader/Wightman reconstruction, physical Hamiltonian and continuum 4D Yang–Mills existence plus mass gap remain **OPEN**. Never label a conditional finite-volume witness as a solved continuum mass gap.

**Essential distinction:** PZ37ZA [#5935](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5935) disproved the separate bounded **compensated two-context** `Q_GI/N_H` uniform floor, **not** the original true full-link/all-boundary-pair-Haar GL mass. `Q_post` (original FX posterior variance), `Q_GI` (two-context compensated minor energy), `J` (raw true posterior one-link GL signal) and `G` (unweighted genuine GI-gap moment) are different mathematical objects.

**CI/authority rules:** re-observe the current theorem branch SHA; inspect entire changed Lean files/imports/dependent signatures and pinned mathlib APIs; require exact-head **completed** success, changed Lean warnings/errors 0/0, axioms audit, no `sorryAx`, independent CI completion receipt; merge theorem PR only after all checks. A docs-only root change does **not** run Strict Lean, confer theorem authority on `main` or count as a new result.

---

## Historical root ROADMAP archive (2026-10-04)

The original default-`main` roadmap below is preserved as a **dated** #5077/#5078-era record. Its “current”/“next” statements are **historical**, not current mathematical priorities. Earlier finite-volume work, q₀ estimates and old no-go results are not discarded.

Status date: 2026-10-04 JST

Authoritative theorem branch:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

Latest theorem-bearing baseline before this docs refresh:

~~~text
426ad4fe783d030a61687fbb123aca00b90a3d1d
~~~

Latest theorem-bearing branch tip contains both adjacent theorem lines:

~~~text
#5078
Add three-mode two-functional unit-kernel lemma

#5077
Realize all SU(2) Gram-Schmidt Wilson modes as physical pairs

final branch tip after #5077 merge:
426ad4fe783d030a61687fbb123aca00b90a3d1d
~~~

Exact validation:

~~~text
#5077 head:
  aaa6d50c2da21461a76a6a0e6e2f9ee72b518998
#5077 PR Lean Fast Check:
  37157037971
  completed / success
#5077 exact-head receipt:
  success

#5078 head:
  61acb9b380ee3822e5574c1e9fd56e61cba5d64f
#5078 PR Lean Fast Check:
  37156892868
  completed / success
#5078 exact-head receipt:
  success
~~~

Pinned environment:

~~~text
Lean v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
~~~

The default branch main is not theorem authority.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

Docs-only commits are not theorem-bearing baselines.

---

## 0. Executive state

The finite-volume spectral/coercive side is substantially closed.

The exact quantitative endpoint is:

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||
~~~

with the q0 estimate extended to the full completed physical pair non-top sector.

The old completed H1-D5 compatibility is formally refuted at positive SU(2) coupling.

The current task is no longer to prove a vacuum-identification seam.

The active route is now:

~~~text
three theorem-generated coherent orthonormal SU(2) pair modes (#5077)
  +
abstract Fin-3 two-functional unit-kernel selector (#5078)
  ->
instantiate two exact finite scalar constraints
  ->
one normalized nonzero physical non-top pair at every scale
  ->
existing q0^m estimate
  ->
projective strong limit
  ->
evolved projective dynamics
  ->
physical-time scaling
  ->
OS Hamiltonian / mass gap.
~~~

---

## 1. Closed finite-volume quantitative route

Already formalized:

- beta = 0 gap = 1;
- positive-beta finite-volume coercivity;
- explicit high-temperature uniform gap floor;
- one-dimensional physical top eigenspace;
- top-orthogonal natural-power decay;
- completed pair top-top / non-top decomposition;
- pair-top one-dimensionality;
- full completed pair non-top q0 power decay.

The explicit common factor remains

~~~text
q0 = 3071/3072 < 1.
~~~

This part should be treated as a reusable receiver, not repeatedly reproved.

---

## 2. Projective finite-scale carrier — closed kinematics

PRs #4993--#4998 establish the projective L2 carrier used for thermodynamic/common-scale comparison.

Important distinction:

### Independent-product lane

Useful for simultaneous finite-scale comparison.

But fresh-coordinate centered sequences can vanish in the limit.

### Projective lane

Keeps compatible cylinder information across scales and supports nonzero strong limits.

All current continuum-side work should stay on this projective lane.

---

## 3. Explicit finite Wilson pair route — closed

PRs #4999--#5016 provide:

- explicit SU(N) primary-plaquette Wilson modes;
- finite physical one-slice representatives;
- explicit ordered endpoint-pair representatives;
- one-dimensional top eigenspace;
- one-dimensional completed pair TopTop block;
- q0 control on the completed non-top receiver.

These modules are the finite kinematic base used by the later no-go and replacement routes.

---

## 4. Canonical-sign OS vacuum and H1-D4 — closed

### #5017/#5018

The canonical-sign finite OS vacuum is identified with the concrete Wilson boundary vacuum.

Its pair representative is fixed by arbitrary independent endpoint gauge transformations.

### #5022--#5029

The repository proves

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

Thus the canonical-sign OS vacuum pair is physical without any H1-D5 transfer compatibility.

Status: CLOSED.

Do not list H1-D4 as an open seam.

---

## 5. Old completed H1-D5 — formally refuted

PRs #5031--#5061 show that the old completed compatibility is not a harmless technical assumption.

The reduction is:

~~~text
completed H1-D5
  ->
literal finite Wilson identity
  ->
positive-half transfer power identity
  ->
top-orthogonal restriction = 0
  ->
rank-one normalized one-slab transfer
  ->
two-mode Gram degeneracy
  ->
feature-analysis kernel nontrivial.
~~~

The positive-coupling SU(2) strictness chain proves the opposite finite statement on the explicit two-mode sector.

Therefore:

~~~text
beta(n) > 0
  ->
not H1-D5 completed compatibility at scale n.
~~~

Status: CLOSED NO-GO.

Rule:

~~~text
Do not resurrect completed H1-D5,
vacuum/top alignment,
or an equivalent rank-one-forcing statement.
~~~

---

## 6. Post-no-go centered scalar replacement — #5063/#5064

### #5063

The actual vacuum-normalized centered pair receives an exact top-pair scalar expansion.

The associated excitation-level scalar compatibility is strictly weaker than H1-D5.

### #5064

The old SU(2) global vacuum/top alignment route is explicitly excluded.

This is an important design constraint for every later theorem.

---

## 7. Canonical projected non-top finite excitation — #5065--#5067

### #5065

For the actual centered finite pair, define:

~~~text
TopTop projection
NonTop projection.
~~~

The projected vector is automatically:

~~~text
in PhysicalPairCarrier,
orthogonal to TopTop,
therefore controlled by q0^m.
~~~

No transfer compatibility is assumed.

### #5066

Nonzero projected excitation is reduced to a nonzero finite OS-vacuum / pair-top overlap.

### #5067

That overlap is proved strictly positive.

Hence at every finite scale:

~~~text
exists k : Fin 2,
projected centered mode k != 0,
and
||S_pair^m x|| <= q0^m ||x||.
~~~

Status: CLOSED.

---

## 8. Common projective carrier for projected modes — #5068/#5069

### #5068

Embed the projected non-top finite modes into one common projective continuum L2 carrier.

The embedding is norm preserving.

### #5069

Among the two selected labels, choose one fixed label on an infinite increasing scale subsequence such that the projected mode stays nonzero.

This establishes a robust finite-to-projective kinematic lane.

Status: CLOSED.

---

## 9. Strong-convergence factorization — #5070--#5074

### #5070

The projected common image is exactly

~~~text
centered common image
  -
<top common image, centered common image>
  * top common image.
~~~

So the scalar coefficient is not an independent object.

### #5071

The uncentered pair common image is eventually exactly one fixed continuum mode.

Thus centered convergence is reduced to:

~~~text
OS-vacuum pair common image
+
pair-top common image.
~~~

### #5072

The canonical-sign OS-vacuum pair common image is exactly constant one at every scale.

Therefore the centered common image already converges.

### #5073

For unit top images:

~~~text
top image -> 1 strongly
  iff
finite vacuum/top overlap -> 1.
~~~

This is valid but stronger than needed.

### #5074

Generic Hilbert lemma:

~~~text
c_n -> c,
||t_n|| = 1,
<t_n,c_n> -> 0
  ->
c_n - <t_n,c_n> t_n -> c.
~~~

Therefore the only needed scalar input is:

~~~text
local projected-top coefficient -> 0.
~~~

No convergence of the moving top direction is required.

Status: CLOSED REDUCTION.

---

## 10. Positive-half factorization of the local coefficient — #5075/#5076

### #5075

For arbitrary physical one-slice x,y:

~~~text
<v_OS, x tensor y>
  =
<v_OS, omega tensor omega>
  *
<S_half x, y>.
~~~

This is exact and normalization free.

No H1-D5 or vacuum alignment is used.

### #5076

For the explicit two-mode pair f_k tensor 1:

~~~text
a_k
  =
alpha_k * delta
  -
gamma^2 * m_k,
~~~

where

~~~text
alpha_k = <omega, f_k>,
delta   = <omega, 1>,
gamma   = <v_OS, omega tensor omega>,
m_k     = <S_half f_k, 1>.
~~~

This converts the pair-Haar local coefficient into one-slice data.

Status: CLOSED.

Interpretation:

The old conditional route could try to control the excitation part of m_k by q0 and separately control the fidelity defect involving gamma.

That route remains available, but it is no longer preferred because #5077 opens a cleaner finite-dimensional construction.

---

## 11. #5077 — all SU(2) Gram--Schmidt Wilson modes are physical pairs

File:

~~~text
MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2GramSchmidtPairPhysical.lean
~~~

PR #5077 proves, for every SU(2) Wilson-energy Gram--Schmidt mode k:

1. the primary spatial plaquette continuous observable is defined explicitly;
2. it is gauge invariant;
3. it gives a physical one-slice L2 vector;
4. the ordered endpoint-pair boundary realization is exactly decomposable;
5. the pair belongs to the completed physical pair carrier;
6. the whole endpoint-pair family is orthonormal in pair Haar L2.

Schematically:

~~~text
u_k,n in PhysicalPairCarrier

<u_i,n, u_j,n> = delta_ij.
~~~

This is the key new kinematic resource.

Status: CLOSED.

---

## 12. #5078 — pure three-mode two-functional selector CLOSED

PR #5078 proves the finite-dimensional theorem independently of the Yang--Mills model.

File:

~~~text
MGAP4D/MathlibAnalytic/RealEuclideanFinThreeTwoFunctionalKernel.lean
~~~

Input:

~~~text
two real linear functionals
  ell_0, ell_1
on
  EuclideanSpace R (Fin 3).
~~~

Output:

~~~text
exists c,
||c|| = 1,
ell_0(c) = 0,
ell_1(c) = 0.
~~~

The proof uses pinned-mathlib rank-nullity through:

~~~text
LinearMap.ker_ne_bot_of_finrank_lt
~~~

and normalizes a nonzero common-kernel vector.

Status: CLOSED.

### 12.1 Immediate model-facing instantiation

Use the first three #5077 physical pair modes:

~~~text
u_0,n
u_1,n
u_2,n.
~~~

Define the synthesis

~~~text
Syn_n(c)
  =
sum k : Fin 3, c_k * u_k,n.
~~~

Prove from #5077 orthonormality:

~~~text
||Syn_n(c)|| = ||c||.
~~~

Define the two functionals required by #5078:

~~~text
Vac_n(c)
  =
<v_OS,n, Syn_n(c)>

Top_n(c)
  =
<Omega_pair,n, Syn_n(c)>.
~~~

Apply #5078 to obtain c_n with

~~~text
||c_n|| = 1
Vac_n(c_n) = 0
Top_n(c_n) = 0.
~~~

Set

~~~text
x_n = Syn_n(c_n).
~~~

Target finite package:

~~~text
||x_n|| = 1
<v_OS,n,x_n> = 0
<Omega_pair,n,x_n> = 0
x_n in PhysicalPairCarrier
x_n in PairNonTop
||S_pair,n^m x_n|| <= q0^m.
~~~

Because the vacuum pairing is zero, finite vacuum-centering leaves x_n unchanged.

Because pair TopTop is one-dimensional, pair-top scalar orthogonality gives exact non-top membership.

This is now the immediate theorem target.

## 13. Projective limit of the scale-dependent three-mode selector

The coefficient vector now depends on scale.

So fixed-label projective coherence alone is not sufficient.

However:

~~~text
||ĉ_n|| = 1
~~~

places every coefficient vector on the compact unit sphere in R^3.

### 13.1 coefficient subsequence

Use finite-dimensional compactness / Bolzano--Weierstrass to obtain:

~~~text
exists phi : N -> N,
StrictMono phi,
ĉ_(phi j) -> c_infinity,
||c_infinity|| = 1.
~~~

Pinned mathlib contains sequence compactness tools such as:

~~~text
IsSeqCompact
tendsto_subseq_of_bounded
~~~

Either route is acceptable.

### 13.2 coherent continuum modes

The existing SU(2) Gram--Schmidt cylinder/readout machinery gives a fixed continuum projective mode U_k for every fixed k.

Use only k = 0,1,2.

### 13.3 synthesis convergence

Show:

~~~text
Embed(x_(phi j))
  =
sum k<3, ĉ_(phi j,k) U_k
~~~

eventually / exactly at containing scales.

Then continuity of finite sums gives:

~~~text
Embed(x_(phi j))
  ->
y =
sum k<3, c_infinity,k U_k.
~~~

### 13.4 nonzero limit

Because U_0,U_1,U_2 are orthonormal and ||c_infinity|| = 1:

~~~text
||y|| = 1.
~~~

Thus:

~~~text
y != 0.
~~~

This should give the cleanest current nonzero projective initial excitation.

---

## 14. Why three modes are preferable to two

With two modes one can always solve one scalar top-orthogonality equation.

But after vacuum centering, the selected one-dimensional kernel can in principle coincide with a vacuum direction and collapse to zero.

Three modes allow two exact scalar conditions simultaneously:

~~~text
vacuum pairing = 0
pair-top pairing = 0.
~~~

The remaining kernel still has dimension at least one.

Therefore nonzero norm can be guaranteed before centering.

This is the dimensional reason for the #5077 extension from two modes to the full Gram--Schmidt family.

---

## 15. Relation to #5074--#5076

The local coefficient route remains mathematically correct.

It is useful for:

- diagnostics;
- quantitative estimates;
- comparing fixed-mode and moving-combination approaches;
- possible later bounds on selected coefficient families.

But the three-mode kernel route should not require:

~~~text
gamma_n -> 1
~~~

or any equivalent global vacuum/top fidelity statement.

If the three-mode route closes cleanly, #5074--#5076 become supporting structure rather than the main seam.

---

## 16. H1-C3: evolved projective dynamics remains open

Even after a nonzero initial strong limit y is built, one still needs the evolved states.

For fixed natural time m define finite evolved states:

~~~text
z_n,m = S_pair,n^m x_n.
~~~

Known:

~~~text
||z_n,m|| <= q0^m.
~~~

Unknown:

- do the z_n,m have coherent projective images?
- do they have strong limits along the same subsequence?
- are the limits compatible in m?
- do they define one bounded operator T on the continuum excitation space?
- is T symmetric/self-adjoint in the required sense?

Target:

~~~text
Embed(z_n,m) -> T^m y

and

||T^m y|| <= q0^m ||y||.
~~~

This is the next genuinely dynamical bridge.

---

## 17. Do not overclaim from finite q0

The statement

~~~text
||S_n^m x_n|| <= q0^m
~~~

is a finite discrete-time estimate.

It does not yet prove:

- existence of a continuum transfer operator;
- strong continuity in physical time;
- a continuum Hamiltonian;
- a positive physical mass.

Every README / paper statement must preserve this distinction.

---

## 18. H2: spacing-scaled physical time

If lattice spacing a_n tends to zero, a fixed q0 gives

~~~text
q0^floor(t/a_n) -> 0
~~~

for every fixed t > 0.

Therefore q0 by itself corresponds to instantaneous collapse under naive physical-time scaling.

A nontrivial physical semigroup requires a scale-sensitive rate, for example:

~~~text
q_n =
exp(-m_n a_n + o(a_n)).
~~~

Equivalent formulations may use:

- transfer logarithms;
- rescaled Dirichlet forms;
- Poincare inequalities;
- generator lower bounds.

Existing repository modules for physical-time rate extraction should be used only after H1-C3 produces actual continuum dynamics.

---

## 19. H3: OS reconstruction

After H1/H2 produce model data, required output is:

- continuum physical Hilbert space;
- normalized vacuum;
- strongly continuous contraction semigroup;
- symmetry / self-adjointness;
- closed Hamiltonian;
- identified vacuum-orthogonal excitation sector.

Much generic functional analysis is already formalized.

The remaining issue is model-facing input.

---

## 20. H4: spectral / Wightman mass gap

Final intended route:

~~~text
finite coercivity
  ->
finite exact non-top excitation
  ->
nonzero projective strong limit
  ->
projective evolved dynamics
  ->
physical-time scaling
  ->
OS Hamiltonian
  ->
spectral lower bound above vacuum
  ->
Wightman / energy-momentum mass gap.
~~~

No current theorem claims the final step is complete.

---

## 21. Lean implementation guidance

Repository-specific lessons to preserve:

### Exact environment

Use:

~~~text
Lean v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
~~~

Current-master theorem names are only hints.

Pinned mathlib is authoritative.

### Full-file audit

When CI fails:

- inspect every error in the changed file;
- do not patch only the first line;
- inspect neighboring theorem signatures;
- identify whether failure is mathematical, coercional, or elaborational.

### Section variables

Lean resolves theorem headers before processing the proof body.

If a section parameter does not occur in a result type strongly enough to infer it, pass it explicitly:

~~~text
(halfExtent := halfExtent)
~~~

### Rewriting through coercions

If rw cannot see the intended occurrence:

- prefer exact theorem terms;
- prefer simpa only using;
- expose the exact coercion boundary;
- avoid relying on pretty-printed syntactic similarity.

### Definitional aliases

Avoid brittle change when crossing several named aliases.

Prefer:

- unfold the exact wrapper definitions;
- then apply the core theorem.

### CI

For theorem-bearing PRs:

- require exact-head PR Lean Fast Check success;
- require matching exact-head receipt success.

For docs-only PRs:

- do not rerun strict Lean merely because README / ROADMAP changed.

---

## 22. Recent milestone ledger

| PR | Status | Main result |
| --- | --- | --- |
| #5029 | merged | independent gauge-fixed pair sector = physical pair carrier |
| #5038 | merged | H1-D5 forces one-slab power identity |
| #5041 | merged | H1-D5 forces rank-one normalized transfer |
| #5045 | merged | two-mode feature-kernel obstruction |
| #5058 | merged | positive-coupling strict bare crossing Gram |
| #5059 | merged | continuous SU(2) two-mode span = span{1,r} |
| #5061 | merged | completed H1-D5 no-go |
| #5063 | merged | centered-pair scalar replacement |
| #5064 | merged | old vacuum/top alignment route excluded |
| #5065 | merged | canonical projected physical non-top excitation |
| #5066 | merged | projected nonzero reduced to vacuum/top overlap |
| #5067 | merged | finite projected excitation nonzero |
| #5068 | merged | common projective embedding |
| #5069 | merged | fixed nonzero mode on infinite subsequence |
| #5070 | merged | projected strong-convergence factorization |
| #5071 | merged | centered convergence reduced to vacuum/top common images |
| #5072 | merged | OS vacuum pair common image = constant one |
| #5073 | merged | pair-top convergence iff vacuum/top overlap -> 1 |
| #5074 | merged | local top-coefficient criterion |
| #5075 | merged | OS-vacuum coefficient factorization through normalized half transfer |
| #5076 | merged | exact one-slice local top coefficient formula |
| #5077 | merged | all SU(2) Gram--Schmidt modes realized as physical orthonormal endpoint pairs |
| #5078 | merged | abstract Euclidean Fin 3 two-functional unit-kernel selector |

---

## 23. Immediate implementation sequence

### G1 — three-mode synthesis

Create the finite linear synthesis of the first three #5077 pair modes and prove its norm formula from orthonormality.

### G2 — instantiate #5078

Define the vacuum-pairing and pair-top-pairing linear functionals on Euclidean Fin 3 and feed them directly to RealEuclideanFinThreeTwoFunctionalKernel.

### G3 — exact finite non-top unit excitation

Synthesize x_n and prove:

~~~text
||x_n|| = 1
<v_OS,n,x_n> = 0
<Omega_pair,n,x_n> = 0
x_n in PhysicalPairCarrier
x_n in PairNonTop.
~~~

### G4 — q0 receipt

Apply the existing completed pair non-top power theorem:

~~~text
||S_pair,n^m x_n|| <= q0^m.
~~~

### G5 — coefficient compactness

Extract a convergent unit coefficient subsequence in R^3.

### G6 — projective synthesis convergence

Transport the three fixed coherent Gram--Schmidt modes and show the selected combinations converge strongly.

### G7 — nonzero continuum excitation

Prove the limit has norm one.

### G8 — evolved projective coherence

Begin H1-C3 with the same selected subsequence.

This is the preferred next formalization order.

---

## 24. Restart instructions

Freshly re-observe:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

Then inspect:

1. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2GramSchmidtPairPhysical.lean
2. MGAP4D/MathlibAnalytic/RealEuclideanFinThreeTwoFunctionalKernel.lean
3. MGAP4D/MathlibAnalytic/SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt.lean
4. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtCylinder.lean
5. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadout.lean
6. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedProjectedLocalTopCoefficientCriterion.lean
7. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedPairPositiveHalfTransferRatio.lean
8. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedLocalTopOneSliceFormula.lean
9. the full completed physical pair non-top q0 power-decay theorem from #5006.

Current handoff:

~~~text
CLOSED:
  finite q0
  full completed pair non-top q0
  top and pair-top simplicity
  H1-D4
  completed H1-D5 no-go
  finite nonzero projected excitation
  projective embedding
  vacuum common image = one
  local coefficient criterion
  half-transfer/local coefficient factorization
  infinite SU(2) Gram--Schmidt physical orthonormal pair family

NEXT:
  instantiate #5078 on the three #5077 pair modes
  ->
  unit exact non-top pair at every scale
  ->
  q0
  ->
  coefficient compactness
  ->
  nonzero projective strong limit

THEN:
  evolved projective dynamics

THEN:
  physical-time scaling

LATER:
  OS Hamiltonian
  spectral / Wightman mass gap.
~~~


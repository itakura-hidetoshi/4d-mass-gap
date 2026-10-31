# MGAP4D — 定理正本ロードマップ追補（2026-10-31 JST／P4-Q2-PZ37ACA）

- **唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。
- **最新定理：** [ACA #6043](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6043) **MERGED**。定理squash＝マージ直後正本HEAD `055efd930b9c45a3894282c9a6023db2abe3a753`。exact-source `cdfdcc1a9150a1716b6f9153b400e25bbdbfc56f` と同一tree `644c5d603630fb0266eb2099181dc16fdb5f7b96`。
- **検証：** [CI #41171556328](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41171556328) workflow/job/Lean step completed / SUCCESS、Lean **11,175 / 11,175 SUCCESS**、4新規Lean葉・43公開定理・43件の標準3公理以内の公理依存、sorryAxなし、変更warning/error 0/0。独立receipt [job #124451395379](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41171556328/job/124451395379) SUCCESS。
- **固定：** Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6。元Wilson模型・物理源・Perron・transfer norm・二posterior・公開root不変。

## CLOSED — ABZ全不整合上界の厳密な最適化

v=Var(F_z)、C=Cov(F_z,E)、s²=1とすると、Q(a)=(b/a)Var(F_z+s*aE)の下限は `B_s=b*(sqrt(v)+2*s*C)`。全M_{-s}≤B_s、Q(a)-B_s=b/(4a)*(a-2sqrt(v))²、任意tに対し `(∃a>0,Q(a)<t)↔B_s<t` を証明。v=0、b=0も含む。これはABZ残差族内の最適性であり、実GIやMの厳密値ではない。

D=VarF-4Cov(F,E)²=Var(F-4Cov(F,E)E)≥0、Var(F+s*aE)=D+(s*a+4Cov(F,E))²/4、2|Cov|≤sqrt(VarF)を証明。分散回帰の係数とtail上界の最適傾きを区別する。

## CLOSED — 真Perron断面と実物理分散の上下界

F=C₀-PU、P>0の真正表示からVarF=P²VarU、Cov(F,E)=-P Cov(U,E)、σ_F=Pσ_U、D_F=P²D_U、残差の厳密輸送を証明。最適上界は `bP*(sqrt(VarU)-2sCov(U,E))`。

元FF/FC係数 `K=‖T‖⁻¹*((exp(8b))³-1)*‖f‖` からVarF≤K²、σ_F≤K、M_{-s}≤b*(K+2sCov(F,E))。元共分散を残すが、Kによる粗い十分条件を最適化の必要条件へ取り違えない。真TnormはH依存のまま。

ABXのz∈Aでは `VarF≥η²ν(V)/2>0`。従ってa*(z)=2sqrt(VarF)>0で最適値を実際に達成する。ν=補助SU2二コピーHaar。ABV固定capの1/64は流用しない。

## CLOSED / CONDITIONAL — 正の残差証明書の必要十分条件

ここでは `s=R.sign` とし、η・κ・Vも同じABX rectangle Rの値を使う。最適化するパラメータは正の傾きaである。

各zであるa>0がABZ残差下界を厳密正にすることと `B_s(z)<exp(-64b)ηκν(V)` が同値。この閾値に失敗すれば、この評価族でaを調整しても正値認証はできない。実GIの非正値性ではない。

元posterior全負tail≤exp(32b)B_s、z∈Aで `sΔ_GI(z)≥L_*(z)=[exp(-32b)ηκν(V)-exp(32b)B_s(z)]/2`。A全体でL_*≥δ≥0という別の明示条件から、真の外側pair-Haar λ_Hで `∫Δ_GI²dλ_H≥λ_H(A)δ²`。共通aや可測な傾き選択は不要。必要条件が元の中心化物理源で充足されたとは主張しない。

## OPEN — 次段階P4-Q2-PZ37ACB

1. 真正中心化Gauss-law源のU_zを解析し、望ましい共分散方向と実D_Uを評価して `bP*(sqrt(VarU)-2sCov(U,E))<exp(-64b)ηκν(V)` を証明する。
2. 元spatial Haar-L²の源中心化を固定リンク受信器平均ゼロやPerron真空中心化へ置換しない。MQの別Riesz商の局所性を真Uへ転用しない。
3. K、P、η、κ、A、VのH依存、固定support cylinder、遠方相殺を評価し、真Gram/Rayleigh一様下界へ進む。小bの因子だけで正寄与との比較が解決したとはしない。
4. ABSの粗Haar中心化誤差障害、ABM／PZ37ZA no-goを保持。全物理Hilbert coercivity、common fine-positive、同一endpoint E/F、H1–H4、OS/Wightman、4D連続体Yang–Mills mass gapはOPEN。

GitHub MCPで正本HEAD、変更Lean全文/imports/依存署名/固定API、exact-source workflow/job/Lean step、公理依存、独立receipt、squash/source treeと正本HEADを再確認。docs-onlyでは追加Strict Leanなし。

**以下のABZ以前の節は当時の履歴として完全に保存する。**

---
# MGAP4D — 定理正本ロードマップ追補（2026-10-31 JST／P4-Q2-PZ37ABZ）

- **唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default mainは文書ミラー。
- **最新定理：** [ABZ #6040](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6040) **MERGED**。squash＝マージ直後正本HEAD `bf7d9575a7f3f25e041b901e00a72f3034ccd244`。exact-source `f1499f8d2d20e97e0f5a111e60628d35b6c6b7d5` と同一tree `971fc2f9be67aa8eb9e150d355dceaff037eb29e`。
- **exact-source検証：** [CI #41168743376](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41168743376) workflow・job・Lean step completed / SUCCESS、Lean **11,171／11,171 SUCCESS**、3新規Lean葉・35公開定理・35公理依存報告が標準3公理以内、sorryAxなし、変更warning/error 0/0。独立completion receipt [#124442869146](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41168743376/job/124442869146) SUCCESS。
- **固定：** Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6。元Wilson模型、Gauss-law源、真Perron、transfer norm、二posterior、公開root不変。

## CLOSED — 全不整合モーメントの実エネルギー残差上界

元の `Ψ_s=2bs(F(g)-F(h))(E(h)-E(g))`、`M_{-s}=∫max(-Ψ_s,0)d(μ×μ)` に対し、`R=F+s*a*E` とすると

`M_{-s} ≤ (b/a) Var_μ(R)`  （b≥0、a>0、sは任意の実数）

を点ごとの平方完成と `∫(R(g)-R(h))²=2Var_μ(R)` から証明。Haar分散が中心化二乗積分と一致すること、可積分性も証明済み。tailや残差が小さいという仮定を使わない。元の真SU(2) Haarで `∫E=1, ∫E²=5/4, VarE=1/4`、従って

`Var(R)=Var(F)+2*s*a*Cov(F,E)+(s*a)²/4`。

## CLOSED — 元FF/GN転送構造と符号付き共分散障害

`F(g)=‖T‖⁻¹I_f(B)-P(z)U_z(g)`、
`P(z)=‖T‖⁻¹sqrtDensity(z)>0`、
`U_z(g)=I_f(B[e:=g])/sqrtDensity(z.left,B[e:=g])`。

元右リンク更新と更新後Perron半密度を含むこの真正断面の連続性、二更新差、全M_{-s}の厳密表示をLean証明。MQの局所Riesz商をUの有限supportへ取り違えない。

`M_s-M_{-s}=-4bs Cov(F,E)` と全負部分の絶対変動＋共分散分解も確定。`s Cov(F,E)≥0` ならABYの下界 `[e^{-32b}M_s-e^{32b}M_{-s}]/2≤0`。**実GIの符号へのno-goではなく、この比較式で正値を認証するための共分散方向の障害。**

## CLOSED / CONDITIONAL — 完全負tailから元外側Haar二次モーメントへ

ABYの元posterior全負tailは `e^{32b}(b/a)Var(R)` 以下。ABXの真正長方形で

`sΔ_GI(z)≥[e^{-32b}ηκν(V)-e^{32b}(b/a)Var(R_z)]/2`。

この下界の厳密正値には `(b/a)Var(R_z)<e^{-64b}ηκν(V)` の実模型での検証が必要で、これは未証明。

この右辺がA全体でδ≥0以上という**別の明示条件**が検証されれば、真の外側pair-Haarについて `∫Δ_GI²dμ_H≥μ_H(A)δ²`。残差条件を実模型で充足したとは主張していない。ν=補助SU2二コピーHaar、μ_H=元configuration pair-Haarを保持し、ABV固定capの1/64はABXのVに流用しない。

## OPEN — 次段階P4-Q2-PZ37ACA

1. 真正中心化物理源の更新後Perron転送断面Uを使い、実際の `Var(F)`、`Cov(F,E)`、`Var(F+s*a*E)` を評価する。任意a>0の上界の最適化と、上界が正寄与より小さいことの証明を分ける。
2. 係数b/aとVarE=1/4のH非依存を、残差・A,V・η,κのH一様性へ取り違えない。固定support cylinder、遠方相殺、共通Haar質量・振幅と真Gram/Rayleigh下界は未確立。
3. ABSの粗いHaar中心化絶対誤差障害、ABM・PZ37ZA no-goを保持。元源・真Perron・真transfer norm・二interacting posteriorsを変更しない。
4. 全物理Hilbert coercivity、common fine-positive、同一endpoint E/F、H1–H4、OS/Wightman、4D連続体Yang–Mills mass gapはOPEN。

GitHub MCPで正本HEAD→変更Lean全文・imports・dependent signatures・固定mathlib→exact-source workflow/job/Lean step→公理依存・独立receipt→squash/source treeと正本HEAD一致を確認。docs-onlyではStrict Leanを追加実行しない。

**以下のABY以前の節は当時の履歴として完全に保存する。**

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

**唯一のLean定理正本：** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラーであり、Lean定理正本ではない。



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

**README/ROADMAP同期はdocs-only。** 新しいLean証明の代わりにはならず、`main` を定理正本にしない。この文書変更だけを理由にStrict Leanを再実行しない。次の定理変更では、その完全source・imports・依存signatures、exact-source CI、変更ファイル診断、公理監査、別completion receiptを実際に確認する。結果と表記の要約は[README.md](README.md)。

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

# MGAP4D — 証明ロードマップ（2026-10-29 JST／現行 P4-Q2-PZ37ABG・PR #6002までMERGED）

## 現行の定理正本：P4-Q2-PZ37ABG／PR #6002までMERGED（2026-10-29 JST）

唯一の定理正本：[`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラーであり定理正本ではない。

| 監査項目 | 確定値 |
| --- | --- |
| 最新定理-bearing PR | [#6002 ABG](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6002) MERGED。前段 [#6001 ABF/ABF2](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6001) MERGED |
| #6002 exact-source-head | `f752141618f07a5d0c2b1cfd51c5cc2e60bb34d4` |
| #6002 squash／マージ直後の定理正本HEAD | `6f68bc2989b7b46b2c3ef1702d521982ed37e521` |
| [#6002 completed CI](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40831840574) | 11,171/11,171 SUCCESS、変更Lean warning/error 0/0、新規5定理標準3公理のみ、`sorryAx`なし、独立completion receipt SUCCESS |
| Lean/mathlib | `v4.30.0-rc2`／`5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

### 追加CLOSED — 真正Wilsonの体積依存を保持した新しい定量的比較

- **ABF [#6001](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6001)**：真正物理プラケット源の完全pair-Haar符号付き交差相関 `K_(H,b,e,p)` は `Σ_p K_p=G_(H,b,e)` を満たす。選択した実プラケットに対して `G=K_p+Σ_(q≠p)K_q` とその**符号付き**残余を厳密保持。ある実リンク・プラケットで `0<G/|P_H|≤K_p`。絶対残余制御でも体積一様下界でもない。
- **ABF2 [#6001](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6001)**：元の物理一スラブ転送ノルム `t_(H,b)>0` を保持した真正局所Gauss-law GI応答に `|t Δ_local,p(z)|≤E_b/2`、`Mcomp=∫(tΔ_local,p)²dμ_H≤(E_b/2)²`。ここで `E_b=exp(8b)(exp(16b)−exp(−16b))` は体積非依存。元の二つの**相互作用する**Wilson posteriorと完全外側pair-Haarは不変更。
- **ABG [#6002](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6002)**：真正pair-Haar `L²` Cauchy–Schwarzから `(tK_p)²≤G Mcomp≤G(E_b/2)²`、したがって `G≥(tK_p)²/(E_b/2)²`。毎有限体積で実リンク／プラケットの正の証人が存在するが、その定数は `H` に依存し得る。

### 次のOPEN — ABHの独立入力

`∃κ>0, ∀H, ∃e_H,p_H: t_(H,b(H)) K_(H,b(H),e_H,p_H)≥κ` を既知の`G`や`R`の一様下界から逆算することなく、真正Wilsonから示す。有限`H`の同符号開領域は、`H`一様な測度・振幅・遠方の符号付き負残余制御を保証しない。これらを明示した独立の局所／descent証明が未完了。正の`κ`と`E_b≤E_B`が揃った場合に限り`G≥4κ²/E_B²`が従う。

全物理Hilbert coercivity、共通positive-fine区間、endpoint E/F、H1–H4、OS/Wightman、連続体Yang–Mills質量ギャップはOPEN。旧PZ37ZAのno-goは保持。**以下のABE・AAZ2など旧節は時点履歴であり、現行正本の上位authorityではない。** 今回はdocs-onlyでLean定理を追加せず、Strict Leanを起動しない。

---

## 履歴：当時の定理正本 P4-Q2-PZ37ABE／PR #5998 MERGED（2026-10-29 JST）

唯一の定理正本は [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。default `main` は文書ミラーで、Lean定理正本ではない。

| 正本監査 | 最新確定値 |
| --- | --- |
| 最新定理bearing PR | [#5998 — P4-Q2-PZ37ABE](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5998) **MERGED**（前段 [#5994](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5994)・[#5995](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5995)・[#5996](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5996)・[#5997](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5997) もMERGED） |
| exact-source-head | `25b6cc2bc6171603bfbb909a23918be3a25586b4` |
| 最新定理bearing squash SHA | [`75bee4a633cb1296a47a85624cd65a0917fddc8d`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/75bee4a633cb1296a47a85624cd65a0917fddc8d)：#5998マージ直後に正本HEADと完全一致 |
| [exact-head CI #40827511993](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40827511993) | **Lean 11,168 / 11,168 SUCCESS**、変更Lean warning/error **0/0**、新規3定理の公理依存 `propext`/`Classical.choice`/`Quot.sound` のみ、`sorryAx`なし、独立completion receipt SUCCESS |
| 固定環境 | Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

### 直近のCLOSED：真正Wilson物理源と符号付き積分まで

- **ABA/ABA2 #5994：** 真正FK posterior密度二側評価から `Q≤(e^(16b)-e^(-16b))²` を、歴史的JLの5件の `native_decide` 公理を継承せず直接Lean証明。任意の有限 `H,b>0` に真正GI重みなし二乗モーメントが正のリンクが存在。さらに `0<b(H)≤B` なら **共通FX上界 `q_B>0` はCLOSED**。
- **ABB/ABB2 #5995：** 正の原pair-Haar測度を持つ真正GI開集合を有限体積ごとに構成。真正GB物理源射影 `α` の二乗モーメントと `G=∫Δ² dμ_H` のGA/ABAを用いる体積非依存二側比較。各 `H` での正値性のみ。
- **ABC/ABC2 #5996：** 元の中心化Wilson Gauss-law源を実プラケットのHaar中心化源の有限和へ正確に分解。元のGI差は各プラケット寄与の総和、任意の一プラケットと**符号付き全残余**への厳密分解、少なくとも一つの局所源GI寄与の非a.e.ゼロを証明。
- **ABD/ABD2 #5997：** 既存LOの真正局所プラケットGauss-law物理Hilbert源とGI寄与を同一視。全Wilson源GI応答と実局所物理GI応答が**同符号の積**を持つ正測度の開pair-Haar領域を構成。
- **ABE #5998：** 真正局所物理源との全pair-Haar符号付き交差積分 `K_(H,b,e,p)=∫Δ_full Δ_local,p dμ_H` に関して **`Σ_p K_(H,b,e,p)=G_(H,b,e)`**。各有限体積で真正リンク・プラケットを選べば **`K_(H,b,e,p)>0`** が、**すべての残余原Haar変数を積分した後にも**成立することをLean証明。これは体積一様正値を意味しない。

### なおOPEN：モデル内で実在する体積一様定量証人

最優先は、元の中心化Gauss-law Wilson物理源と真正二posterior・完全pair-Haarのまま
`∃m>0, ∀H, ∃e_H, G_(H,b(H),e_H)≥m` を**実証**すること。ABA2の有限`H`での`G>0`、ABD2の正測度の同符号領域、ABEの`K>0`はいずれも、共通の振幅・測度・Haar積分後の量的下界を含まない。真の4リンク局所**入力**から非局所Perron/Wilson GI**応答**への依存を精密化し、体積一様な局所寄与または符号付き残余相殺の制御を証明する。正の局所開集合をH共通の有限座標支持円筒と混同しない。

**FX上界ゲートは条件 `0<b(H)≤B` の下でABAにより閉じた**。歴史的JL #5658の追加公理を無検証で取り込まない。任意の上限なし変動結合には、共通上界を主張しない。PZ37ZAで否定した補償済み二文脈 `Q_GI/N_H` の一様正下界を復活させない。

全物理Hilbert空間coercivity、共通positive-fine区間、同一endpoint E/F、任意深さ、H1–H4、OS/Wightmanおよび連続体4D Yang–Mills質量ギャップは引き続きOPEN。以降の旧AAZ2章と旧Gate A–Eは**当時の履歴**であり、この最新のCLOSED/OPEN判定より優先しない。

**文書更新はdocs-onlyであり新しいLean定理ではない。** Strict Leanは不要。CIのcompleted判定は定理-bearing PRのexact-head receiptからのみ採る。古い証明・no-go・引用は削除しない。

---



## 履歴：PZ37AAZ2時点の証明正本（2026-10-29 JST）

唯一の定理正本は [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。**default `main` は定理正本ではない。** 真正有限体積SU(2) Wilson一スラブkernel、正Perron真空、Gauss-law物理Hilbertと元の中心化源`V_H`、**二つの相互作用するWilson条件付きposterior**、本物のSU(2) Haar・境界pair-Haar・GI受信器を変更しない。

| Authority | 確定値 |
| --- | --- |
| 最新定理PR | [#5991 AAZ/AAZ2](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5991) **MERGED** |
| exact-headテスト対象PR source | [`d769e275d016b6645e924a116acb0d7653f7e9a0`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d769e275d016b6645e924a116acb0d7653f7e9a0) |
| theorem-bearing squash SHA | [`20f910f54791d662b687965af231842a27f093b6`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/20f910f54791d662b687965af231842a27f093b6)、#5991マージ直後の正本HEADと完全一致 |
| [CI #40814241452](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40814241452) | **Lean 11,159 / 11,159 SUCCESS**、変更Lean2ファイルwarning/error **0/0**、8定理`#print axioms`＝`propext`/`Classical.choice`/`Quot.sound`のみ、`sorryAx`なし、独立completion receipt SUCCESS |
| 固定環境 | Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

このsquashは**定理統合時点**の記録。後続README/ROADMAPだけのマージでbranch HEADが変わっても新しいLean定理を証明したことにはならない。source SHAとsquash SHAは区別する。

## 直近のCLOSED — 有限体積の正値性と真正Wilsonモデル固有の判定

| 段階 | 証明済み | 閉じていないこと |
| --- | --- | --- |
| PZ37ZA [#5935](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5935) | 真の**補償済み二文脈**`Q_GI/N_H`の体積一様正下界は不可能。 | **全リンク・全文脈posterior積分**のGL massや4D質量ギャップのno-goではない。 |
| AAH–AAK [#5973–#5976](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5976) | 全有限`H,b>0`で真正中心化物理源の`R_{H,b}>0`、`C_H=4‖V_H‖²>0`、`J_e≥0`、`R=(4/C_H)Σ_eJ_e`、一つの正の実リンク応答`J_e>0`。 | `inf_H R_{H,b(H)}>0`は未証明。 |
| AAQ–AAU [#5982–#5986](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5986) | 元の空間Haar・Wilson kernel・正Perron・二posterior・GI/FXの**無条件並進共変性**。`M₂≤3R²`、参加率`P≥1/3`。 | 相対集中度の制御のみ。絶対的`R`下界にはならない。 |
| AAV [#5987](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5987)・AAW [#5988](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5988) | 3つの真正空間方向の一方向の全リンクで`j_e≥R/L_H`、活性密度`≥1/3`。一リンク`j_e≥3c/L_H`は`R≥c`に十分。 | 正の体積一様一リンク証人は未構成。 |
| AAX/AAX2 [#5989](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5989) | 真の空間プラケット数`P_H=L_H`、Haar共分散`C_H≤24L_H`、生一リンク応答`J_e≥ε⇒R≥ε/18`。 | 共通`ε>0`は未証明。 |
| AAY [#5990](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5990) | 原境界pair-Haar可測領域`E_H`上の`μ_H(E_H)≥ρ`、`|Δ|≥δ`、`0<Q≤q`から`J_e≥ρδ²/q`。 | 一様正値`ρ,δ`を持つ真正領域の存在。 |
| AAZ/AAZ2 [#5991](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5991) | 各固定`H,b>0`で`Δ`が**pair-Haar-a.e.ゼロではない**実リンクが存在。分母なし`G_e=∫Δ_e²dμ_H`を定義。真正FX分散`Q≤q`なら`G_e`は**自動可積分**、`G_e≤qJ_e`。共通`G_e≥m>0,q>0`なら条件付き`R≥m/(18q)>0`。 | `m`と対象`b(H)`での共通`q`の証明は残る。 |

`Q=∫_{SU(2)}(p_0-p_\pi)^2dν`は**真正posterior密度差のFX分散**、`Q_GI=Σ_pd_p²`は旧二文脈補償済みminorの**別量**。`J_e=∫Δ_e²/Q_e\,dμ_H`に使う`μ_H`は**元の外側境界pair-Haar**。`R`は**特定中心化Gauss-law物理源**のRayleigh値であって、全物理Hilbert源のcoercivityではない。

## 真の次段階：未解決ゲートの優先順位

### Gate A — 本物のGI二乗モーメントの絶対的下界【最優先】

\[
\boxed{\exists m>0,\quad\forall H,\quad\exists e_H\in\mathrm{Links}_H,\quad
 \int|\Delta_{H,b(H),e_H}(z;V_H)|^2\,d\mu_H(z)\ge m.}
\]

AAZの各有限`H`での非a.e.ゼロは**定性的**であり、正の`inf_H G_e`は従わない。**既に未知の`R`を前提にしない**真正局所応答から証明する。

実装候補は、元のWilsonリンクと境界に依存する有限局所円筒領域を**同じ外側pair-Haar**で構成し、真正GI期待値差`|Δ|≥δ>0`と領域確率`μ_H(E_H)≥ρ>0`をともに全`H`で証明すること。高次元積Haarで全リンクを制限すると領域測度が体積とともに減り得る。source/receiverの真正有限サポートと他のHaar変数の積分降下を証明し、**元の二つのinteracting posteriorを独立Haar posteriorへ置換しない**。密度差の非零性・符号変化だけではGI受信器の積分相殺を排除できない。

### Gate B — 実FX分散の共通上界と公理依存の境界

目標`∀H,z,\ Q_{H,b(H),e_H}(z)≤q`（`q>0`）。既存[JL #5658](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5658)は**固定`b`**について`Q≤(e^{16b}-e^{-16b})²`を真正posteriorから証明したが、その`#print axioms`には**歴史的finite-grid `native_decide` 5公理**が継承されている。標準公理のみのAAZ2へ無断に取り込まない。真正FK二側HarnackとSU(2) Haar積分から、固定mathlibに適合する独立証明が必要か検討する。任意の変動`b(H)`に`q`を勝手に仮定せず、`b(H)\to0`でのposteriorのHaar化も評価する。

**AAZ2でCLOSEDなのは`Q≤q⇒G_e`の自動可積分性であり、`q`の無条件存在ではない。**

### Gate C — AAZ2の条件付き含意を実在の`m,q`で閉じる

Gate A/Bの本物の独立証人が完成した場合にのみ、

\[
\boxed{0<m/(18q)\le R_{H,b(H)}\quad (\forall H)}
\]

が既存[AAZ2](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapAutomaticIntegrabilityV5_PZ37AAZ2.lean)から成立する。**この含意はすでにLean証明済み**であり、条件式だけを再証明せず、`m,q`のモデル内での構成へ進む。

### Gate D — 全物理源のcoercivity、positive-fineの共通区間、endpoint E/F

特定中心化源のfine-zeroの正値から、物理Gauss-law Hilbert全源の下界へは別のframe/source-synthesisが必要。AAE/AAHの正fine半径は**有限`H,b`ごと**で、全`H`・任意深さ共通ではない。`F_t=U-T_tU→0`やfine-zero係数Gram特異性からノルム正規化Rayleighのno-goを導かない。PZ37ZAで否定した二文脈`Q_GI/N_H`の一様正下界を復活させない。

### Gate E — H1–H4、連続体・4D Yang–Mills質量ギャップ

同一のendpoint、正のfine全深さ、source/measure compatibility、強極限Gauss-law Hilbert、物理Hamiltonian・正の非零スペクトル下界、OS/Wightman再構成と連続体4D質量ギャップは**OPEN**。条件付き有限体積Rayleigh判定をこれらの完了と同一視しない。

## 実装/CI受入れ条件

- 定理本文・imports・dependent signaturesを全部確認：[AAZ](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapMomentCriterionV5_PZ37AAZ.lean)、[AAZ2](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapAutomaticIntegrabilityV5_PZ37AAZ2.lean)、[AAY](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPosteriorPositiveEventCriterionV5_PZ37AAY.lean)、[AAX2](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPosteriorRawMassUniformV5_PZ37AAX2.lean)。
- GitHub MCPで正本fresh HEADを観測。Leanを変更したら**exact-source-head CI completed SUCCESS**、変更Lean warning/error`0/0`、公開`#print axioms`、`sorryAx`なし、独立completion receipt **SUCCESS**後のみsquash merge。queued/in_progressをauthorityにしない。
- **README/ROADMAPだけのdocs-only更新ではStrict Leanを回さない。** Markdown、両文書リンク、古いreceiptの履歴と最新SHA、`OPEN`と`CLOSED`を点検し、docsマージを新しい数学定理の証明とみなさない。
- 現状の数学・再現手順は[README.md](README.md)。最新theorem-bearing検証は[CI #40814241452](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40814241452)。

---

## 歴史的checkpoint archive（2026-10-27時点まで）

以下に残す「LATEST/CURRENT」「次はPZ37ZI／PA」は**その当時の検証履歴**であり、上の2026-10-29の最新正本・OPENゲートに優先しない。過去の形式化成果・no-go・独立completion receiptは削除しない。


**HISTORICAL VERIFIED PZ37ZI — 2026-10-27 JST · [PR #5947](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5947) MERGED**

- Sole theorem carrier: `formal/real-hilbert-uniform-coercive-strong-limit`; exact tested PZ37ZI source `f3a849f736334be71c6424f7ba6aa3a769249eda`; verified theorem-bearing squash [`87f187014c78222fd84e275a8d3b8bc19e6d6a36`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/87f187014c78222fd84e275a8d3b8bc19e6d6a36). Default `main` is not authority.
- Exact source-head [CI #40491398111](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40491398111): **11,107/11,107 SUCCESS**, changed Lean warning/error **0/0**, four new public `#print axioms` all limited to `propext`/`Classical.choice`/`Quot.sound`, independent MCP completion receipt SUCCESS; no new axiom, sorry, admit or native_decide.
- **CLOSED:** PZ37ZI combines genuine AQ global raw/normalized original Wilson physical transfer estimate with PZ37ZE/ZC and PZ37ZH. For any finite H, frozen b>0 and fine t≥0, with `B_H` the original plaquette/temporal crossing action budget and `L_H` original spatial-link count: `‖T_t-T_0‖≤2B_Ht`, `‖U-T_tU‖≤2B_Ht`, `0≤M_GL(H,b;U-T_tU)≤2L_He^(16b)(2B_Ht)²`. For sufficiently small **positive** fine, PZ37ZH makes that same true all-link two-posterior GL numerator strictly positive. This is fixed-volume `O(t²)`, not normalized-Rayleigh asymptotics or H-uniform lower coercivity.
- **OPEN / next PZ37ZJ:** actual JG strong original raw one-slab Haar-`L²` first variation `R_t U=U+tD_H+o(t)`; its nonconstant genuine spatial Wilson tangent has `P_(U⊥)D_H ≠0`. Combine `‖R_t‖→1` with the projected cancellation `P_(U⊥)(U-T_tU)` to prove rigorously in Lean the **normalization-insensitive** slope `P_(U⊥)F_t/t→-P_(U⊥)D_H` for positive fine, *without* assuming differentiability of operator norm normalization. Transfer this to a genuine fixed-H linear lower bound on `‖F_t‖` if justified. Full `F_t/t` direction requires normalizer derivative or independent control; genuine GL normalized ratio/covariance needs further work.
- **STILL OPEN:** source-norm fine-/volume-uniform GL coercivity, limit of `M_GL(F_t)/‖F_t‖²`, endpoint E, arbitrary-depth common fine F, H1–H4 and continuum mass gap. Do not revive PZ37ZA's disproved bounded two-context compensated `Q_GI/N_H` lower floor. Historical PZ37ZH and prior snapshots below remain dated, not latest theorem status.
- Docs only: do not trigger unnecessary Strict Lean.

---

**HISTORICAL VERIFIED THEOREM / NEXT GATE — 2026-10-27 JST · PZ37ZH #5945 MERGED**

- Sole theorem carrier: `formal/real-hilbert-uniform-coercive-strong-limit`, tested PZ37ZH source SHA `8c258a37a04187cc6c708eef354e88682d7a7f5e`, verified squash theorem [`c2101b5596689ed6dd0939aad60b8c2884f6e3ee`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/c2101b5596689ed6dd0939aad60b8c2884f6e3ee) ([PR #5945](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5945)). Default `main` is not authority.
- Exact-head [CI #40489013358](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40489013358): **11,093/11,093 SUCCESS**, changed file warning/error **0/0**, all seven new `#print axioms` reports exclusively standard `propext`, `Classical.choice`, `Quot.sound`, independent MCP CI completion receipt SUCCESS. No new axiom, sorry, admit or native_decide.
- **CLOSED:** explicit adjacent frozen/fine `beta(0)=b>0`, `beta(k>0)=t≥0`, true HJ depth-one signed physical coefficients `(1,-1)`, exact same-Gauss-law-Hilbert equality `S_1(1,-1)=F_t=U-T_tU`. Apply the original OX all-fine/all-depth two-interacting-Wilson-posterior full-link GL kernel theorem: `M_GL(F_t)=0 iff F_t=0` for every nonnegative fine `t`. For any genuinely nonzero `F_t`, `0<M_GL(F_t)/‖F_t‖²≤2|Links(H)|e^(16b)`. PZ37ZF supplies nonzero physical `F_t` throughout one sufficiently small **positive** fine interval, without any assumed rank/separation axiom.
- **OPEN / next PZ37ZI (tentative):** use verified genuine JG strong Haar-`L²` one-slab Wilson raw-row first variation with its nonconstant spatial-action tangent, together with original normalized transfer/operator-norm continuity. Analyze `F_t/t`, perpendicular spatial-action component, true full-link GL continuity/covariance, and whether a positive lower bound for `R(F_t)` uniform over `t∈(0,δ_H)` can be **proved** at each fixed finite `H,b` without assuming a transfer-norm derivative. Distinguish any fixed-model result from a volume-/scale-uniform physical source floor.
- **Never infer:** `M_GL(F_t)→0` ⇒ normalized ratio tends to zero, or two-mode coefficient-ℓ² no-go ⇒ source-norm coercivity no-go. The separately disproved PZ37ZA bounded two-context `Q_GI/N_H` sufficient density remains closed. Endpoint E, arbitrary-depth common fine F, H1–H4 and continuum Yang–Mills mass gap are **OPEN**. Historical PZ37ZG/ZF/ZA checkpoints below are dated receipts, not latest authority.
- Documentation-only append-only update: **do not run Strict Lean**.

---

**HISTORICAL VERIFIED THEOREM AUTHORITY / NEXT GATE — 2026-10-27 JST, PZ37ZG #5943 MERGED**

- Sole theorem carrier: `formal/real-hilbert-uniform-coercive-strong-limit`; verified theorem-bearing squash [`49467c2542e4a4b565ec480f04884f9c97c57abe`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/49467c2542e4a4b565ec480f04884f9c97c57abe), distinct from tested source `77d50b0c0d6bc90aa3b8a243bdf3ae50aeef37e8` ([PR #5943](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5943)).
- Exact source-head [CI #40483971949](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40483971949): **11,092/11,092 SUCCESS**, changed Lean warning/error **0/0**, four new public axiom audits only `propext`, `Classical.choice`, `Quot.sound`; independent MCP completion receipt SUCCESS.
- **CLOSED (PZ37ZG):** for every nonzero genuine Gauss-law physical `f`, the full-link true interacting Wilson-posterior GL Rayleigh `R=M_GL(f)/‖f‖²` satisfies `0≤R≤2|Links(H)|e^(16b)`. On each finite original right-Krylov physical source subspace a strictly positive model-dependent lower `c(H,b,t,r)` exists for nonzero sources, using previously proved PZ37U; no new coercivity assumption. For the true `F_t=U-T_tU≠0` at sufficiently small positive fine, the same explicit upper Rayleigh cap holds.
- **OPEN (next PZ37ZH tentative):** a named *literal* Lean equality `F_t=S_1(1,-1)` and direct strict `R(F_t)>0` via existing OX/U; the small-fine normalized-source direction and leading original Wilson analytic jet; existence/positivity of a ratio limit; fine-, volume- and scale-uniform physical norm lower bounds; endpoint E, arbitrary-depth common window F, H1–H4, continuum gap.
- **Logical separation:** `M_GL(F_t)→0` does not determine `M_GL(F_t)/‖F_t‖²`. The PZ37ZF coefficient frame no-go **is not** a physical-source Hilbert coercivity no-go; PZ37ZA already disproved the separate bounded compensated two-context `Q_GI/N_H` uniform-density sufficient condition.
- **Historical documents:** the PZ37ZF and PZ37ZA "CURRENT/LATEST" checkpoint text below is retained as dated history, not current authority. This is a docs-only appended checkpoint: do not run Strict Lean for this change.

---

**HISTORICAL THEOREM AUTHORITY / PROOF GATES (2026-10-27 JST, PZ37ZF #5941 MERGED)**

- Sole theorem branch: `formal/real-hilbert-uniform-coercive-strong-limit`; exact verified HEAD = PZ37ZF squash `2d59cfc970cd358e29263577e2f8c76c688e35f9` ([PR #5941](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5941)). Source-HEAD [CI #40479003824](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40479003824) **11,091/11,091 SUCCESS**, changed Lean warnings/errors **0/0**, four public `#print axioms` only `propext`/`Classical.choice`/`Quot.sound`. The #5935/PZ37ZA “latest” entries farther below are historical checkpoint receipts, not the current HEAD.
- **#5937 PZ37ZB — CLOSED:** genuine all-link/all-context three-mode GL Gram singular at fine zero; no positive coefficient-ℓ² frame *including* zero.
- **#5938 PZ37ZC — CLOSED:** arbitrary original Gauss-law physical `f` and genuine spatial patch `S`: `M_GL(f,S) ≤ 2 e^(16b) |S| ‖f‖²` at frozen `b>0` (upper only; no surrogate, no finite-mode assumption).
- **#5939 PZ37ZD — CLOSED:** at every finite depth/fine, true GL Gram upper quadratic comparison `B_GL ⪯ (1+2|Links(H)|e^(16b)) P_phys` and explicit 3-mode trace upper; a lower comparison constant exists *per finite model*, with no uniform `c_H` asserted.
- **#5940 PZ37ZE — CLOSED:** exact true physical cancellation source `F_t=U-T_tU` obeys `M_GL(F_t) ≤ 2|Links(H)|e^(16b) ‖T_t-T_0‖² →0` as fine `t↓0` at fixed `H,b`.
- **#5941 PZ37ZF — CLOSED:** for every positive `δ,ε`, some **strictly positive** `t<δ` has `F_t≠0` and `M_GL(F_t)<ε`; the fixed coefficient `(1,-1)` cannot have a uniformly positive coefficient-ℓ² GL floor over a punctured fine window.
- **OPEN / do not confuse:** `M_GL(F_t)/‖F_t‖²` for the **nonzero, physically normalized** source; genuine full-link posterior covariance and volume/spacing-uniform lower bounds; same-endpoint source E; positive fine at all depths F; strong-limit H1–H4; continuum mass gap. The two-context `Q_GI/N_H` floor was *disproved* by PZ37ZA, not reopened by ZB–ZF. Positive-fine 3-mode Gram definiteness proved earlier remains true at each sufficiently small positive fine; a shared coefficient lower across `t↓0` is a different quantification.
- **Next PZ37ZG (tentative):** inspect actual Wilson first-order physical cancellation source and normalized posterior GL mass ratio. Keep Gauss-law physical Hilbert and unchanged interacting SU(2) Wilson posterior integrals; investigate true covariance/compactness obstructions only once their hypotheses are proved. Docs-only updates must not trigger unnecessary Strict Lean.

---


**2026-10-27 JST · 唯一のLean定理正本：`formal/real-hilbert-uniform-coercive-strong-limit` · 最新検証済みtheorem-bearing squash HEAD：[`56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300)（[#5935 PZ37ZA](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5935)）。default `main`は定理正本ではない。**

**最新到達（PZ37ZA）：** 元の真正SU(2) Wilson・二相互作用posterior・Gauss-law物理Hilbert・参照積Haar・frozen/fine結合を保持。PZ37Q–Yで全有限Hの小正fine三モード物理rank3・元の3モードGL積分Gram coercivityと `det G_H^GL≥c_H³D3(H,t)>0` を証明済み。PZ37Z #5933は異なる量 `Q_{H,b}(e,e',z,z')=Σ_{p∈P_H}d_{H,b,p}²` の `Q_H/N_H` に関し、文脈選択型の一様正下界と固定絶対閾値・正のGI活動割合の同値を証明した。しかし**PZ37ZA #5935でこの二文脈補償済みGI densityの実在側を否定した**。元の四リンク支持と有限重なり（24）、中心化Wilsonプラケットの積Haar独立性、補償済みGI二文脈汎関数ノルム `≤2E_b²` から、**全H・全リンク・全境界文脈で `Q_H≤96E_b⁴`**。実際のプラケット数 `N_H≥2(H+1)` により**固定 `b≥0` の `Q_H/N_H` はどのH依存文脈を選んでも一様正下界を持てない**。変動 `b_H` で元のHarnack共通上界 `(4E_{b_H}²)²≤K` を置けば `Q_H≤6K` で同じ結論。PZ37Zの同値は論理的に正しく、双方が偽となる。**限定：** 二文脈補償済み密度のno-goであり、元の全リンク・全文脈GL積分質量の一様coercivity、元の3モードの有限H正値性、endpoint E、任意深さF、強極限H1–H4・4D Yang–Mills質量ギャップの否定ではない。次に必要なのは十分条件の言い換えでなく、同一source/endpointに沿う真正full-link GL積分・相関の解析的一様評価。

**[プロジェクトの数学的定義・数式・再現手順 → README.md](README.md)**

## 0. Historical 2026-10-27 authority / CI receipt

| 項目 | 正確な検証結果 |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| 定理の唯一正本 | `formal/real-hilbert-uniform-coercive-strong-limit`（default `main`ではない） |
| 最終検証済み**定理-bearing**マージ点 | `56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300` — PZ37ZA #5935。後段の歴史的表はそれぞれの証明時点に限定。 |
| 検証**source HEAD**（squashと区別） | PZ37ZA `780ad873a0e678b5a70cd5d8235682436ea28b7c`、squash `56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300`。 |
| [PZ37ZA exact-head #40455326601](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40455326601) | **SUCCESS・11092/11092**、変更Lean5ファイルwarning/error **0/0**、新規公理監査13/13標準3公理のみ、MCP completion receipt SUCCESS、squash SHAと正本HEAD一致。 |
| 公開`#print axioms` | PZ37ZA新規13/13：`propext`、`Classical.choice`、`Quot.sound`のみ、`sorryAx`なし。既存の別系統finite-latticeの`native_decide`依存と混同しない。 |
| Lean / mathlib pin | `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| 現在のbranch HEAD | [毎回GitHubで再観測](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) |

固定SHAは**2026-10-27 PZ37ZAまでの定理統合点**であり、後続docs-onlyマージは新規Lean証明を意味しない。PZ37Zの二文脈補償済み `Q_H/N_H` の一様性はもはや単なる未証明ではなく、**PZ37ZAで条件成立の不可能性がLean証明済み**。PZ37Zの同値定理自体は保持し、旧記述は証明時点の履歴に限定する。fresh HEAD→定理全体とimports→exact-head CI・公理監査→docs→履歴の順で判定する。

### 重要な区別

- `Q_post = ∫(p_{0,b}-p_{π,b})²dν`：過去のGI/source比較に現れる真正posterior**密度差**。
- `Q_GI = Σ_{p∈P_H}d_p²`：LY以降の真正Wilson**局所GI minor二乗エネルギー**。`d_p=||T_{H,b}||²Δ_p`、`N_H=|P_H|`。
- `E_b=e^{8b}(e^{16b}-e^{-16b})`：元のone-link joint-density Harnack等からLWで得る正のコントラスト尺度（`b>0`）。
- `k_{H,b,e,e',z,z'}=(Q_GI/N_H)/(10E_b²)`。**`Q_GI>0`が体積ごとに成立しても`inf_H k_H>0`は従わない。**

`A_W`（非正規化の原Wilson Haar-reference）、`D₁₂`（正規化物理条件射影のDirichlet）、元のGI検出器、`p`ごとに変わる物理源のGram、fine-evolution/endpoint、連続体Hamiltonianは**異なる作用素・検証対象**。

### P4-Q2-PD–PN：真正第三モードの新しい証明段階

| 範囲 | CLOSED（Lean4で証明したこと） | OPEN（証明していないこと） |
| --- | --- | --- |
| PD–PE | `R₂ ⟂ U,TU`、`‖R₂‖²=Δ₂D₃`、真正GI/GL条件付き移送 | `R₂≠0` 無条件証明 |
| PF–PH | 真正連続空間代表、`Δ₂>0` で `D₃>0 ↔ ∃A,B,C, minor≠0` | 具体的非零3配置 |
| PI–PJ | 元の一段Haar核・二段完全Wilson二重Haar核と真正非正規化物理転送のpointwise一致、minorの正規化尺度 | 非零literal minor |
| PK–PM | 原Wilson二段全空間作用の厳密分解、空間Wilson作用重み付きHaarゲージWard恒等式、混合モーメントのアフィン関係、**二次までの形式的jetの三次minor係数は恒等的に0** | 形式的jetを積分済み真のTaylor jetに同定すること |
| PN #5839 | 固定mathlibの指数関数3次余剰、真正一・二段元Wilson核および二重Haar余剰の有限体積一様上界、10901/10901 GREEN | 真のminor `O(t⁴)`、四次以上の非零係数、rank3 |

数学的な核は（ここで `M_H` は本来の一スラブWilson作用予算）：

```text
Q(X,A,B) = S(X,A) + S(A,B)
         = W(X)/2 + W(A) + W(B)/2 + C(X,A) + C(A,B)
0 ≤ Q ≤ 2 M_H

|∫dμ_H(A)∫dμ_H(X) [exp(-tQ) - (1 - tQ + t²Q²/2)]|
    ≤ ‖2tM_H‖³              (‖2tM_H‖≤1).
```

この境界は真の空間Haarを使う**有限体積での余剰制御**であり、真正二posteriorの独立性や体積一様性を主張しない。次のPOで一段・二段の積分済Taylor係数とPKの `a,b,d` をFubini/Bochnerで同定し、PMのWard退化と合わせて実際のliteral minor `O(t⁴)` を閉じる。その先は元のSU(2) Wilson模型の四次以上の具体的非零3配置witnessが必要で、これを仮定へ置き換えてはならない。

## 1. 証明ゲート一覧：CLOSEDの量化範囲を明示

| Gate | 正本Leanで証明された範囲 | 未解決の部分 |
| --- | --- | --- |
| **P：真正Wilson模型** | 元のSU(2) Wilson相互作用kernel/Perron/ground-state posterior、Gauss-law物理Hilbertと物理receiver、original GI signed response | これらを独立Haar conditionalや架空のrank/sourceへ置換しない |
| **S：真正空間GI非零性 — CLOSED（有限H）** | **LM**：任意の有限H、`b>0`、実際のリンク対に対して、`Δ_W(z,z')≠0`となる**真正二文脈**の存在 | 選択文脈のH依存、fine全深さ、体積一様性は別 |
| **L：局所真の物理源強制性 — CLOSED（有限H）** | LN/LO/LP/LQ、LS–LX、LY：原Wilson物理源`xU+yW_{H,p}U`とGI minorから`κ_p>0`、補償尺度・Harnack/Frobeniusの明示評価 | 全てのpの一様下界ではない。固定pの全スケール互換も未証明 |
| **V：局所GIエネルギー／変動 — CLOSED（有限H）** | LY/LZ/MA/MB/MC：`Q_GI`の正の文脈、平均・分散・上界、真正活性集合と有限密度評価 | `Q_GI/N_H`の正のH一様下界なし |
| **G：空間平均物理応答Gram — CLOSED（有限H）** | MD–MJ：真の`R_p`の空間和、MFの`Q_GI/N_H`**一次**強制性、MG/MHのGram・det、MI/MJの逆写像・データ差Lipschitz | `p`依存sourceの空間frameは**単一endpoint源**や全Krylov source spanではない |
| **K：単一真正plaquetteの平均達成 — CLOSED（有限H）** | LYの既存max witnessをMKで再利用可能な4公開定理へ展開：`d_p²≥Q_GI/N_H`、`κ_p≥k`、全`x,y`で物理`R_p≥k(x²+y²)` | `p=p(H,z,z')`の選択は一般にスケール間で固定・互換とは限らない |
| **G：真の時間Wilson Gaussian解析 — CLOSED（有限点・固定b）** | NY: 非零signed functionalの完全Gaussianエネルギー正値、NZ: section実線形包稠密、OA: 全有限Gram厳密正定値、OB: Matrix.PosDef/逆、OC: 真正section有限補間 | kernel Gramは真正物理GI covarianceの非零性・下界そのものではない |
| **D：真の二posterior→Gauss-law GIのone-link表現 — CLOSED（OD・有限H）** | OD: 真の `D=p₀-pπ` が非零 `L_D` を定め、NYでkernel sectionが `L_D` に検出される。元のGI gap `Δ_GI(f)=L_D(R_f)` を本来のFF物理receiver fiberについて厳密証明 | **OPEN:** 物理受信器像 `range(f↦R_f)` が `ker L_D` に入らないこと、要求される源familyとendpointへの輸送、positive fineと全深さ |
| **Z0：同一スケール真正零次Krylov源の文脈・深さ互換 — CLOSED（OG）** | OF/GXの真正零次源U、ODのsigned作用一致、OGの真のHF modal等式と `∃(z,z')∀r` 同一下界 | **零次selectorだけ**。任意係数・スケール間endpoint・U0はOPEN |
| **R1：固定スケール単一真正GI受信器の全深さ・係数核rank — CLOSED（OH）** | OGの同一二文脈から元の1行を固定選択し、全rの正準零次源の二乗応答が真の `Q_GI/N_H` 下界の半分以上。HFの係数kernel `finrank=r`、各深さに同じ文脈で検出される開球 | 一行のkernel係数は非零物理源と同一視できず、全文脈・全係数源の可視性はOPEN |
| **R2：本当のKrylov係数・物理源の一行kernel分解 — CLOSED（OI）** | 元のHF一行受信器で `a=k_r+t_r a0`、`Φ_r(k_r)=0` と分解し、HJ真正物理源で `S(a)=S(k_r)+t_r U`、OD signed元受信器でも選択一文脈で `S(k_r)`の応答0を厳密証明 | 一文脈のkernelを全文脈の物理不可視源と同一視しない。非零性・全係数源分離・U0はOPEN |
| **R3：別の真正Wilson文脈の交差minor・全文脈kernel比較 — 条件式OJ／小正fine深さ1実在OMでCLOSED** | OJ：真正HF minor＝元の残差の別文脈GI応答。**OM：LM・JIを接続し真正 `(U,T_tU)` の非零二文脈minor実在をLean証明** | **深さ2以上／正fine全域／H一様下界は未証明**。OI/OJ時点の未解決はOMで範囲限定して解決 |
| **R4：真正fine Wilsonの固有直線による全深さGI・物理源障害 — CLOSED（OKの条件付き分枝）** | 実際の normalized fine Wilson transfer が `T_fine U=cU` なら **全** right-Krylov物理源は `c^jU`、全真正cross-context minorゼロ、OHで非零anchorがある固定scale全有限rに対して `ker S_r=ker Φ_all,r`。fine=0なら任意r、r=0なら任意fineでminorゼロ。minor非零には `r>0`・正fine・非固有直線が必要 | **OLにより十分小さい正fineでのU非固有性は証明済み**。非固有直線分枝での真正GI受信器の高次検出とsource分離はOPEN。U0/endpointもOPEN |
| **R5：真正small-positive fine物理非固有直線・一行kernel内の非零物理源 — CLOSED（OL）** | IY・IX・IVから有限H小正fineで `T_t U∉ℝU` と、HY/IS/IU選択一行GIで零の非零物理pivot | **OMで同じpivotの第二文脈による検出が後にCLOSED**。δ_HはH依存、任意正fine・一様性・endpointはOPEN |
| **R6：真正small-positive-fine GI二文脈minor — CLOSED（OM）** | LMの元空間minorとJIの実fine微分によって `(U,T_tU)` の真正二文脈minorが有限H小正fineで非零。OJの実HF modal minorとの同一性・選択第一文脈で消えるpivotの第二文脈検出までLeanで証明 | 深さ2の第三minor、任意正fine、H一様下界はOPEN |
| **R7：深さ1の全係数全文脈GI・物理源単射 — CLOSED（ON）** | OMの非零2×2行列式によって、全実係数 `(a₀,a₁)` で `Φ_all,1(a)=0 ⇔ a=0` かつ `S₁(a)=0 ⇔ a=0` | `r≥2`では、第三モード `T_t²U` と真正第三GI受信器の非退化性が別途必要 |
| **R8：真正深さ2Schur残差の構成・第一二行GI消去 — CLOSED（OO）** | 深さ2の実物理源 `(U,T_tU,T_t²U)` と真正signed HF応答を同定。OMの先頭minorを実深さ2へ輸送し、選択二行GIで同時に消える非零**係数**残差R₂を構成。元のHilbert像と第三文脈でのsigned応答を正確に計算 | **残差の物理像または第三GI応答が非零とは未証明**。係数非零と源非零を混同しない |
| **R9：深さ2の真正GI／物理源核の一次元還元 — CLOSED（OP）** | 真正二行GI共通係数核=`ℝR₂`、`ker S₂ ⊆ ker Φ_all,2 ⊆ ℝR₂`。`S₂`単射⇔`S₂(R₂)≠0`、`Φ_all,2`単射⇔ある実Wilson第三文脈で `Φ(R₂)≠0` | **必要十分条件の右辺はOPEN**。二つの非零性を架空のrankやreceiver-span仮定から導出しない |
| **R10：真正fine二次元閉包の全深さGI/source核一致 — CLOSED（OQの条件分枝）** | 元の `S₂(R₂)=0` から、元の正規化Wilson転送の `T_t²U=αU+γT_tU`、任意jの物理二次元軌道・任意rの源合成と `ker S_r=ker Φ_all,r` をLean証明。有限H小正fineではこの全深さ核一致と**実Schur物理像非零**の二分が無条件成立 | **実Schur物理像の零／非零を決定したのではない**。第三GI文脈による非零検出・全正fine・体積一様性はOPEN |
| **R11：真正二posterior GL質量正値性 — CLOSED（ORの条件分枝）** | FX・GL真正二乗積分の非負性とHJ・OQの全深さkernel一致を接続。実Schur物理源ゼロ分枝の全有限rで `M_GL(S_r a)=0⇔S_r a=0` および `S_r a≠0⇒M_GL(S_r a)>0`。有限H小正fineでこの全深さ定性正値性と実Schur物理源非零の二分を証明 | 全正fine・体積／深さ／spacingに一様な**定量的**GL下界はOPEN。非零第三GI受信器も未証明 |
| **R12：真正有限H小正fine物理ノルム係数制御 — CLOSED（OS、条件分枝を区別）** | mathlib有限次元逆Lipschitz＋ONから、実深さ1の元Wilson物理Hilbert源合成・全文脈GI検出器に、各固定H・fine/frozen結合に依存する正の係数ノルム制御定数が存在。**もし**実Schur物理源非零ならOPにより実深さ2の同様の係数ノルム制御も成立。ORと接続し、全深さ非零源の定性的GL質量正値性、または実深さ2の正ノルム係数制御の無条件二分 | 深さ2実Schur源の非零はOPEN。係数ノルム制御は真正GL質量の一様下界ではなく、H・coupling一様U0もOPEN |
| **R13：真正元Wilsonの連続物理源検出・全有限深さ核一致 — CLOSED（OT–OW）** | OT：完全Wilson核正値性→ゲージ正規化→元の二posterior signed GI検出、OU：任意Gauss-law入力の正規化Wilson出力に真正連続Haar-L²代表、OV：Gauss-law a.e.不変性を積Haar全supportで点ごとへ昇格、OW：真Krylov全有限rの連続ゲージ不変代表と **`ker S_r=ker Φ_all,r`**（固定H・凍結正・fine非負）。実Schur源非零なら第三実GI文脈が存在 | 物理Schur源の非零、第三物理モードrank3、格子／深さ一様定数、endpointはOPEN。核一致から `S_r` 単射は導かない |
| **R14：元の二posterior真正GL質量の全fine・全深さ定性正値性 — CLOSED（OX）** | OWの無条件真正核一致とORの元のposterior GL二乗／正分散積分を接続：有限H、凍結 `b>0`、fine `t≥0`、任意有限r、実係数aで `M_GL(S_r a)=0 ⇔ S_r a=0` および `S_r a≠0 ⇒ M_GL(S_r a)>0` をLean4証明。小正fine・Schur閉包仮定を除去 | `inf_H Q_GI/N_H>0` を含む一様下界、全物理空間への拡張、任意深さの`S_r`単射、4D連続体gapはOPEN |
| **R15：元のWilson正fine物理エネルギー・一段Krylovシフト核保存 — CLOSED（OY）** | 完全元Wilson one-slabのLJ厳密正Haar二次形式を、真正物理転送の積Haar inner raw integralとa.e. transportで一致させる。全有限H、fine `t>0`、任意有限r、実非零物理源 `f=S_r a` で `⟨T_raw(t)f,f⟩>0`、従って `T_t f≠0`。全係数の1段shiftで `Σa_jT_t^(j+1)U=0 ⇔ Σa_jT_t^jU=0` をLean証明 | `U,TU,T²U`のrank3未証明。finiteH fine t>0のみ、fine=0は除く。U0・endpoint・連続体はOPEN |
| **R16：元Wilson正fine反復Krylov源の非消滅 — CLOSED（OZ）** | 実normalized Wilson出力OU/OVは連続・真ゲージ不変代表を持つため、OYの元の完全Wilson核の厳密正二次形式を反復使用できる。全有限H・fine `t>0`・任意有限r・任意kで、真物理源 `S_r a≠0 ⇒ T_t^k(S_r a)≠0`。ONで証明済みの実深さ1単射性と接続し、小正fineで全kのshifted隣接二モードの非退化性 | 三モード `U,T_tU,T_t²U` の独立性・実Schur非零、H/k/tに一様な定量下界、U0・endpoint・連続体はOPEN |
| **R17：真正物理全シフト二モードGram — CLOSED（PA #5823）** | OZ・ONから小正fineの一つの区間で全kにわたる真正二モードsource単射、`T_t^kU,T_t^(k+1)U` のGauss-law物理Gram PosDef、det>0、k依存の正の逆Lipschitzノルム定数をLean証明 | 三モードrank3、k/Hに一様な下界、U0はOPEN |
| **R18：真正Wilson Hankelモーメント — CLOSED（PB #5824）** | self-adjoint真Wilson物理転送から全i,jで `⟪T^iU,T^jU⟫=m_(i+j)`。すべての有限Krylov物理Gram＝真のHankelモーメント行列、PSD、偶数モーメントは正確なノルム二乗 | 3×3 det>0、真Schur物理源非零を含まない |
| **R19：真正Wilson全シフトHankel厳密二次minor — CLOSED（PC #5825）** | ONの同一小正fine区間で全kの2×2実Hankel PosDef・det>0、`m_(2k)m_(2k+2)-m_(2k+1)^2>0`。Lean 10889/10889、公開公理3/3、2定理に既存native_decide依存継承 | **元の物理3×3 Hankel det>0は未証明**。二点スペクトル反例に留意 |
| **F：positive fine / arbitrary r** | OM/ONは小正fineの深さ1 `S₁` 単射。OWは全非負fine・全有限rで **`ker S_r = ker Φ_all,r`**、OXはそれらの真の物理源が非零なら元のGL質量厳密正（全非負fine・全有限r）。OQ/ORの旧条件分枝はより広いOW/OXによりその範囲で強化。 | 全rのsource係数単射、Schur物理像非零、真正第三物理モードrank3、U0・endpointはOPEN |
| **U：真の一様解析** | 固定bで元のreceiverコントラスト`E_b`の体積一様な**上界**など | GIエネルギー/分離の下界、signed spatial covariance・tailsの可和性、深さとスケールの制御は OPEN |
| **C/H：連続体** | 一部の有限格子・限定されたsource subspaceの証明 | H1-C1/C2/C3、物理時間、OS/Wightman、非自明な4D連続体質量ギャップは OPEN |

**SはLMによって既にCLOSED。** 2026-10-18版で記した「第二の空間Wilson物理文脈の非零GI応答がOPEN」という記述を、ここで修正した。JP–JRの時間posterior共分散ルートやJSのreceiver-span条件は別の有意義な補助定理だが、Sを証明するために今からreceiver-span membershipを仮定する必要はない。

## 2. このスレッドの検証済み数学的推移（空間物理GI：LM → MK）

### 2.1 真正空間Wilson static minor非零：LM、LN、LO–LP

- **LM** `p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts`：literal original Wilson空間作用と単位物理源の**真の2×2 GI行列式非零**。証明は原Wilson転送核、full Haar正値性、gauge-normalized centered transfer、LCの厳密検出へ依存。
- **LN**：global original source plane `xU+yW_HU`に有限体積の実際の2行GI応答強制性。**LO/LP**：真の各局所plaquette `W_{H,p}U`を表現・局所 minorへ分解し、少なくとも1つの真正局所nonzero witnessを選択。
- **LQ–LX**：original physical source denominatorと補償されたGI表現。LV/LWでfull original Wilson transfer、joint半密度と`E_b`の明示的上界を用い、`d_p=||T||²Δ_p`などを証明。これはoriginal physical Hilbertを変えないスカラー再表示。

### 2.2 消去されない局所GI二乗エネルギー：LY–MC

$$
Q_{\rm GI}(H,b,e,e',z,z')=\sum_{p\in\mathcal P_H}\bar\Delta_p^2.
$$

- **LY** `p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor`：LM/LPの実文脈で`Q_GI>0`、真のmax-plaquette `d_p²≥Q_GI/N_H`、真の未補償Gauss-law源で`κ_p≥Q_GI/(10N_HE_b²)`。この**最大選択はLYで既に証明**されている。
- **LZ**：局所GI square energyの厳密なmean/variance恒等式。
- **MA**：全ての実plaquetteで`d_p²≤(4E_b²)²=16E_b^4`という、体積を含まない局所上界（**下界ではない**）。
- **MB #5729、MC #5731**：`d_p²≥Q_GI/(2N_H)`という真の活性集合`A`の有限Hでの割合、および各活性pでの元の物理源強制性。[#5730](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5730)は同一source SHAのCI回復のための重複マージ、[#5732](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5732)は未マージでクローズした検証専用PRであり、数学的マイルストーンに重複計上しない。

### 2.3 空間frame・逆写像：MD–MJ

真の2つのoriginal signed Wilson事後物理応答`G_{e,z},G_{e',z'}`について

$$
R_p(x,y)=G_{e,z}(xU+yW_{H,p}U)^2+
 G_{e',z'}(xU+yW_{H,p}U)^2,\quad
k=\frac{Q_{\rm GI}/N_H}{10E_b^2}.
$$

- **MD #5733 / ME #5734**：活性集合から全真正plaquetteへの有限和の比較。MEの`(Q_GI/N_H)^2`依存は、次のMFによって改善。
- **MF #5735**：活性集合作成を経由しない各original pの物理強制性から
  $$
  k(x^2+y^2)\le\frac1{N_H}\sum_{p\in\mathcal P_H}R_p(x,y)
  $$
  を正確に証明（`Q_GI/N_H`へ**一次**依存）。
- **MG #5736**：同じ真正応答の偏極で`G_{\rm spatial}=\begin{pmatrix}A&B\\B&C\end{pmatrix}`を定義し、`G_{\rm spatial}\succeq kI`、`AC-B²>0`を証明。
- **MH #5737**：`A,C≥k`、`AC-B²≥kA≥k²>0`という具体的な**有限H行列式下界**。
- **MI #5738**：`G_{\rm spatial}^{-1}`の明示的adjugate式、係数一意性、`k²\|G^{-1}v\|_2²≤\|v\|_2²`。
- **MJ #5739**：同じ逆写像の加法性、実数倍、差分と任意2観測`v,w`のLipschitz安定性
  $$
  k^2\|G^{-1}v-G^{-1}w\|_2^2\le\|v-w\|_2^2.
  $$
  これらは有限Hの**局所源familyの空間平均Gram**であり、独立Haar検出器でも単一endpoint transfer作用素でもない。

### 2.4 一枚の実プラケット：MK #5740

`p4Q2MK_originalGI_exists_meanEnergyPlaquette`、`...exists_meanCoercivePlaquette`、`...exists_singlePlaquetteLinearFloor`、`...exists_authenticMeanPlaquette`の4定理によって、元のfinite `Finset.univ`のmaxから

$$
\exists p\in\mathcal P_H,\quad d_p^2\ge Q_{\rm GI}/N_H,\qquad
\forall x,y\in\mathbb R:\ R_p(x,y)\ge k(x^2+y^2)
$$

を真のoriginal interacting-Wilson文脈で扱いやすい形に整理した。`p`の存在は真正Wilson物理源に基づくが、**p選択のH/scale連続性やendpoint source同一性はまだ証明されない**。

### 2.5 真正時間Wilson Gaussian・物理GI receiver：NT–OD（#5776–#5787）

この経路は空間GI源のMF–MKと **混同してはいけない別の正本定理群**。同じ元のSU(2) Wilson時間核であり、Wilson相互作用posteriorやPerron半密度の置換ではない。

- **NT–NX**：真正signed座標モーメント、任意Taylor次数のGram展開、signed double energy、Banach収束。
- **NY [#5781](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5781)**：任意非零 `L : C(SU(2),ℝ) →L[ℝ] ℝ` と `b>0` について、完全Wilson核 `K_b(x,g)=exp(bχ(x⁻¹g))` の二重signedエネルギー `T_L(K_b)>0`。元のWilson–Perron signed receiverについて局所Haar分散の正値性を証明。ただし物理GI共分散の一般下界ではない。
- **NZ [#5782](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5782)**：Hahn–Banachを用いて固定 `b>0` の本当の時間kernel section実線形包が `C(SU(2),ℝ)` に稠密。
- **OA [#5783](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5783)**：任意有限の相異なる元のSU(2)点の `Σᵢⱼ aᵢaⱼK_b(xᵢ,xⱼ)>0` を非零係数列について証明。
- **OB [#5784](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5784)**：元の核の有限行列についてmathlib `Matrix.PosDef`、`IsUnit`、`det ≠ 0`、逆行列PosDef。
- **OC [#5785](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5785)**：相異なる有限点において真正kernel sectionのみで任意実数目標値を厳密補間する係数 `v ᵥ* M⁻¹` と、section線形独立性。


- **OD [#5787](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5787)**：真正な相互作用Wilson二posteriorの密度差 `D=p₀-pπ` と `L_D(v)=∫v(g)D(g)dμ_Haar` を連続signed汎関数として構築。`L_D(D)=Q_post` およびGAの `Q_post≥exp(-32b)b² V_SU2>0` による非零性を証明し、NY完全Gaussian double energyとWilson kernel section分離に接続。**同じ `L_D` を実際のFF物理受信器fiberに作用させた値が元のGauss-law物理GI gapと厳密に一致**することもGIの元の積分恒等式から証明。exact-head CI #39716611363 SUCCESS、Lean 10865/10865、新公開8件、sorryAxなし、変更警告/エラー0、MCP receipt SUCCESS。GA定量下界を用いる定理だけ既存 `native_decide` 依存を継承する。

**到達していないもの：** ODで `Δ_GI(f;e,z)=L_D(R_f(z,·))` の**一リンク厳密な作用一致はCLOSED**となった。しかしNYの `∃x,L_D(K_b(x,·))≠0` と `∃f,L_D(R_f)≠0` は**別命題**。実際のreceiver rangeの非消去、選択物理源から同一endpoint源へ移るintertwining、真のGI covarianceの一様下界と正fine全深さはOPEN。OA–OCの `Function.Injective points` は有限holonomy分離であり、物理源検出器の単射性ではない。`b>0`各有限体積のPosDefから `inf_H(Q_GI/N_H)>0` は導出しない。

### 2.6 OE–ON：真正signed GI受信器・cross-minor・小正fine全深さ1係数分離

- **OE [#5789](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5789)**：ODの厳密な二posterior signed汎関数評価をLO〜MKの真のGauss-law物理源に接続。元の二文脈局所minorから物理的二座標源 `xU+yW_pU` の二行signed receiverの共通核が選択文脈で自明であることを証明。MF/MKの元の `Q_GI/N_H` 一次下界をそのまま受信器へ輸送し、`x=1,y=0` により**プラケットに依存しない同一物理源U**への正の下界を取得。これらは以前のLB/HY/IDの非零GI witnessを置き換えず、厳密な受信器表示・定量値の接続を強めるもの。
- **OF [#5790](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5790)**：GXにより実際のfine-right zero-selector `a⁽⁰⁾_r` のGauss-law Hilbert源が `S_{n,r}(a⁽⁰⁾_r)=U` と厳密に等しいことを使い、任意有限Krylov深さ・任意非負fine couplingでOEの元の二posterior signed受信器下界を零次選択源に輸送。frozen `b_n>0` は別途固定する。

- **OG [#5791](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5791)**：HFの真正right-Krylov係数GI modal検出器が零次選択係数についてODのsigned二posterior物理受信器（同じU）と厳密一致することをLeanで証明。任意の有限深さr,sで同一スケールn・同じ物理文脈のmodal GI実数値は等しい。さらに**先に実際のWilson文脈z,z'を選んでから、全有限rで同一正のQ_GI/N_H下界を示す** `∃z,z' ∀r` を証明。exact-head #39725595181、Lean 10868/10868、5/5公理監査、sorryAxなし、変更警告・エラー0、MCP receipt SUCCESS。3件は標準公理のみ、2件は既存native_decideを継承する。新規公理なし。

- **OH [#5793](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5793)**：OGの真正二行GI frameから、固定スケールnで同じ実Wilson文脈の**一行を深さrと独立に選択**。この真のHF modal検出器に対して全有限深さで正準零次係数の二乗応答が `(Q_GI/N_H)/(20 E_b²)>0` 以上であること、mathlibの線形rank-nullityとHF既存定理から係数核のfinrankが正確にrであること、および各深さで同じ受信器に検出される正の開係数球があることをLean4で証明。exact-head CI #39729769207、Lean 10869/10869、6/6公理監査、sorryAxなし、変更警告・エラー0、MCP receipt SUCCESS。元の二posterior・Gauss-law源・Perron半密度はそのまま。**係数核の非零ベクトルが非零物理源かは未証明**。

- **OI [#5794](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5794)**：OHで証明済みの深さ共通の一行GI零次検出を使い、任意の係数aに対して真正HF modal値の比 `t_r=Φ_r(a)/Φ_r(a0)` と明示的なkernel残差 `k_r=a-t_r a0` を構成。`Φ_r(k_r)=0`、正確な係数分解、元のHJ Gauss-law物理Hilbert源の `S_r(a)=S_r(k_r)+t_r U`、選択された同じ真のWilson文脈でOD二posterior signed FF受信器の `S_r(k_r)` 応答が0になることをLeanで証明。固定nの一行・同一文脈について、すべての有限rと実係数aに同時に適用できる。exact-head CI #39731413087、Lean 10870/10870、6/6公理監査、sorryAxなし、変更警告・エラー0、MCP receipt SUCCESS。5件は標準公理のみ、1件は既存native_decide継承。**残差が非零物理源・全文脈不可視源だとは結論していない**。
- **OJ [#5796](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5796)**：OHで選択された真正一行と任意の別真正リンク・Wilson文脈のHF受信器を用い、元の零次源と実際のright-Krylov係数に対する交差minorを定義。OIの明示的残差kについて、`M_{01}(a)=Phi_0(a0)Phi_1(k)=Phi_0(a0)L_{D_1}(R_{S(k)})` をODの変更されていないsigned FF物理receiverと一致させ、`全minor=0 ⇔ k∈ker Phi_all`、全文脈核の一行値＋全minor判定、`ker S ⊆ ker Phi_all ⊆ ker Phi_single`、真正非零minorが与えられたときの非零物理残差検出、OH anchor-square下界をU係数へ輸送する不等式を証明。exact-head [CI #39742256154](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39742256154) SUCCESS、Lean 10871/10871、8/8公理監査、sorryAxなし、変更警告/エラー0、MCP receipt SUCCESS。**非零minorの存在・任意正fineの全係数源非退化性を仮定または証明していない**。
- **OK [#5799](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5799)**：真正SU(2) normalized fine Wilson作用素 `T_fine` による `U` の固有直線条件 `T_fine U=cU` が成立する場合、全有限深さで `R_j=c^jU`、実HJ源 `S_r(a)=(Σ a_j c^j)U`、すべての元の二posterior GI交差minorが0とLean証明。OH真正原Wilson非零anchorを用いると固定n・凍結coupling `β(n)>0` で **全有限r同時に** `ker S_r=ker Φ_all,r`。これは物理源rank-one縮退分枝での正しいsource/GI核一致であり、架空のdetector単射性を加えない。逆向きに **非零minorが実在すれば** `r>0`、`β(n+1)>0`、`T_fine U∉ℝU` が必要。非零minor実在そのものや正fine非固有性は証明していない。source `791bb6fa04523c48a6ec1574f49b3708050c41fa`、squash `57ee9b2136887f72ca42cd4bddd8a68a480ed45e`、exact-head [CI #39745586647](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39745586647) SUCCESS、Lean 10872/10872、公開15/15公理監査（14件標準3公理のみ、1件既存finite-lattice native_decide継承）、sorryAxなし、変更警告・エラー0、MCP receipt SUCCESS。
- **OL [#5801](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5801)**：IYで証明済みの空間SU(2)Wilson作用 (W(B_0)=0, W(B_1)≥2) とIXの真正temporal crossing Haar平均不変性から、元のone-slab Wilson Haar-row差のβ=0微分が ≥1 であることを証明。両rowがβ=0で1に一致するため、数学的に正の体積依存区間で真のHaar-row値が厳密に異なる。IVの真正physical Hilbert等価定理により同じ区間で **元の正規化fine Wilson作用素 `T_t U∉ℝU`** をLean証明。独立に正凍結couplingがあるとHY/IS/IUの実GI anchorから、真正depth-one係数pivotは非零Gauss-law物理源を合成し、その選択一行の真の二posterior GI応答は0。**全リンク・全文脈で不可視とは証明しておらず、非零2-context minor存在もOPEN**。source `596be095da2afa654d8054d5ffbfb5ca26b8bc1f`、squash `d8da75fcb269fe85ec0ea6a9f7ccd5564a697977`、[CI #39750196718](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39750196718) Lean 10873/10873 SUCCESS、公開5/5公理監査・sorryAxなし・変更警告/エラー0・MCP receipt SUCCESS、4件標準公理のみ、1件は既存native_decide継承。
- **OM [#5803](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5803)**：LMが示す元の正凍結Wilson空間二文脈minorの非零性を、JIの `d/dt|₀` 真正normalized fine源minor公式で小正fineへ移し、OJの元のsigned HF二行・零次／一次Krylovモードminorとの厳密同一性を証明。任意有限H・凍結 `β(n)>0` で二つの実Wilson文脈をfineより前に選べ、体積依存 `δ_H>0` の `0<β(n+1)<δ_H` に非零minorが存在。第一受信器で零の同じ非零物理pivotを第二受信器が検出。source `843498afe0f4603316d6c4567a1ac0bbcfc6a514`、squash `4d63b07ad467091855c04af5f8f43be1e143296f`、[CI #39752764954](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39752764954) **10874/10874 SUCCESS**、8/8公理監査、sorryAxなし、warning/error 0/0、MCP receipt SUCCESS。
- **ON [#5804](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5804)**：OMの真正非零2×2 minorからすべての実深さ1係数を二つの真正GI文脈が分離。元のHJ全文脈検出器 `Φ_all,1` と真正物理Hilbert合成写像 `S₁` に `ker Φ_all,1=ker S₁={0}`、`U,T_tU`の実線形独立性を証明。source `18bd4e1de81cc21f624c3cd06b75e5a7bc2c10c6`、squash `b5d56f40f6682ec87d0b064428d80eb07da755a4`、[CI #39754031020](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39754031020) **10875/10875 SUCCESS**、5/5公理監査、sorryAxなし、warning/error 0/0、MCP receipt SUCCESS。
- **OO [#5806](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5806)**：真正Gauss-law物理Hilbert右Krylov深さ2の3モードを厳密同定し、元の二posterior HF受信器との厳密一致とOMの先頭2×2 minor非零を輸送。選択二行受信器で消える実Schur係数残差R₂は**係数ベクトルとして非零**。Hilbert合成像・第三GI文脈応答は厳密に表示したが、非零性は証明していない。source `e98d877a3c75245211e02f75e67e61ebdeb76cc3`／squash `375cd6826b997b6de923f032e33c25e37584b4ca`／[CI #39757133108](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39757133108) **10876/10876 SUCCESS**、13/13公理監査、sorryAxなし、warning/error 0/0、MCP receipt SUCCESS。
- **OP [#5807](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5807)**：OOの真正二行受信器の全同時零係数を**ちょうどR₂の一次元直線**と証明。全文脈核・物理源核の包含、真の物理合成単射性⇔R₂の真のHilbert像非零、全文脈GI単射性⇔第三の**真正Wilson二posterior文脈**による同じR₂の検出を必要十分条件としてLean4証明。後者非零は仮定・証明していない。source `13a0f59989e1366cecc6407f6848de390037613e`／squash `a53295e837d60778959349cbf880fa6064f882de`／[CI #39763001799](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39763001799) **10877/10877 SUCCESS**、9/9公理監査、sorryAxなし、warning/error 0/0、MCP receipt SUCCESS。
- **OQ [#5809](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5809)**：真正元Wilson正規化fine伝達作用素Tの実Schur物理残差 `S₂(R₂)=0` を用いると、OMで既証明の非零二文脈minorによりT²UはU,TUの実線形結合になる。この実Wilson二次元閉包を全j、全有限rに帰納輸送し、ONの既証明二行GI分離から**全rで実Hilbert物理源核=全文脈GI検出器核**をLean証明。さらに有限H・凍結正・小正fineで核一致またはSchur実物理源非零の無条件二分。source `b248c1681a41130619f3b8fb737ee70e03853bb5`、squash `b1c968700c3e59a79fd78151c52c92877e3b8254`、[CI #39767540710](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39767540710) **10878/10878 SUCCESS**、7/7公理監査、sorryAxなし、warning/error 0/0、MCP receipt SUCCESS（6件標準3公理のみ、1件既存native_decide継承）。
- **OR [#5810](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5810)**：元の真正二posterior GI応答二乗を、FXで証明済みの正のposterior密度差分散で割って積分するGL質量が非負と証明。OQの二次元閉包分枝では全有限rで実Hilbert物理源ゼロ⇔本来のGI/GL質量ゼロ、非零実源⇒質量厳密正。さらに有限H小正fineで全深さ定性正値性または同じ実Schur物理源非零の無条件二分。source `2fb4bdc5934f2f5bac5c5198c2a524851f721ca3`、squash `34b26d9bad92babf4f484adae418bc767129ddf4`、[CI #39769721363](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39769721363) **10879/10879 SUCCESS**、7/7公理監査、sorryAxなし、warning/error 0/0、MCP receipt SUCCESS（2件標準3のみ、5件既存native_decide継承）。
- **OS [#5812](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5812)**：ONの真の深さ1元Wilson物理・全文脈GI単射をmathlib有限次元逆Lipschitz定理で固定有限Hの正ノルム係数評価に定量化。実Schur物理源が非零**なら**OPにより深さ2の全3係数にも同様の評価。ORとつなぎ、全深さGL質量正値性または深さ2係数ノルム安定性という無条件二分。source `2321e4a5dd804f52e13a265297c28aa4702e963a`、squash `daf1c714f08ed57d42d9e5c3b92e12601bc61478`、[exact-head CI #39774820731](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39774820731) **10880/10880 SUCCESS**、4/4公理監査、sorryAxなし、変更warning/error 0/0、MCP receipt SUCCESS（2件標準3のみ、2件既存native_decide継承）。
- **OT [#5814](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5814)**：元の完全Wilson核と実ゲージ正規化・二相互作用posteriorを接続し、連続ゲージ不変な非零物理源の真正GI検出をLean4証明。CI #39779364146、10881/10881、5/5公理監査、sorryAxなし。
- **OU [#5815](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5815)**：実normalized Gauss-law Wilson一スラブ作用素の連続Haar-L²像を正確なA†A分解で構築。CI #39781160365、10882/10882、3/3公理監査、sorryAxなし。
- **OV [#5816](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5816)**：本来のGauss-law物理L²固定点を、積Haar全supportを使って連続代表の点ごとのゲージ不変性へ移す。CI #39791923530、10883/10883、4/4公理監査、sorryAxなし。
- **OW [#5817](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5817)**：全非負fine・全有限Krylov深さで実物理源核=元の全GI文脈核を証明、Schur物理源非零なら真の第三GI検出。source `bc3db90ad1172a3ae8343883f22d87b590274674`、squash `48c83c2deeb86bf6a544206dd6a0a28caa32aaa5`、[CI #39852361096](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39852361096) **10884/10884 SUCCESS**、公理監査5/5、warning/error 0/0、MCP receipt SUCCESS。
- **OX [#5818](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5818)**：OWとORを接続して **全非負fine・全有限rにて `M_GL(S_r a)=0 ⇔ S_r a=0`、非零源の厳密GL質量正**。source `f340a912972c57a51f5fe222ff5484e0ad468b25`、squash `c73ea9f21c28b60080f793383b344d0c78c4ca4a`、[CI #39854681185](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39854681185) **10885/10885 SUCCESS**、公理監査2/2、sorryAxなし、warning/error 0/0、MCP receipt SUCCESS。
- **OY [#5819](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5819)**：元の完全Wilson SU2一スラブ核LJの厳密正Haar二次形式と実Gauss-law物理転送のinner raw integralを、積Haarとa.e.同値で厳密同一視。全有限rの非零Krylov実物理源で正fine転送エネルギー厳密正、正規化転送不消滅と1段shift核一致をLean証明。source `da71dff1676d1728c81adb0dc88f25a093aa6d2a`、squash `7569fcf984e8040c314bbe723f56393d1faf524b`、[exact-head CI #39856189021](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39856189021) **10886/10886 SUCCESS**、公理監査6/6（全件標準3公理のみ）、sorryAxなし、変更warning/error 0/0、MCP receipt SUCCESS。
- **OZ [#5821](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5821)**：実元Wilson正fine転送の厳密正値とOU/OVの反復連続・ゲージ不変代表を接続し、全有限rの非零実Krylov源で全kの転送後非零性。OM/ON小正fine深さ1独立性を各kへ輸送（rank3は未証明）。source `2d1c4ff6f45a0d51ef90c6a2353d61dc70f576d6`、squash `feac7e92d3e56f5301d1f8ecbc66dceb4d74c011`、[exact-head CI #39857992320](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39857992320) 依存範囲 **10886/10886 SUCCESS**、公開公理監査4/4（3件標準3のみ・1件native_decide継承）、sorryAxなし、変更warning/error 0/0、MCP receipt SUCCESS。

**量化の境界：** OGで閉じたのは**固定nにおける零次selector**の同一源・同一文脈・深さ互換であり、任意係数列や異なる格子スケールでの同一endpointではない。Q_GI/N_Hの正下界は有限体積の選択文脈に依存する。
### 2.7 次段階P4-Q2-PA：元のWilson第三物理モードGramと高次fine展開（OPEN）

OWは元の実右Krylov全有限深さで物理源・全文脈GI核の一致を無条件に証明し、OXはその元の二posterior GL質量零集合と物理源零集合の一致を非負fine全域に延長した。OYは正fineで実物理Wilson二次エネルギーの厳密正と全有限Krylovの1段shift核保存を証明した。残る中心は**実Schur物理源非零性**である。OYで元の一スラブWilson完全核の真のHaar二次形式厳密正値性を実Gauss-law物理転送の内積へ輸送し、1段shift核保存を証明した。OZで全反復kの非消滅・小正fine隣接二モード非退化を証明した。ただし三モード独立性はOPENであり、次は実物理Gramと高次fine Taylorの新しい非零係数を真の一スラブ積分から証明する。

1. **本当の正fine第三物理モード**：実際の `S₂(R₂)` のGauss-law Hilbertノルムを原Wilson一スラブ積分・高次fine微分と比較。必要なら高次Wilson空間作用多項式・少なくとも3つの真正境界値による非退化性を証明する。形式的なrank 3や独立モードを仮定しない。
2. **本当の第三GI受信器**：本来の二相互作用posterior・FF receiverと同じS₂(R₂)で `∃e'',z'', Φ_{e'',z''}(S₂(R₂))≠0` を直接検出する。物理源が非零でも全GI検出は自動ではないことをOPで区別済み。
3. **一様正定量下界**：ORの定性的な `M_GL(f)>0` は任意のrについて成立しても、それだけで `∃c>0∀H,r,f, M_GL(f)≥c‖f‖²` とはならない。真正posterior covariance、Wilson tail、coupling scheduleを実際に評価して必要な一致条件を示す。
4. **同一endpoint・強極限はさらに別**：U0、E、FとH1-C1/C2/C3は未解決のまま保持し、有限体積正値性を連続体mass gapへ飛躍させない。

## 3. 次の核心：本当に不足する数学的入力

### Gate U0 — 真正Wilson GI密度または同等のframe coercivityを一様化

**PZ37ZA #5935による確定した障害：** 真正二文脈・transfer補償済み局所GIの正規化 `Q_H/N_H` は、固定frozen `b≥0` では全文脈について `Q_H≤96E_b⁴` かつ `N_H≥2(H+1)` であるため、**一様な正下界を持たないことを証明済み**。結合スケジュールでも共通Harnack振幅上界を課すと同様。したがって以下に残る『この二文脈 `Q_H/N_H` の正下界を導く』という旧候補は採用できない。一方、真正full-link / all-context GL積分Gram・同一endpoint源の一様coercivityは**別対象としてOPEN**であり、このno-goは否定しない。


**求める条件の一例：** 自然な有限格子・coupling schedule・相容れる物理文脈族に対して、`Q_{\rm GI}(H,b_H,\ldots)/N_H`の十分な正下界と`E_{b_H}`の同時制御を**真のWilson積分から導く**。より直接的には`k_H=(Q_{\rm GI}/N_H)/(10E_{b_H}²)`そのものの有効な正下界、または必要な物理source作用素の相当する非退化性を証明してもよい。

**既存証明からは出ないこと：** `∀H\,∃(z_H,z'_H),Q_H>0`は`∃c>0\,∀H,Q_H/N_H≥c`を含意しない。さらに文脈や選択plaquette`p_H`が各Hで独立に選べるだけでは、projective/物理時間の**同一source family**は得られない。`E_b`の一様上界だけでも`Q_{\rm GI}/N_H`の下界は得られない。

**優先して調べる真の対象：** signed posterior receiverの空間Wilson局所minorの二点相関、局所感度の位置依存、真正Wilson fiber-Haar posterior energy、volume依存の重なりや相関の減衰。Dobrushinをデフォルトの代替模型として再構成しない。**証明可能な新しい定理と、未証明の推測を必ず分ける**。

### Gate E — 空間`p`依存Gramを同一のendpoint物理源へ接続

MF–MKの量化は`\sum_p R_p(x,y)`や`∃p\,R_p(x,y)`で、`R_p`の物理源は`xU+yW_{H,p}U`。高次Krylov/endpointで必要な`S_{n,r}a`、真のfine transfer/receiver、実際のoriginal二posterior GI detector`Φ_{n,r}`と**自動的には等しいものではない**。

必要な証明は、実際のendpoint source写像で選択源・平均frameをtransportした際に、同じsigned GI応答・ノルム・誤差がどう変化するかという**具体的なintertwining / interpolation / controlled remainder**。架空の等長同型やrow rankで代用しない。LM/LNにglobal original source planeの非零性があることと、任意Krylov源へのinjectivityを混同しない。

### Gate F — positive fine coupling・高次Krylovの全源分離

真の`S_{n,r}`と`Φ_{n,r}`の組に対し、物理的不可視部分`I_{\rm phys}=S_{n,r}(\ker\Phi_{n,r})`を考える。

- **CLOSED（OW #5817）：** 正frozen coupling、任意有限体積、**全有限深さr・全非負fine** で `ker S_r=ker Φ_all,r`。したがって、同じ全original GI受信器を用いた `I_phys=S_r(ker Φ_all,r)={0}` はこの量化範囲で証明済み。これを新たなOPEN gateに戻さない。
- **OPEN（物理係数の独立性）：** ONの小正fine深さ1で `ker S₁={0}` が証明済み。PA/PCで全シフト2モード独立・厳密2×2 Hankel positivityまで証明したが、**深さ2の `ker S₂={0}`、真Schur物理像非零、3×3 Hankel det>0、任意rの `S_r` 単射、体積・深さ・fine一様強制性はなおOPEN**。`ker S_r=ker Φ_all,r`とは異なる命題。
- Gate Eのtransportが成立しても、**同じ全source spanへの分離・Coercivity**を別途示す必要がある。

### 次の解析ゲート PD — 元のWilsonモーメントで第三モードを判定

PB/PCの真正Wilsonモーメント `m_j=⟪U,T_t^jU⟫_physical` と小正fine区間での `D₂=m₀m₂-m₁²>0` から、`U,T_tU,T_t²U` の独立性は元のWilson模型の **`D₃=det[[m₀,m₁,m₂],[m₁,m₂,m₃],[m₂,m₃,m₄]]>0`** と同値。追加で必要な厳密不等式は

```text
m₄ (m₀m₂-m₁²) > m₂³ - 2 m₁ m₂ m₃ + m₀ m₃².
```

元の正規化一スラブ核の反復Haar積分（真の4-slabモーメント）または真正第三二posterior受信値の非零性から証明する。**PCの全シフト2×2正定値性だけではrank3は導けない**（二点スペクトルの正作用素が反例）。スペクトル支持点数3以上を仮定せず、真正Wilson核から導出する。仮に有限Hのrank3が成立しても、U0・endpoint・連続体質量ギャップは別ゲート。

### Gate U1–U4 — 空間可和性・深さ・scale

| Gate | 受理できる次の証明 | 現状 |
| --- | --- | --- |
| U1 真正 signed response | 任意の実物理signed sourceに対するoriginal受信器の応答・posterior covarianceの定量比較。参照Haarを元のposteriorへすり替えない | OPEN（一部固定源の結果あり） |
| U2 空間可和性 | 実際の全リンク/plaquette相関tailの局所化と`H`独立または要求された重み付き可和評価 | OPEN |
| U3 Krylov深さ | 全`r`で共通source familyのnorm・fine innovation・誤差が制御される定理 | OPEN |
| U4 coupling/spacing | frozen`b_n`とfine`t_{n+1}`を区別した真正schedule、格子間隔・volumeに耐える定数とsummability | OPEN |
| Relative比較の注意 | 以前の`A_W/D₁₂`相対係数がHとともに小さくなることは、絶対連続体mass gapの不可能性を示さない | 既存証明の適用範囲 |

## 4. H1-C3および連続体問題は別々のOPEN gates

| Gate | CLOSEと呼ぶための実際のLean定理 |
| --- | --- |
| **C1：coarse/fine物理的一致** | 元のWilson lawでの真正共通物理marginal、Gauss則、正確なdescent/source対応 |
| **C2：強収束する物理transfer** | 同一物理source family上でoriginal細格子の時間発展・再構成を比較し、実際の物理Hilbert strong limitが得られる |
| **C3：軌道に沿う可和誤差** | 実際の`b_n,t_{n+1}`スケジュール、必要な`|b_{n+1}-b_n|`等を含むsummable error、同一のlimitを与える |
| **一つの自然時間構造** | 多時刻の極限が**同じ一つの物理作用素**の冪・semigroupであり、独立した各時刻の点ごとの極限でない |
| **H2：物理時間Hamiltonian** | 格子間隔を正しくスケールした強連続semigroup、非自明な正自己共役generator |
| **H3：OS/Wightman再構成** | 連続体の反射陽性、局所化、物理gauge-invariant observable・真空・スペクトル支持 |
| **H4：4D Yang–Mills質量ギャップ** | 完全な非自明4次元連続体Yang–Mills構成と、エネルギー運動量スペクトルの厳密に正のmass gap |

**すべてOPEN。** 有限格子の`D₁₂`や`A_W`の正スペクトル、真の非零GI witness、Gram inverseのLipschitz性のいずれも、単独でこの表をCLOSEDにしない。

## 5. 実装するときの優先順位：数学的阻害条件に近い順

1. **Source-family compatibility の正確な定義・分解。** MF/MG/MJ/MKのどの作用素が本当に元のendpoint `S_{n,r}`へ移送できるかを、構造写像と偽になる場合のobstructionに分ける。定義を置いただけで移送可能と主張しない。
2. **Authentic local-GI energy のcross-volume比較。** 実際のWilsonian sourceのlink/plaquetteごとの感度・posterior-fiber二乗モーメントを読み取り、`Q_{\rm GI}/N_H`の増減・下界候補を具体的に分解する。新しい独立分布を作らない。
3. **Signed spatial covariance の可和性**と**スケール互換な局所選択**。MKの`p_H`に許された選択依存を明記し、固定sourceへの局所化が必要なら別の証明を構築する。
4. **OWで済んだ物理不可視源の消去は再証明しない。** 元の完全Wilson核・二posteriorの構造から真のSchur物理源 `S₂(R₂)` の非零性、実三モードHankel `D₃>0`、または元の第三GI文脈の非零受信値を証明し、その後に全深さの係数独立性・定量的強制性を検討する。Dobrushinや架空のspectral measureへ戻らない。
5. U0/E/F/U1–U4が十分になってから、実際のC1/C2/C3を一つの物理時間極限として閉じる。H2/H3/H4はさらに独立に証明する。

**「次のPRに書くべきもの」は、単にGram定理の代数的帰結を増やすことではなく、上記のいずれかの**実際の物理的・解析的obstructionを減らす定理**である。逆に、未証明のuniformな仮定を`theorem`の引数として追加しただけではGateをCLOSEしない。

## 6. 検証できるLean定理・ファイルへの導線

すべてのファイルは`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaar`で始まり`.lean`で終わる。GitHubの[authoritative branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit/MGAP4D/MathlibAnalytic)で**実ファイル・実定理**を読む。

| Track | Exact suffix | Checkable result |
| --- | --- | --- |
| 最初の原空間minor | `OriginalGISpatialActionMinorTangentV5_JI` | 元の空間`Δ_W`とfine couplingの導関数 |
| spatial nonzero（重要） | `OriginalTwoContextSpatialGIMinorNonzeroV5_LM` | `p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts` |
| 真の局所物理源 | `OriginalLocalPlaquetteGIWitnessV5_LO` | `p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive` |
| 本当のplaquette count | `OriginalCountControlledLocalPhysicalGICoercivityV5_LQ` | `p4Q2LQ_originalSpatialPlaquetteCount_eq_card` |
| Harnack/補償 | `OriginalTransferNormalizationCompensatedCoercivityV5_LW` | `p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original` |
| cancellation-free `Q_GI` | `OriginalLocalGICompensatedSquareEnergyV5_LY` | `p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor` |
| ローカル上界 | `OriginalCompensatedGIUniformLocalMomentBoundV5_MA` | `p4Q2MA_originalCompensatedLocalGIMinor_sq_le_four_contrastSq_sq` |
| 活性集合と真正性 | `OriginalGIActivePlaquetteDensityV5_MB` / `OriginalActiveGIPhysicalCoerciveDensityV5_MC` | `p4Q2MB_originalActiveGI_density_ge_energy_fraction` / MC物理強制性 |
| 真の空間線形床 | `OriginalLinearGIPhysicalGapV5_MF` | `p4Q2MF_originalFullPhysicalGapAverage_ge_linearGI` |
| Gram/逆写像 | `OriginalPhysicalGramDeterminantV5_MG` / `OriginalPhysicalGramQuantitativeDeterminantV5_MH` / `OriginalPhysicalGramInverseV5_MI` / `OriginalPhysicalGramInverseLipschitzV5_MJ` | exact polarisation / `det≥k²` / adjugate / two-input Lipschitz |
| **空間物理GI：最新MK（このトラック）** | `OriginalMeanEnergySinglePlaquetteV5_MK` | `p4Q2MK_originalGI_exists_meanEnergyPlaquette`、`p4Q2MK_originalPhysicalGI_exists_authenticMeanPlaquette` |
| **時間Gaussian〜真正物理GI：OD** | `OriginalSignedGaussianStrictV5_NY` / `OriginalGaussianKernelSpanDenseV5_NZ` / `OriginalGaussianAllFiniteStrictGramV5_OA` / `OriginalGaussianMatrixPosDefV5_OB` / `OriginalGaussianFiniteInterpolationV5_OC` / `OriginalTwoPosteriorGaussianSeparationV5_OD` | NY Gaussian `T_L>0`; NZ稠密; OA/OB全有限Gram PosDef; OC補間; **OD `p4Q2OD_originalPhysicalGI_eq_truePosteriorSignedFunctional`** とposterior kernel section検出 |
| **真正物理GI・右Krylov二次閉包／真正GL質量：OE–OR** | `OriginalSmallFineKrylovTwoContextMinorV5_OM` / `OriginalDepthTwoKrylovSchurResidualV5_OO` / `OriginalDepthTwoExactGIKernelV5_OP` / `OriginalFineQuadraticCollapseAllDepthV5_OQ` / `OriginalFineQuadraticAllDepthGLMassV5_OR` | OO/OP：実Schur残差と一次元核、OQ：実Schur物理ゼロ分枝の全r核一致と無条件二分、OR：同分枝の全r実GI/GL質量厳密正値性と無条件二分。第三受信器非零・実Schur物理像の分枝決定はOPEN |

| **真正Wilson全深さ検出・全反復・モーメント：OW–PC** | `OriginalWilsonAllDepthGIKernelFaithfulnessV5_OW` / `OriginalWilsonAllIteratedFineKrylovNonzeroV5_OZ` / `OriginalWilsonAllShiftTwoModePhysicalGramV5_PA` / `OriginalWilsonPhysicalKrylovHankelMomentsV5_PB` / `OriginalWilsonStrictShiftedHankelMomentsV5_PC` | OW全有限r・fine非負のsource/GI核一致、OZ任意回非消滅、PA全shift実物理二モードGram PosDef、PB真正物理Gram＝Hankel、PC厳密二次Hankel minor。rank3 OPEN。 |

## 7. CIを効率的に保ちながら厳密性を保つ

定理を新しく書いた場合は次を省略しない。

- 定理正本branchのfresh SHA、**変更Lean全文**、import先と真正物理定義、実際に必要な前提条件を再観測する。
- pinned Lean/mathlibの既存補題を優先し、数学的に別物のindependent-Haar検出器・架空のrank/source・未検証uniform条件で不足を埋めない。
- **変更した依存の最大leaf**に対する`lake build`、CI exact source SHA、変更ファイルのwarning/error 0件、全公開`#print axioms`で`sorryAx`なし、独立MCP completion receipt SUCCESSを確認する。既存有限格子の`native_decide`由来の依存は「新規公理」と混同しない。
- 変更が`README.md`/`ROADMAP.md`だけの場合、現在の`PR Lean Fast Check`はパスフィルタで**Lean CIを起動しない**。Markdown表示・相互リンク・正本SHAを直接点検し、1万以上のLeanモジュールを再ビルドしない。Lean変更時のキャッシュキーはpinned toolchain/manifest、authoritative baseと安全なPRリトライscopeで扱い、不要なフルビルドを繰り返さない。
- PRソースCI成功後に定理正本へ統合し、**squash SHAとsource SHAを別々に記録**。docs-onlyマージを新しい数学的達成と数えない。

再現例（**検証済みPC theorem-bearing merge**；新規証明leaf）:

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch --detach 104e0008d5d7372bf45f226c51fe1a61dfc67805
cat lean-toolchain
# optional when available: lake exe cache get
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonStrictShiftedHankelMomentsV5_PC
```

## 8. 検証済みの履歴とリンク（旧版の「最新」を繰り返さない）

- 真正Wilson物理transfer・有限格子operator：[#5440](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5440)、[#5472](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472)、[#5485](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5485)、[#5514](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5514)。
- 真のsigned sourceと物理的不可視sector：[#5574](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5574)、[#5621](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5621)、[#5639](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5639)。
- 空間GI検出（既に閉じたGate S）：[#5656 JI](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5656)、[#5657 JK](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5657)、LM `OriginalTwoContextSpatialGIMinorNonzeroV5_LM`。
- 独立の時間posterior/receiver経路：[#5662 JP](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5662)、[#5664 JR](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5664)、[#5665 JS](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665)。JS receiver-span membershipの未証明性は**空間LM定理の欠如とは別問題**。
- 真のGI二乗エネルギー・空間frame・逆写像：[#5729 MB](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5729)、[#5731 MC](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5731)、[#5733 MD](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5733)、[#5734 ME](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5734)、[#5735 MF](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5735)、[#5736 MG](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5736)、[#5737 MH](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5737)、[#5738 MI](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5738)、[#5739 MJ](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5739)、[#5740 MK](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5740)。

時間Gaussian・真正二posterior/物理GI経路：[#5776 NT](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5776) → [#5781 NY](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5781) → [#5782 NZ](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5782) → [#5783 OA](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5783) → [#5784 OB](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5784) → [#5785 OC](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5785) → [#5787 OD](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5787)（[exact-head CI #39716611363](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39716611363)、MCP receipt SUCCESS）。

- 真正物理受信器・Krylov零次源：[OE #5789](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5789)（exact-head #39719598610、Lean 10866/10866）→ [OF #5790](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5790)（exact-head #39720662153、Lean 10867/10867）、いずれもSUCCESS / sorryAxなし / MCP receipt成功。さらに [OG #5791](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5791)（#39725595181、Lean 10868/10868、5/5公理監査、MCP receipt SUCCESS）が同一文脈all-depthを形式化。

- 真正一行GIの全深さ係数frame：[OH #5793](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5793)（[exact-head CI #39729769207](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39729769207)、Lean 10869/10869、6/6公理監査、sorryAxなし、MCP receipt SUCCESS）。

- 真正物理Krylov source分解：[OI #5794](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5794)（[exact-head CI #39731413087](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39731413087)、Lean 10870/10870、6/6公理監査、sorryAxなし、MCP receipt SUCCESS）。
- 元の二文脈交差minor・HJ全文脈kernel判定：[OJ #5796](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5796)（[exact-head CI #39742256154](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39742256154)、Lean **10871/10871**、8/8公理監査、sorryAxなし、変更警告・エラー0、MCP receipt SUCCESS、[squash theorem SHA](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/13f961c746306d76685a8a28a7365310c402f3b4)）。
- 真正fine Wilson U固有直線の全深さKrylov縮退・核一致・minor消滅：[OK #5799](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5799)（[exact-head CI #39745586647](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39745586647)、Lean **10872/10872**、15/15公理監査、sorryAxなし、変更警告/エラー0、MCP receipt SUCCESS、[squash theorem SHA](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/57ee9b2136887f72ca42cd4bddd8a68a480ed45e)）。
- 実際の小正fine Wilson物理源非固有直線と、選択GI一行核内の非零depth-one Gauss-law源：[OL #5801](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5801)（[exact-head CI #39750196718](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39750196718) Lean 10873/10873、5/5公理監査、sorryAxなし、警告・エラー0、MCP receipt SUCCESS、[squash theorem SHA](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d8da75fcb269fe85ec0ea6a9f7ccd5564a697977)）。非零GI二行minorとは混同しない。

これらは**有限モデルでどこまで実際に証明したか**を表すリンクであり、Yang–Mills Millennium Prize問題の解決宣言ではない。より古いステップごとのPRと定理の履歴はGit historyに残してある。


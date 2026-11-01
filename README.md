## 検証済み定理 — ACV（2026-11-01 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit` です。default `main` はREADME／ROADMAPのみの文書ミラーで定理正本ではありません。P4-Q2-PZ37ACV・定理PR #6100 はMERGED、定理squash SHAは `46f9580c668f94e819511c7a8b9487f400a030bf`。ACU以前の全定理とno-go、元の物理Wilson模型を保持し、append-only／tighten-only／overwrite-forbidden／same-rootを維持します。

### 元のPerron密度と真正更新後transferでの厳密な正負境界評価

有限体積・相互作用Wilson SU(2)の元FF受信器、中心化Gauss-law物理源、正Perron ground代表、真正transfer norm、更新後のjoint Perron半密度で正規化したoriginal transfer section `U_z`、本来の二interacting posterior、境界対とpair-Haar測度 `ν_H` を変更していません。ABZより `P_z=||T_b||⁻¹ sqrtDensity_b(z)>0`。元境界依存の平方密度を `R_b(z)=sqrtDensity_b(z)²>0`、共通因子を `c_b=||T_b||⁻²>0` とすると、`P_z²=c_b R_b(z)` は厳密な同一模型の恒等式です。密度Rは確率法への置換ではなく、積分から除去しません。

- ACTの真正局所判別量 `d_b(z)=16A_U(z)²−τ(b)W_U(z)` に対し、`Iplus=∫R_b(z)max(d_b(z),0)dν_H`、`Iminus=∫R_b(z)max(−d_b(z),0)dν_H`、`I=∫R_b(z)d_b(z)dν_H` を定義しました。正負とも元の**同じ**Perron平方密度で重み付けします。
- **唯一の消去可能因子は共通transfer norm**：ACU/ACTの真の寄与について、`Eplus=c_b Iplus`、`Eminus=c_b Iminus`、`D_ACT=c_b I`、`I=Iplus−Iminus` をLean4で厳密に証明。従って元の平均GI**二乗証明書** `M_GI>0 ⇔ Iplus>Iminus` です。
- 真正四成分と高次SU(2)Haarの元transfer二乗モーメントを `I4=∫R_b A_U² dν_H`、`Ih=∫R_b W_U dν_H` とすると、`I=16I4−τ(b)Ih`。ACSの真正閾値 `η>τ(b)/(τ(b)+4) ⇔ τ(b)Ih<16I4` となります。`16M_GI=κ(b)c_b(Iplus−Iminus)` も厳密に成立し、原模型のsigned二posterior GI応答と**証明書**を同一視していません。
- **追加の定量的阻害**：ACRの元FF受信器のFC上界`B_b`を用い、負側の元境界Perron重み付き寄与 `Eminus≤τ(b)B_b²` を全有限H・b>0・真正リンクeで無条件に証明。`Eplus>τ(b)B_b²` は元の正の平均GI証明書の十分条件で、逆に`M_GI≤0`なら`Eplus≤τ(b)B_b²`が必要。上記十分条件が実Wilson模型で成立することは**未証明**です。
- 密度優越`Iplus>Iminus`が元模型で実際に確認できれば、ACOの元の二posterior GI応答が非零のOPEN正pair-Haar質量集合が従うことも形式証明しました。体積一様な下界、元の境界Perron密度の消去、残差優越、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills存在・質量ギャップは依然OPENです。

### 検証済みの定理正本・exact-source CI

- 定理PR #6100: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6100 — MERGED。新規Leanファイル1件、8定義・21公開定理、既存Lean・theorem root・workflow・physical model・pinの変更なし。最終source HEAD `5a8138e3cfb0cb3934595c8e57fdb2a7eeb5b51f` とsquash `46f9580c668f94e819511c7a8b9487f400a030bf` のGit treeは完全一致 `bb6d21207744217ab14659d11cce57daa7ae0cb7`。
- exact-source CI #41265239612: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41265239612 — workflow・変更Lean実ビルド・独立completion receipt SUCCESS、11246/11246、21/21公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0。
- 独立マージ後push CI #41265614778: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41265614778 — head=squash、workflow/Lean job/実Lean step SUCCESS、11246/11246、21/21公理は標準3公理のみ、`sorryAx`なし、変更Lean warning/error 0/0。独立MCP completion receipt job #124728634849 もSUCCESS。
- PinはLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` のままで変更なし。

### 次の課題 — ACW（OPEN）

真正境界Perron密度Rと更新後transferの四成分・高次Haarモードを直接使い、正寄与が成立する具体的境界領域の正Haar質量と補集合の負寄与を評価します。FC全域上界より鋭い局所‐大域比較の条件、正負寄与の真の不等式またはその阻害を調べます。モデル置換、未証明の一様下界・残差優越、物理GI応答との証明書同一視を行いません。

---

## 検証済み定理 — ACU（2026-11-01 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAPの文書ミラーであり、定理正本ではありません。P4-Q2-PZ37ACU／定理PR #6097 はMERGED、squash SHA `cadb5d01c9380cea14e65e7f0ae1098fdb7d91e4`。ACT以前の全Lean証明・no-goを保持し、append-only／tighten-only／overwrite-forbidden／same-rootを維持します。

### 元のPerron重み付き正負エネルギーの厳密分離

真正相互作用Wilson SU(2)有限体積模型、Gauss-law中心化物理源、元FF受信器、正Perron ground代表と真正transfer norm、更新後の正規化Perron半密度を分母に含むoriginal transfer section `U_z`、元の二つの相互作用posteriorと境界対、元の外側pair-Haar測度 `ν_H` を一切置き換えていません。全有限H、b>0、真正空間リンクeにおいてACTの局所判別量 `d_b(z)=16A_U(z)²−τ(b)W_U(z)`、正Perron prefactor `P_z>0` を使用します。

- 正負寄与を `Eplus=∫P_z² max(d_b(z),0)dν_H`、`Eminus=∫P_z² max(−d_b(z),0)dν_H` と定義し、両者の元境界Haar法での可積分性・非負性を証明。各符号部分で**同じ**真正Perron²重みを保持し、積分から除去していません。
- 新しい厳密恒等式 `D_ACT=Eplus−Eminus`、`16M_GI=κ(b)(Eplus−Eminus)` をLean4で形式証明。`κ(b)>0`なので、元の**平均GI二乗証明書**が正であることと `Eplus>Eminus` は必要十分。ACSの `η>τ(b)/(τ(b)+4)` と完全同値です。`D_ACT≤0 ⇔ Eplus≤Eminus` および厳密な負側優越も同値です。
- 量的優越評価 `Eminus+ε≤Eplus` から `κ(b)ε≤16M_GI` を証明。未証明の数値ε、残差優越、体積一様下界は持ち込みません。
- **厳密負側優越に対する新定理**：`Eminus>Eplus` が成立する場合、元の境界対にはOPENかつ正の外側Haar測度を持つ集合が存在し、その全配置で `d_b(z)<0`、真正更新後transfer高次SU(2)直交Haar残差 `W_U(z)>0` となり、さらに非零の元transfer高次文字witnessが存在します。これは元GI応答が消えるとの主張ではありません。
- **正側優越時の局所証拠**：`Eplus>Eminus` なら、ACTから `d_b(z)>0` のOPEN正Haar質量領域が従います。ただし局所正値例だけでは平均正値には足りません。
- 元Wilson模型で正側・負側のどちらが実際に優越するかは依然**OPEN**。平均二乗証明書とsigned two-posterior GI応答は同一視せず、連続体4D Yang–Mills質量ギャップの成立も主張しません。

### Lean4・exact-source CI・独立push完了receipt

- 定理PR #6097 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6097 — MERGED。新規Lean定義3、公開定理18、1新規Leanファイル（419行）。従来のLean本体・モデル・workflow・定理root・pinを変更していません。
- exact-source HEAD `c43d643f7fc9d035f6f98f9cfc36d44f2418bd22` と定理squash `cadb5d01c9380cea14e65e7f0ae1098fdb7d91e4` のGit treeはともに `97c13506127dfb49dc0cc265732c412797f54ca2`。
- PR exact-source CI #41263478269 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41263478269 — workflow／Lean job／独立MCP completion receiptすべてSUCCESS、11245／11245 Lean、18／18公理表示は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning／error 0／0。
- マージ後独立push CI #41263878974 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41263878974 — head=定理squash、workflow／Lean job／独立completion receipt job #124723530493 すべてSUCCESS。11245／11245 Lean、ACTを含む従来証明は維持、ACU18／18公理標準3個のみ、`sorryAx`なし、変更Lean warning／error 0／0。
- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。

### 次の研究課題 — ACV（OPEN）

真正Perron代表、更新後transfer section、原boundaryから`Eplus`と`Eminus`を実際に比較できる強制評価・局所符号領域の定量評価を探します。単なる正負分離は元Wilsonデータの優越符号を決めません。根拠のない残差上界、共通support cylinder、体積一様性、full physical Hilbert coercivity、H1–H4、OS/Wightman再構成、連続体4D Yang–Mills存在と質量ギャップは引き続きOPENです。

---

## 検証済み定理 — ACT（2026-11-01 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit` です。default `main` はREADME・ROADMAPの文書ミラーであり定理正本ではありません。P4-Q2-PZ37ACT／定理PR #6094 はMERGED、squash SHA は `4b0a182c406f400fc5c2c2244e3bebc318042973`。ACSおよび以前の全証明・no-go・原Wilson SU(2)受信器を保持し、append-only／tighten-only／same-rootを維持します。

### 真正Perron-transfer分解による厳密なGI二乗証明書判定

元の有限体積相互作用Wilson SU(2)模型、中心化Gauss-law物理源、FF受信器、正Perron代表、真正transfer norm、更新後joint Perron半密度を分母に持つtransfer section `U_z`、真正二posterior、境界対、元の外側pair-Haar法 `ν_H` を変更していません。`P_z=||T_b||⁻¹√density_b(z)>0` を同じ配置に保持します。元の四成分Haar係数二乗和 `tA2(z)`、高次直交残差 `tW(z)`、`τ(b)=(exp(64b)−1)²`、`κ(b)=(2b exp(−32b))²` を用います。

- 局所判別量 `d_b(z)=16 tA2(z)−τ(b)tW(z)=4(τ(b)+4)tA2(z)−τ(b)Var_Haar(U_z)` を定義。更新後の真正transfer sectionの四成分Haar係数と分散から直接評価でき、別受信器ではありません。
- 正本のPerron重み付き平均判別量 `D_b=16∫P_z²tA2(z)dν_H−τ(b)∫P_z²tW(z)dν_H=∫P_z² d_b(z)dν_H=64S−τ(b)Wbar` を定義。外側平均から`P_z²`を除去せず、分散のみを用いた同値表現も形式証明しました。
- 真正GI平均**二乗証明書**`M_GI`と局所証明書`Q_GI(z)`について、`16M_GI=κ(b)D_b`、`16Q_GI(z)=κ(b)P_z²d_b(z)` をLean4で厳密に証明。`b>0`では`D_b>0 ⇔ η>τ/(τ+4)`、`Q_GI(z)>0 ⇔ d_b(z)>0`。局所transfer分散が正なら、transfer四成分割合`4tA2/Var_Haar(U_z)`はACSの元受信器局所割合と一致し、同じposterior閾値で厳密に判定できます。
- **阻害**：全真正境界対で`d_b(z)≤0`なら、真正平均四成分割合`η≤τ/(τ+4)`であり、正の**平均GI二乗証明書**は得られません。逆に`D_b>0`なら、局所`d_b(z)>0`の真正witnessがあり、ACOのFC上界を使って正質量OPEN領域およびHaar質量の明示下界を導けます。ただし局所の一例で`d_b(z)>0`であることだけでは外側Perron重み付き平均の正値性を保証しません。
- `M_GI`と`Q_GI`は**証明書**であり、実際のsigned two-posterior GI応答そのものとは同一視していません。`D_b>0`が元相互作用Wilsonデータで成立するかは依然**OPEN**です。

### Leanカーネル・独立CI確認

- 定理PR #6094: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6094 — MERGED。新規Lean定義3、公開定理15、1新規Leanファイル。旧定理、定理root、ワークフロー、模型、pinは変更しません。
- exact-source HEAD `e8b0de41b6a1acce16e6d8326bef6f5ae32634cf`、定理squash `4b0a182c406f400fc5c2c2244e3bebc318042973` のGit treeは同一 `ae520d1e6b156fa85da05b15461d87a548e0e4b5` です。
- exact-source CI #41261498896: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41261498896 — workflow・Lean job・独立completion receipt SUCCESS。Lean 11244/11244、15/15公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0。
- マージ後独立push CI #41261969922: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41261969922 — head=定理squash、workflow・Lean job・独立completion receipt job #124717874524すべてSUCCESS。依存ビルド11244/11244、ACTの15/15公理は標準3公理のみ、`sorryAx`なし、変更Lean warning/error 0/0。
- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変。

### 次の物理課題 — ACU（OPEN）

ACTは真正のPerron更新後transfer・原境界対で判別量を厳密に定義しましたが、元相互作用Wilson模型で`D_b>0`か否かを直接評価する問題は未解決です。次段階は原Perron代表・同一配置の四成分信号と高次Haar残差の重み付き比較を進め、符号の正否または具体的数学的阻害を判定します。未証明の体積一様下界、残差優越、共通support cylinder、遠方相殺、全Hilbert coercivity、H1–H4、OS/Wightman再構成、連続体4D Yang–Mills存在・質量ギャップを導入しません。

---

## 検証済み定理 — ACS（2026-11-01 JST）

唯一のLean定理正本は formal/real-hilbert-uniform-coercive-strong-limit。default mainはREADME・ROADMAPの文書ミラーであり、定理正本ではありません。最新の証明は P4-Q2-PZ37ACS／PR #6091 MERGED、定理squash aa9af96e369fe5a808c739480ee40af6381667f5。既存ACK・ACL・ACM・ACN・ACO・ACP・ACQ・ACRと従来のno-goをすべて保持し、append-only／tighten-only／overwrite-forbidden／same-rootを維持します。

### 真正Perron重み付き四成分の無次元エネルギー割合

元の相互作用Wilson SU(2)模型、中心化Gauss-law物理源f0、FF受信器F、正Perron代表、真正transfer norm、二つの相互作用posterior、元の境界対と外側pair-Haar法ν_Hを変更しません。b>0、全有限H・真正リンクeにおいて、ACJ/ACKの S=∫Cov_Haar(F_z,E)^2 dν_H>0、Vbar=∫Var_Haar(F_z)dν_H=16S+Wbar>0、Wbar=∫W_F(z)dν_H≥0を使用します。

- 真正四成分エネルギー割合 η=16S/Vbar と高次直交残差割合 ω=Wbar/Vbar を定義し、0<η≤1、0≤ω<1、η+ω=1をLean4で無条件に証明しました。両者は元の物理受信器の同じ分散を分配する数であり、別模型の割合ではありません。
- ACQの元の更新後Perron正規化transfer section U_zとP_z=||T_b||^{-1}sqrtDensity_b(z)>0を維持。η=4∫P_z² A_U(z)² dν_H / ∫P_z² Var_Haar(U_z)dν_H、ω=∫P_z² W_U(z)dν_H / ∫P_z² Var_Haar(U_z)dν_H を厳密に証明しました。外側Haar積分のP_z²を削除していません。
- ACI/ACPの真正posterior誤差に由来する τ(b)=(exp(64b)−1)²>0、κ(b)=(2b exp(−32b))²>0 を使い、臨界割合 c(b)=τ(b)/(τ(b)+4) が 0<c(b)<1 を満たすことを証明しました。
- **鋭い元GI平均二乗証明書の判定**：M_GI>0 ⇔ η>c(b) ⇔ ω<4/(τ(b)+4)。M_GI≤0 ⇔ η≤c(b)。さらに厳密な量的恒等式 16 M_GI = κ(b)(τ(b)+4)Vbar(η−c(b)) をLean4で形式証明しました。元Wilson模型のηが臨界割合より大きいことは依然としてOPENです。
- **同一配置の局所証明書**：真正の元受信器分散 V(z)>0 の場合、η_z=4A_F(z)²/V(z) は0≤η_z≤1、かつ q_GI(z)>0 ⇔ η_z>c(b)。さらに全b≥0に対し 16q_GI(z)=κ(b)[(τ(b)+4)4A_F(z)²−τ(b)V(z)]。この q_GI は真正ACM二乗GI**証明書**であり、実際のsigned two-posterior GI応答と同一ではありません。
- η>c(b)が元物理データに対して実際に検証できれば、ACOの真正SU(2)軌道と外側pair-Haar測度でOPEN・正質量な元GI非零領域が従います。η≤c(b)の場合はACRの高次Perron-transferモード非零witnessが存在しますが、元GI応答がゼロとは結論しません。これらはいずれも既存の正確な物理量での条件付き接続です。

### exact-source Lean4 CIと正本保全

- 定理PR #6091: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6091 — MERGED。新規Lean 1ファイル、16定理、新規419行・削除0。旧Leanファイル・定理root・workflow・モデル・pinは不変。
- 最終source HEAD f1829049edb579a197d59277201d6bc3d283e738、実CI checkout c7d0251293a5c8a012ed0259878ebbc523a15830、定理squash aa9af96e369fe5a808c739480ee40af6381667f5のGit treeは全て93c3bdcb773119816b697102b07fc4ad69a364aaで一致。
- exact-source CI #41258219511: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41258219511 — workflow/Lean step SUCCESS、Lean11243/11243、新規16/16公理表示はpropext・Classical.choice・Quot.soundのみ、sorryAxなし、変更Lean warning/error 0/0。
- マージ後push CI #41258625202: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41258625202 （独立workflow/実Lean stepとMCP completion receiptを別途確認）。
- 独立マージ後push完了receipt：run #41258625202（head=aa9af96e369fe5a808c739480ee40af6381667f5）、workflow/Lean job/実Lean stepすべてSUCCESS、Lean11243/11243、ACSの16/16公理表示はpropext・Classical.choice・Quot.soundのみ、sorryAxなし、変更Lean warning/error 0/0。独立MCP completion receipt job #124708141585 もSUCCESS。
- Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6 を維持。

### 次のACTの物理課題（OPEN）

元の真正Perron重み付きtransfer sectionの四成分エネルギー割合ηについて、元受信器と二posterior/boundaryデータからη>τ/(τ+4)を実際に示せるか評価します。数値・体積一様の下界、full physical Hilbert coercivity、共通support cylinder、遠方相殺、共通positive-fine区間と同じendpoint E/F、H1–H4、OS/Wightman再構成および連続体4D Yang–Mills存在・質量ギャップは引き続きOPENです。

---

## 検証済み定理 — ACR（2026-11-01 JST）

唯一のLean定理正本は formal/real-hilbert-uniform-coercive-strong-limit。default mainはREADME・ROADMAPの文書ミラーであり、定理正本ではありません。P4-Q2-PZ37ACR／PR #6088はMERGED、定理squash SHA fe2244da74fe91fff792cdc4808bb50d5a202855。従来のACK・ACL・ACM・ACN・ACO・ACP・ACQと全no-goを保持し、append-only／tighten-only／overwrite-forbidden／same-rootを維持しました。

### 真正Wilson高次Haar残差の定量的阻害と正質量OPEN領域

元の相互作用Wilson SU(2)模型、中心化Gauss-law物理源f0、FF受信器F、正Perron代表と物理transfer norm、両interacting posterior、元の境界対zおよび元の外側pair-Haar法ν_Hを変更しません。ACK/ACQによる四成分振幅A_F²、真正直交高次残差 W_F(z)=P_z² W_U(z)、平均S>0（b>0）、Wbar=∫W_F dν_H、真正FC上界B、ACPの τ(b)=(exp(64b)−1)² とGI平均二乗証明書 M_GI を使用します。

- 全有限H・b≥0・真正リンクeにおいて、W_F(z)は元の境界対zの連続関数で、0≤W_F(z)≤B²をLean4で証明しました。Wbar>0なら、0<2B²−Wbarおよび ν_H{z:W_F(z)>Wbar/2}≥Wbar/(2B²−Wbar)>0。集合はOPENです。
- **阻害条件付きの無条件含意**：b>0で実際の M_GI≤0 なら、τ(b)Wbar≥64S>0、すなわち Wbar≥64S/τ(b)>0。したがって真正Perron伝達断面U_zの高次残差 W_U(z)>0 が成立するOPENな正Haar質量集合が、上記の明示下界つきで必ず存在します。少なくとも一組の真正境界対zとSU(2)リンク値gにおいて、U_z(g)が定数＋四成分基本文字の射影と一致しない証拠も証明しました。
- **追加GI符号仮定なし**：任意のε>0について Q_ε(z)=(Wbar+ε)A_F(z)²−4S W_F(z) と置くと、T_ε={z:Q_ε(z)>2Sε} はOPENで、0<D_ε=2(Wbar+ε)(B²/4)−4Sε および ν_H(T_ε)≥4Sε/D_ε>0。各z∈T_εでは真正transfer側のA_U(z)²>0と 4S W_U(z)<(Wbar+ε)A_U(z)² が同じ元の配置で成立します。P_z²はこの**局所比較に限り**正因子として相殺されますが、外側平均から除去していません。
- もし全真正境界対で W_U(z)=0 が証明できるなら、逆に元GI平均予算は正になり、ACM/ACOの真正two-posterior GI応答が非零のOPEN正Haar質量集合が成立することもLean4で証明しました。このゼロ残差仮定を**実Wilson模型が満たすとは主張していません**。
- M_GI≤0はあくまで**正の平均GI証明書**の阻害であり、真正two-posterior GI応答の消滅や連続体質量ギャップのno-goを意味しません。物理的な M_GI>0 自体は依然OPENです。

### exact-source CIと形式化保全

- 定理PR #6088: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6088 — MERGED。新規Lean 1ファイル・10公開定理、追加329行・削除0。既存Lean、定理root、workflow、original Wilson receiverは不変。
- exact-source HEAD 6533fc5f0daba0017ab77c3ded3a9ee0568c046d、実CI checkout be445b12de9ea73b857fcb74eb9bf86ec3ffa793、定理squash fe2244da74fe91fff792cdc4808bb50d5a202855 のGit treeは全て325b180f9cfdc53bbf7d048abd0cf68ba4d8e00aと一致。
- exact-source CI #41256507169: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41256507169 — workflow/job/実Lean step SUCCESS、Lean 11242/11242、10/10定理の公理は propext・Classical.choice・Quot.soundのみ、sorryAxなし、変更Lean warning/error 0/0。
- マージ後push CI #41256965003: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41256965003 （定理sourceとは独立に完了を再観測する）。
- マージ後pushの独立完了receipt：#41256965003（head=fe2244da74fe91fff792cdc4808bb50d5a202855）、workflow/Lean job/Lean step すべてSUCCESS、Lean 11242/11242、ACR 10/10公理は標準3公理のみ、sorryAxなし、変更Lean warning/error 0/0。独立MCP completion receipt job #124703166858 もSUCCESS。
- Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6、不変。

### 次の課題 — ACS（OPEN）

元の更新後Perron半密度と真正物理transfer断面の高次SU(2)モードを直接制御し、実模型で重み付き残差／四成分信号の厳格なACP閾値を満たすかを評価します。残差の正質量だけで高次残差の優越を導けず、平均予算の厳格正値も得られません。体積一様GI二乗モーメント正下界、共通support cylinder、遠方相殺、全物理Hilbert coercivity、共通positive-fine区間と同じendpoint E/F、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills存在と質量ギャップは引き続きOPENです。

---

## 検証済み定理 — ACQ（2026-11-01 JST）

唯一のLean定理正本は formal/real-hilbert-uniform-coercive-strong-limit。mainはREADME・ROADMAPだけの文書ミラーであり、定理正本ではありません。最新定理 P4-Q2-PZ37ACQ／PR #6085（MERGED）、定理squash a6a40dc277df4f0b6f8c1b28a7aa1319d60b5c36。既存ACK・ACL・ACM・ACN・ACO・ACP・各no-goを維持し、append-only／tighten-only／same-rootです。

### ACQの真正Perron伝達断面と四成分直交残差

元の相互作用Wilson SU(2)模型、中心化Gauss-law物理源 f0、FF受信器 F、正Perron代表、真正transfer norm、二つの相互作用posterior、元の境界対と外側pair-Haar法 ν_H は一切変更していません。ABZ/ACAの厳密な元物理恒等式 F_z(g)=定数_z−P_z U_z(g) を使用。ここで P_z=||T_b||^{-1} sqrtDensity_b(z)>0、U_z(g)=I_{f0}(B[e:=g])/sqrtDensity_b(A,B[e:=g]) は更新後の真正joint Perron半密度を分母に含む元のtransfer sectionです。

- SU(2)の真正四成分零平均Haar文字 φ_j を用い、transfer係数 u_j(z)=∫U_z(g)φ_j(g)dHaar(g)、transfer四成分振幅 A_U²=∑_j u_j²、真正直交残差 W_U=∫[U_z−∫U_z−4∑_j u_j φ_j]²dHaar≥0 を定義します。
- 全有限H、非負b、真正リンクe、元の境界対zで m_F(z,j)=−P_z u_j(z)、A_F(z)²=P_z² A_U(z)²、W_F(z)=P_z² W_U(z) が恒等的に成立することをLean4で形式証明。Perron正因子は**局所比では相殺**されますが、元の外側Haar平均から消してはいけません。
- 元の pair-Haar平均について 4S=∫P_z² A_U(z)² dν_H、Wbar=∫P_z² W_U(z)dν_H、Vbar=∫P_z² Var_Haar(U_z)dν_H を厳密に証明。元の ACO GI二乗軌道margin も q_GI(z)=P_z²[κ(b)A_U(z)²−ρ(b)W_U(z)]、M_GI=∫q_GI dν_H の全因子を保持しています。
- b>0 の厳密な正平均GI証明書判定は (exp(64b)−1)²∫P_z² W_U dν_H <16∫P_z² A_U² dν_H と必要十分。さらにACOの無条件same-context相対残差配置の存在を元transfer側で証明。正平均閾値が実際に成立**するならば**、真正二posterior GI応答の非零なOPEN正Haar質量集合が存在します。
- 重要：この**厳格な重み付き不等式自体の元Wilson模型での成立は未証明**です。均一なfour-mode dominance、外側重みの除去、独立Haar代用品、真GIの無条件正値、質量ギャップ解決は主張していません。

### exact-source CIと形式証明の保全

- 定理PR #6085: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6085 — MERGED。新規Lean 1ファイル、15定理、追加371行・削除0。変更は既存Lean root/模型/workflow/pinに及びません。
- 最終source HEAD e4294ad15b7bd3361ba1acd8e8302a0dc2524f9e、実PR CI merge checkout 4929962faeec273a08e191e2b54f56326d5dfd8a、定理squash a6a40dc277df4f0b6f8c1b28a7aa1319d60b5c36 のGit treeは全て b1ccf760bb043678f4f5ef3e6fbe4fda65320070 と一致。
- exact-source CI #41255009352: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41255009352 — workflow/job/実Lean step SUCCESS、Lean 11241/11241、15/15公理出力は propext・Classical.choice・Quot.soundのみ、sorryAxなし、変更Lean warning/error 0/0。
- マージ後push CI #41255418655: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41255418655 （独立のworkflow/job/Lean step結果を別途確認）。
- 独立マージ後push完了receipt：run #41255418655（head=a6a40dc277df4f0b6f8c1b28a7aa1319d60b5c36）、workflow/job/実Lean stepがいずれもSUCCESS、Lean 11241/11241、ACQ 15/15公理が標準3公理のみ、sorryAxなし、変更Lean warning/error 0/0。
- Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6 を厳守。

### 次のACRへのOPEN義務

元の更新後Perron/transfer section U_z(g) の第一四成分信号と高次直交残差の**真の重み付き比**を、元の境界条件・相互作用posteriorとともに直接評価すること。S>0、W_U≥0、既存FC上界だけからstrict positive mean GIを推論できません。体積一様GI二乗モーメント下界、共通support cylinder、遠方相殺、全物理Hilbert coercivity、共通positive-fine区間、同じendpoint E/F、H1–H4、OS/Wightman再構成と4D連続体Yang–Mills質量ギャップはOPENのままです。

---

## 検証済み定理 — ACP（2026-11-01 JST）

唯一のLean定理正本は formal/real-hilbert-uniform-coercive-strong-limit です。default mainはREADME・ROADMAPの文書ミラーであり定理正本ではありません。最新の定理は P4-Q2-PZ37ACP／PR #6082（MERGED）、squash SHA 40c85513fcd453166ba51fc02af440827ce2114f。既存ACO、ACK、ACL、ACM、ACN、各no-goを保持し、append-only／tighten-only／same-rootを継続しています。

### ACPで形式証明した厳密な元GI平均予算の符号閾値

元の相互作用Wilson SU(2)模型、中心化Gauss-law物理源、FF受信器、真正Perron代表・transfer norm、二つの相互作用posterior、元の境界データと外側pair-Haar測度を一切置換しません。ACKの真正四成分分解 Vbar=16S+Wbar と ACOの元GI平均二乗margin M_GI=4κS−ρWbarを使用しています。ここで S=∫C²dν_H>0 (b>0)、Wbar≥0、κ(b)=(2b exp(−32b))²、ρ(b)=b²(exp(32b)−exp(−32b))²/4。

- 全bに対して 16ρ(b)=κ(b)(exp(64b)−1)² が厳密に成立。従って 16M_GI=κ(b)[64S−(exp(64b)−1)²Wbar]。b=0ではM_GI=0。
- b>0に対し、M_GI>0 ⇔ (exp(64b)−1)²Wbar<64S ⇔ (exp(64b)−1)²Vbar<[64+16(exp(64b)−1)²]S。さらに一般の分散表現 M_GI=(4κ+16ρ)S−ρVbar の正値／非正値判定を厳密に証明しました。
- 不等式が逆向きなら ACOの**平均GI証明書**は非正です。ただしこれは真正二posterior GI応答がゼロというno-goではなく、正の平均予算を経由する十分条件の阻害です。
- 上記の厳密な元分散閾値が実際に成立する場合のみ、ACMの真正SU(2)軌道証明書が正になり、元の外側pair-Haar測度で正質量のOPEN集合上、真正二posterior GI応答が非零となります。閾値自体の元物理模型での正値成立は依然としてOPENです。

### exact-sourceで検証したLean4定理と保全

- PR #6082: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6082 — MERGED。新規Lean 1ファイル、14定理（公理表示14件）、追加273行・削除0。既存Lean、workflow、pin、定理rootは変更なし。
- source HEAD c6d734239bbd780d2b9a61c618b1505511d053fe、実CI checkout dd191e3fc96662e7733677ded431b5144dbd3972、定理squash SHA 40c85513fcd453166ba51fc02af440827ce2114f のGit treeは全て 604cd9bccafc21dcba62a783d198a308eb6af4dd と一致。
- exact-source CI #41253444390: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41253444390 — workflow・Lean step SUCCESS、Lean 11,240/11,240、全14/14定理が propext・Classical.choice・Quot.sound の標準3公理のみ、sorryAxなし、変更Lean warning/error 0/0。既存依存ファイルの過去warningは非fatalで保持。
- マージ後push CI #41253828302: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41253828302 （source CIとは別に確認する独立run）。
- マージ後push CIの独立完了receipt: workflow/job/実Lean stepいずれもSUCCESS、Lean 11,240/11,240、ACPの14/14公理監査はpropext・Classical.choice・Quot.soundのみ、sorryAxなし、変更Lean warning/error 0/0（run head=定理squash 40c85513fcd453166ba51fc02af440827ce2114f）。
- Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6 を維持。

### 次の実物理評価（OPEN）

ACOの正平均GIを無条件に確立するには、元の受信器の四成分Haarエネルギー割合を元posterior・Perron・境界データから直接評価し、上記の厳格閾値を実際に満たすか否かを示す必要があります。単にS>0、Wbar≥0、Vbar=16S+WbarだけからはM_GI>0を導けません。体積一様GI二乗モーメント下界、共通support cylinder、遠方相殺、全Hilbert coercivity、共通positive-fine区間、同じendpoint E/F、H1–H4、OS/Wightman再構成、連続体4D Yang–Mills存在と質量ギャップは引き続きOPENです。

---

## 検証済み定理 — ACO（2026-11-01 JST）

唯一のLean定理正本は formal/real-hilbert-uniform-coercive-strong-limit。mainは文書ミラーであり、定理正本ではありません。最新の定理は P4-Q2-PZ37ACO／PR #6079／squash 7dc0737f363ad82686111a5db96bf0663adad1d8（MERGED）です。前段ACN／#6076を維持し、新規14定理（一般3・元物理11）を元の相互作用Wilson SU(2)模型のまま追加しました。

### ACOで無条件にLean証明した範囲

元の中心化Gauss-law物理源、FF符号付き受信器、元のPerron代表と物理transfer norm、二つの真正相互作用posterior、元の外側pair-Haar測度 ν_H、ACK/ACM/ACNの四成分分解とすべてのno-goを保持。全有限H（H=0を含む）、b>0、全真正リンクeで、S=∫ C(z)^2 dν_H>0、A(z)^2=∑_{j=0}^3 m_j(z)^2、W(z)=元の四成分直交残差エネルギー、Wbar=∫W(z)dν_H≥0、B=元FC物理受信器上界を用います。ACK・ACNより ∫A^2 dν_H=4S>0、A(z)^2≤B^2/4 が既に形式証明済みです。

- 任意の ε>0 について、同じ元の物理配置で Q_ε(z)=(Wbar+ε)A(z)^2−4S W(z) と定義すると、厳密な元外側Haar平均恒等式 ∫Q_ε dν_H=4S ε>0。
- 0<2(Wbar+ε)(B^2/4)−4S ε を証明し、元の高相対margin集合の定量的Haar下界 ν_H{z: Q_ε(z)>2S ε} ≥ (4S ε)/[2(Wbar+ε)(B^2/4)−4S ε]>0 を証明。
- この選択集合は元の外側配置トポロジーでOPEN。したがって、同一の真正物理配置 z において A(z)>0 および 4S W(z)<(Wbar+ε)A(z)^2 を同時に満たすことを無条件で証明。GI正値閾値や一様量は一切仮定していません。
- 一般定理 CompactPositiveMeanRelativeResidual.adjustedMargin_continuous / adjustedMargin_integral / adjustedMargin_half_mean_tail は、任意のコンパクト確率空間の連続信号 u、連続非負残差 v、実上限 u≤R と U=∫u>0 から、V=∫v、Q=(V+ε)u−Uv に対し ∫Q=εU>0、Q≤(V+ε)R と ν{Q>εU/2}≥εU/[2(V+ε)R−εU]>0 を証明。独立性、atom-free、架空の配置や体積一様性を使用しません。

### 元GIの厳密な平均予算 — 条件付き橋渡しとOPEN境界

ACMの元のGI証明書で κ(b)=(2 b exp(-32 b))^2、ACIの真正two-posterior error envelopeを ρ(b) と置きます。元のGI二乗軌道margin q_GI(z)=κ(b)A(z)^2−ρ(b)W(z) は連続で、次の平均等式が無条件にLean証明されました。

  M_GI(H,b,e) = ∫q_GI(z)dν_H(z) = 4S κ(b)−ρ(b)Wbar.

さらに元物理FC上界 q_GI(z)≤κ(b)B^2/4 を証明。もし M_GI>0 なら、2κ B^2/4−M_GI>0 と ν_H{q_GI>M_GI/2}≥M_GI/[2κ B^2/4−M_GI]>0、真正SU(2)軌道上の正のACM certificate、および開集合 U（ν_H(U)>0、各w∈Uで |original two-posterior GI(w)|>0）が成立することをLean4で証明しました。この含意は正確ですが、**実Wilson模型で M_GI>0 自体が成立することは未証明です**。これを暗黙の物理仮定や検証済み結論に置き換えていません。

### exact-sourceとマージ後CIの確定receipt

- 定理PR #6079: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6079 — MERGED。
- 定理squash: 7dc0737f363ad82686111a5db96bf0663adad1d8。
- exact-source HEAD: 66b5a03e919e8e0c58a2241d71bb96da70d6a3b6。
- actual source CI checkout: ce18d7d9fc97ad1837fbd5053497003355a4203b。
- source／checkout／squashの共通Git tree: a07560f6397fac1bc2ea90c7a56ca4b5c4c97c93。
- exact-source CI #41245182721: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41245182721 — workflow/job/実Lean step completed SUCCESS。独立source completion receipt job 124668123060 SUCCESS。
- postmerge push CI #41245618767: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41245618767 — workflow/job/実Lean step completed SUCCESS。独立push completion receipt job 124669300972 SUCCESS。
- 両CIとも Lean 11,239/11,239 SUCCESS、新規14/14定理の #print axioms は propext・Classical.choice・Quot.sound のみ、sorryAxなし、変更Lean warning/error 0/0。
- Lean追加は新規2ファイルのみ（510行、削除0）。既存Lean、模型、定理root、workflows、Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6 を変更していません。初回の結合順序、宣言文法、物理積分定義展開の失敗は証明記法のみ修正済みで、数学的前提を弱めていません。

### 次の研究課題 — ACP（OPEN）

まず真正物理量 M_GI=4S κ(b)−ρ(b)Wbar の符号を、同じ受信器・posterior・Perron・境界データから追加仮定なしで評価する必要があります。別表現 Wbar=Vbar−16S（ACKの分散配分）から、M_GI=(4κ+16ρ)S−ρ Vbar に整理できますが、その厳格正値性は未証明です。体積一様original GI二乗モーメント正下界、共通support cylinder、遠方相殺、全物理Hilbert coercivity、共通positive-fine区間、同じendpoint E/F、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills存在と質量ギャップも引き続きOPEN。ABS・ABM・PZ37ZA・ACC・ACG・ACK・ACL・ACM・ACNの阻害定理を維持し、旧正本に対しappend-only／tighten-onlyを続けます。

---

## 検証済み定理 — ACN（2026-11-01 JST）

唯一のLean定理正本は formal/real-hilbert-uniform-coercive-strong-limit。main は文書ミラーであり、定理正本ではありません。最新の定理証明は P4-Q2-PZ37ACN／PR #6076／squash 12caee4dab07368a717aa1adc753155e91be91ae です。2026-11-01のACNは元の相互作用Wilson SU(2)模型と元の外側pair-Haarを変更せず、四成分振幅の定量的Haar評価を追加しました。

### ACNでLean4により確定した範囲

元の中心化Gauss-law物理源・真正FF受信器・正Perron代表・物理transfer norm・二つの相互作用posteriorをすべて維持します。全有限H（H=0を含む）、b>0、全真正リンクeにおいて、ACJの元共分散二乗モーメント S = ∫ C(z)^2 dν_H(z) > 0 を用います。ACKの四成分 m_j とACMの元SU(2)軌道最大振幅 A(z)^2 = ∑_{j=0}^3 m_j(z)^2 について、以下を証明しました。

- 元外側Haarにおける厳密な振幅二乗平均： ∫ A(z)^2 dν_H(z) = 4 S > 0。
- 元FC受信器上界 B による全配置上界： A(z)^2 ≤ B^2/4。Bは元のtransfer norm・物理源ノルムを保持します。
- 分母の厳密正値性： 0 < B^2/2 - 4 S。高振幅集合の実Haar質量は ν_H{z : A(z)^2 > 2 S} ≥ 4 S/(B^2/2 - 4 S) = 8 S/(B^2 - 8 S) > 0。
- よって、仮定ではない真正配置 z で A(z)^2 > 2 S が存在します。
- ACMの同じ真正SU(2)軌道の共同最適化 C=A、D=W、および V=4 A^2+W、V≤B^2 を使い、開集合 {w : sqrt(2 S) < C(w), D(w) < B^2-8 S} が元外側Haarで正の質量を持つことを証明しました。
- 一般化補題 CompactPositiveMomentTail.half_mean_upper_tail は、コンパクト確率空間の連続実関数 f に対する M=∫f>0、全配置 f≤R から、0<2R-M と M/(2R-M)≤ν{f>M/2} を証明します。独立性、atom-free、未証明の一様性を仮定していません。

ACJの選択共分散閾値 sqrt(S/2)、残差上界 B^2-2S と比較して、ACNでは同じ元配置領域に対し sqrt(2S)、B^2-8S を実現します。これは実際の振幅集合の定量的質量下界と、共分散・残差の同時選択集合の正質量（後者は定量的一様下界をまだ持たない）を区別した成果です。

### exact-sourceとマージ後の独立検証

- 定理PR: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6076 — MERGED。
- 正本定理squash: 12caee4dab07368a717aa1adc753155e91be91ae。
- exact-source HEAD: 7742e6596ca8b00d6022773321668c9709983270。
- 実source CI checkout: 89cbd2e841383b0fdefaefed35254df6d2032834。
- source／checkout／squash共通Git tree: 62e02e66153803a9bf9458684a33715444348c2f。
- exact-source CI: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41240999298 — workflow、build job、実Lean step completed/SUCCESS。独立source receipt job 124655837296 SUCCESS。
- マージ後push CI: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41241453102 — workflow、build job、実Lean step completed/SUCCESS。独立push receipt job 124657175508 SUCCESS。
- 両CIで Lean 11,237/11,237 SUCCESS、新規公開8定理／8公理出力、propext・Classical.choice・Quot.sound のみ。sorryAxなし。変更Lean warning/error 0/0。
- 追加したのはLean 2ファイルのみ（302行、削除0）。既存のLean、元物理模型、root、workflow、Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6 は不変です。
- 初回CIの測度型推論、2回目CIの定数積分簡約を修正し、最終sourceで全8定理がkernel検証に合格しました。定理の主張、物理的前提、元の境界データは弱めていません。

### 次の研究課題 — ACO（未証明）

同じ元物理配置における A と四成分残差 W の比・共分散二乗モーメントの定量的制御を続けます。ACMの真正GI下界評価式が正になるための W(z) ρ(b) < (2 b exp(-32 b) A(z))^2 が実Wilson模型で成立することは、ACNでも未証明です。正質量は有限Hごとのもので、体積一様なGI二乗モーメント正下界、固定support cylinder、遠方相殺、全物理Hilbert coercivity、共通positive-fine区間、同一endpoint E/F、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills存在・質量ギャップもOPENです。ACK・ACL・ACMおよびABS・ABM・PZ37ZA・ACC・ACGのno-goをすべて保持します。

---

> `main` は文書ミラーです。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit` です。

## 検証済み定理 — ACM（2026-10-31 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACM #6073](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6073) は、元の相互作用Wilson SU(2)模型、中心化Gauss-law物理源、真正FF受信器、正Perron代表、物理transfer norm、二つの相互作用posterior、元の外側pair-Haarを保持する。

### 1. 四成分から真正SU(2)軌道の最大共分散を厳密に構成

同じ受信器について `C(z)=Cov_Haar(F_z,E)`、`V(z)=Var_Haar(F_z)`、`D(z)=V(z)-4*C(z)^2` と書く。ACKの四成分を `m_j(z)`、実際の四成分残差二乗積分を `W(z)` とし、

```text
A(z) = sqrt(sum_{j : Fin 4} m_j(z)^2)
V(z) = 4*A(z)^2 + W(z),    W(z) >= 0
```

を用いる。全有限H（H=0を含む）・b>=0・全真正リンクe・全元配置zで成立する。一般的な非零共分散や残差小性を新たな物理仮定にはしない。

実際の2×2複素行列から、任意の実単位四成分に対応する元SU(2)元を構成し、ユニタリ性と行列式1を証明した。ACKの四成分 `phi_j` に対して、

```text
chi(a*g) = sum_j phi_j(a^-1)*phi_j(g)
C(Gamma_a z) = -sum_j m_j(z)*phi_j(a^-1)
max_a |C(Gamma_a z)| = A(z)                 (実際に達成)
```

を得る。零振幅の場合も扱う。抽象的な四成分球面の上限だけでなく、元SU(2)の真正ゲージ変換で達成する。

### 2. 共分散・回帰残差の軌道上の値域全体

ACLの真正連続center pathを最適化元から動かし、中間値の定理で全区間を埋める。

```text
range_a C(Gamma_a z) = [-A(z), A(z)]
range_a D(Gamma_a z) = [W(z), V(z)]
```

同じ真正ゲージ変換 `a*` で `C(Gamma_a* z)=A(z)` と `D(Gamma_a* z)=W(z)` を同時に達成する。したがって、ゲージ軌道内で除去可能なscalar回帰残差と、ACKの四成分を除いても残る実残差Wとを厳密に分離できる。

### 3. 同じ元配置領域で共分散と残差を制御

任意の実c,dで `c<A(z)`、`W(z)<d` ならば、

```text
{w | c < C(w) and D(w) < d}
```

は開集合であり、元の外側pair-Haarの正の質量を持つ。共同最適化された元配置 `Gamma_(a*) z` がこの同じ集合に属することから証明する。b>0ではACIから各真正リンクに正振幅配置zの存在を導き、全epsilon>0について `C(w)>A(z)/2` と `D(w)<W(z)+epsilon` を同じ正質量開集合で実現する。

正の質量は厳密不等式で定めた元配置空間の開集合に対するもの。軌道自身や正確な極値のlevel setの測度、epsilon共通の正質量、体積一様な振幅・質量は主張しない。

### 4. 真正GI絶対値の下界評価式の最適値と正値性の必要十分条件

ACIの既存のposterior残差上界

```text
rho(b) = (b^2/4)*(exp(32*b)-exp(-32*b))^2
```

を保持し、元のGI絶対値に対して

```text
L(z) = 2*b*exp(-32*b)*|C(z)| - sqrt(D(z)*rho(b))
L(z) <= |GI(z)|
```

を無条件に証明した。元のposterior係数は変換後の同じ第二境界で評価しており、posteriorのanchorを置換しない。

この評価式は真正ゲージ軌道上で

```text
max_a L(Gamma_a z)
  = Lstar(z)
  = 2*b*exp(-32*b)*A(z) - sqrt(W(z)*rho(b))
```

を実際に達成する。よって、

```text
(exists a, 0 < L(Gamma_a z))
  iff W(z)*rho(b) < (2*b*exp(-32*b)*A(z))^2
```

が成立する。b=0でLstar=0、A=0でLstar<=0も明示した。これは**このGI下界評価式の正値性**の必要十分条件であり、GI自体が非零であることの必要十分条件ではない。実際の物理配置で右辺の厳格不等式が成立することは未証明である。

### 5. exact-source検証と保存

| 項目 | 確定結果 |
| --- | --- |
| 定理PR | [#6073](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6073) — MERGED |
| exact-source HEAD | `29478dcaa5fa632dc4e7d65145a93241e84d42a3` |
| 実CI checkout | `d4aaeef3b23fd5a73e9427f73eff33ebfab5b448` |
| 定理squash | `aece46412a07084b28389e862ed1e065a28d7b05` |
| source／checkout／squash共通tree | `e8c0e9abf94e273f345def4d6520478d504cb039` |
| exact-source CI | [41210066023](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41210066023) — completed / success |
| 独立source receipt | [124564080061](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41210066023/job/124564080061) — success |
| マージ後push CI | [41210529629](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41210529629) — completed / success |
| 独立push receipt | [124565478045](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41210529629/job/124565478045) — success |
| Lean検証 | 11235 / 11235 SUCCESS（source／push） |
| 公開定理／公理出力 | 32 / 32、propext・Classical.choice・Quot.soundのみ |
| sorryAx／変更Lean warning／error | なし / 0 / 0 |
| 変更 | 新規Lean4ファイル、778行追加、削除0 |
| 既存保存 | 8,763個の既存blobをpath・modeを含めすべて保存 |
| Lean／mathlib | v4.30.0-rc2 / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

新規全文、imports、dependent signatures、固定mathlib API、実Lean elaboration、公理依存、source identity、completedログを確認。既存Lean、root、workflow、依存固定は変更しない。文書更新ではStrict Leanを再実行しない。

### 6. 次段階 — ACN（未証明）

ACMが与えた**同じ実配置のAとW**について、`W*rho < (2*b*exp(-32*b)*A)^2` を実Wilson模型で成立させる定量評価を研究する。Aの正値性のみからこの厳格不等式へ進むことはできない。

体積一様な元GI二乗モーメント下界、固定support cylinder、遠方相殺、全物理Hilbert coercivity、共通positive-fine区間、同一endpoint E/F、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills存在・質量ギャップは引き続きOPEN。ABS・ABM・PZ37ZA・ACC・ACGのno-go、ACK厳密分解、ACLの全配置／a.e.上界障害を保持する。

_以下のACL以前の「最新」表現は各PR時点の履歴スナップショット。現在の検証済みfrontierは上記ACM。_

> このmainは文書ミラー。唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。以下はACL定理PR #6070の正本検証記録の同期である。

## 検証済み定理 — ACL（2026-10-31 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACL #6070](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6070) は、元の中心化Gauss-law物理源、真正FF受信器、Perron代表、transfer norm、二つの相互作用Wilson posterior、元の外側pair-Haarを保持する。

### 1. 真正連続SU(2)軌道で共分散ゼロと正分散を両立

同じ受信器について `C(z)=Cov_Haar(F_z,E)`、`V(z)=Var_Haar(F_z)`、`D(z)=V(z)-4*C(z)^2` と書く。H=0を含む全有限H・b>0・全真正リンクeが対象であり、正の共分散配置を新しい仮定にはしない。

ACIの既存定理から `C(z_plus)>0` の実在配置を取り、`4*C(z_plus)^2<=V(z_plus)` により正分散を得る。既存の真正回転族
`a(t)=[[cos(t),-sin(t)],[sin(t),cos(t)]]` は連続で、`a(0)=1`、`a(pi)=centralMinusOne`。
ACKの同時source頂点ゲージ作用を両外側境界に施すと、

```text
h(t) = C(Gamma_(a(t)) z_plus) is continuous,
h(0) = C(z_plus) > 0, h(pi) = -C(z_plus) < 0,
V(Gamma_(a(t)) z_plus) = V(z_plus) > 0.
```

ACCのcenter符号反転と中間値の定理から、実際の `t_* in [0,pi]` と `z_0=Gamma_(a(t_*)) z_plus` を得る：

```text
C(z_0)=0, V(z_0)>0, D(z_0)=V(z_0)>0.
```

元の物理源・受信器を代替せず、同じゲージ軌道で共分散だけをゼロにし、元の正分散を保存する。

### 2. 任意の有限共分散二乗capは正質量の開領域で破れる

任意の実数Kに対し、元の外側pair-Haarを `nu_H` として、

```text
U_K = {z | K*C(z)^2 < D(z)},
U_K is open, nu_H(U_K)>0,
not (forall z, D(z)<=K*C(z)^2),
not (almost every z under nu_H, D(z)<=K*C(z)^2).
```

がACLの結論となる。Kの符号・大きさに制限はなく、固定したH・b>0・eに対してさえ、そのような有限Kは存在しない。ACKの `K<12` という障害を全有限Kへ拡張する。

正質量はCとVの連続性、上の実在証人、元pair-Haarの非空開集合に対する正値性から導く。`C=0` 集合自体のHaar質量は評価していない。正質量を持つのは厳密違反の開集合であり、非零共分散の配置も含み得る。

### 3. 分散capの鋭い係数は1

元の共分散二乗評価から、全有限H・b>=0・全リンク・全配置で `0<=D(z)<=V(z)`。
一方、b>0では任意の `theta<1` に対し、

```text
W_theta = {z | theta*V(z)<D(z)},
W_theta is open, nu_H(W_theta)>0,
not (forall z, D(z)<=theta*V(z)),
not (almost every z under nu_H, D(z)<=theta*V(z)).
```

従って全配置またはほとんど至る所に共通する分散capの係数1は最良であり、ACKの `theta<3/4` から厳格化される。選んだ配置領域に限定した評価を否定する結論ではない。

### 4. 一つの証人から全Kの違反と正の局所振幅を得る

H・b>0・eを固定すると、Kを選ぶ前に一つの `z_0` を取り、

```text
C(z_0)=0, V(z_0)>0,
forall K in R,
  nu_H({z | V(z_0)/2<V(z) and K*C(z)^2<D(z)})>0.
```

同じ正の半分散振幅を全Kで保持するが、違反集合はKに依存する。全K共通の正質量、質量の数値的下界、H・b・リンクに一様な正質量や振幅は得ていない。ゼロ共分散点での除算には依存しない。

### 5. 検証記録

| 項目 | 確定値 |
| --- | --- |
| 定理PR | [#6070](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6070) — MERGED |
| 定理squash | `9d8eed5a59c8b9eba5c093cf1d1008619d1701c8` |
| exact-source HEAD | `c82fd8de685af3fc26c4a13423fbe017aa80eea1` |
| 実CI checkout | `bf986355ff8a939513e8acdba2e6a42ef22e8bf3` |
| source・checkout・squash共通Git tree | `9feda32dc1ebe46024171c37b08c325f8f52e0b0` |
| exact-source CI | [#41206293933](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41206293933) — SUCCESS |
| 独立source receipt | [#124553198555](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41206293933/job/124553198555) — SUCCESS |
| マージ後push CI | [#41206896250](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41206896250) — SUCCESS |
| 独立push receipt | [#124555009386](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41206896250/job/124555009386) — SUCCESS |
| Lean検証 | source・マージ後とも 11,231 / 11,231 SUCCESS |
| 新規Lean・公開定理 | 3ファイル、547行追加、削除0、29定理 |
| 公理依存 | 全29定理とも propext・Classical.choice・Quot.sound のみ。sorryAxなし |
| 変更Lean warning / error | source・マージ後とも 0 / 0 |
| Lean / mathlib | v4.30.0-rc2 / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

workflow・job・実Lean stepのcompleted/success、全29件の公理出力、独立completion receipt、source/checkout/squash tree一致を完了ログで確認した。一般連続関数補題12定理、真正center経路3定理、元物理受信器への適用14定理を含む。新規3ファイルの全文・imports・依存署名・固定mathlib APIを独立レビューし、初回exact-source CIとマージ後CIの両方で検証した。定理PRでは既存8,760個のblobとそのpath/modeを保存し、旧Lean・root・workflow・依存固定は一切変更していない。

### 6. 次段階 ACM（未証明）

真正SU(2)ゲージ軌道の選択領域で、元受信器の共分散振幅と源残差を同時に解析する。ACKの四成分から同じ軌道上の共分散の最大振幅を厳密に表示できるかも検討対象だが、この段階では未証明である。

同じ元配置域で `-C>=c>0`、`D<=d` と正の元pair-Haar質量を揃え、`rho(b)=b^2*(exp(32b)-exp(-32b))^2/4` に対するGI正値の十分条件 `2*b*exp(-32b)*c>sqrt(d*rho(b))` の実成立を調べる。ACLが排除した全配置／a.e.の有限capを次段階の前提にせず、選択領域の評価を元定義から構成する。

固定b>0または `0<b0<=b(H)<=B0` における共分散二乗モーメントS・真正GI二乗モーメントの体積一様正下界、同一配置域の一様質量と振幅、遠方相殺、全物理Hilbert coercivity、共通positive-fine区間、同一endpoint E/F、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills存在・質量ギャップは未解決。ABS・ABM・PZ37ZA・ACC・ACGの既存障害定理とACKの厳密分解を維持する。

以下のACK以前の「最新」「次段階」は歴史スナップショットとして保存する。ACK節の「ACL（未証明）」や全有限Kについての留保は、当時の到達点を記録したものである。この節だけを先頭に追加し、旧本文はバイト単位で保存する。

---

> このmainは文書ミラー。唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。以下はACK定理PR #6067の正本検証記録の同期である。

## 検証済み定理 — ACK（2026-10-31 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACK #6067](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6067) は、元の中心化Gauss-law物理源、真正FF受信器、Perron代表、transfer norm、二つの相互作用Wilson posteriorと元の外側pair-Haarを保持したまま、SU(2)四成分と残差の厳密な配分を証明した。

### 1. 真正SU(2)の四つのHaar直交実成分

元の実Wilson characterを `chi(g)=1-E(g)`、元の四元数族を `q_j=(1,J,K,L)` とし、`phi_j(g)=chi(q_j*g)` を定義。有限群平均へ置換せず、元の正規化compact SU(2) Haarに対し、

```text
integral phi_j = 0,
integral phi_i*phi_j = delta_ij/4,
sum_j phi_j(g)^2 = 1
```

を証明した。任意の連続実関数Fに対する有限四分の一Gram射影を一般補題として構成し、元の物理受信器 `F_z` に適用する：

```text
m_j(z) = integral F_z(g)*phi_j(g),
P_z(g) = 4*sum_j m_j(z)*phi_j(g),
R_z(g) = F_z(g) - integral F_z - P_z(g).
integral R_z = 0, integral R_z*phi_j = 0,
W_z := integral R_z^2 = Var(F_z) - 4*sum_j m_j(z)^2 >= 0.
```

引く平均は同じリンクHaar上の実際の平均であり、元物理源の空間Haar中心化とは区別している。

### 2. 任意SU(2)ゲージ値に対する元受信器の輸送

選んだ真正リンクeのsource頂点に任意の `a:SU(2)` を置き、両外側境界へ同じ格子ゲージを施す `Gamma_a` を構成。H=0を含む全有限Hで、joint continuity、元pair-Haarの保存、恒等変換、元ACCのcenter変換との一致、および

```text
F_(Gamma_a z)(g) = F_z(a^(-1)*g),
mean(F_(Gamma_a z)) = mean(F_z),
Var(F_(Gamma_a z)) = Var(F_z),
C(Gamma_a z) = -integral F_z(g)*chi(a*g),
m_j(z) = -C(Gamma_(q_j) z)
```

を証明した。元のprefactorとPerron半密度は保持する。固定posterior anchorの輸送やGI自体の符号反転は主張しない。ACCの `C(Gamma_center z)=-C(z)` と `D_F(Gamma_center z)=D_F(z)` は維持される。

### 3. 同じ元外側Haarにおける正確な分散・残差配分

ACJの実積分 `S=integral_outer C^2` をそのまま用いる。各jのゲージ変換が同じ元外側測度を保存するため、`integral_outer m_j^2=S` が全四成分で成立する。実際の非負量 `W=integral_outer W_z` により、

```text
Vbar := integral_outer Var(F_z) = 16*S + W,
Dbar := integral_outer (Var(F_z)-4*C(z)^2) = 12*S + W,
W >= 0.
```

を証明した。全有限H・b>0・全真正リンクeでACJの `S>0` が使えるので、

```text
Dbar >= 12*S > 0,
Dbar >= (3/4)*Vbar,
0 < S <= B^2/16,
B = norm(T)^(-1)*(exp(8*b)^3-1)*norm(f0)
```

が成立。元FC上界を保持したまま、ACJの `S<=B^2/4` を四倍厳格化した。ACJの数値分散評価と同じ元源のノルム評価を代入すると、

```text
S <= 36*b^2*exp((2*A_H+48)*b)*norm(f0)^2
  <= 216*P_H*b^2*exp((2*A_H+48)*b).
```

作用予算A_H・真正プラケット数P_Hの体積依存は明示したまま。これらは上界であり、Sの数値的正下界や体積一様な正下界を与えるものではない。

### 4. 元物理受信器についての新しい残差障害

同じ固定H・b>0・eにおいて、`D_F<=theta*C^2` が全配置、または元の外側pair-Haarでほとんど至る所成立することは、`theta<12` なら不可能。同様に `D_F<=theta*Var(F_z)` は `theta<3/4` なら不可能。これは元物理源・元Haarからの無条件の結論であり、選んだ好条件領域での評価を否定しない。任意の有限Kに対する不可能性は今回証明していない。

### 5. 検証記録

| 項目 | 確定値 |
| --- | --- |
| 定理PR | [#6067](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6067) — MERGED |
| 定理squash | `d26e285dc81061f39f4a8de7b9c19cef3e62527f` |
| exact-source HEAD | `b998b94815761849b7d0ead7338842f14ee8aa43` |
| 実CI checkout | `8416e2ec9eefcf7dc2268320fb1fa3aa6912f0a3` |
| 三者共通Git tree | `c6ce20cdeee8253bcd4209a9a38785189e9f6174` |
| exact-source CI | [#41203213018](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41203213018) — SUCCESS |
| マージ後CI | [#41203671530](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41203671530) — SUCCESS |
| 独立source receipt | [#124543920340](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41203213018/job/124543920340) — SUCCESS |
| 独立push receipt | [#124545380755](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41203671530/job/124545380755) — SUCCESS |
| Lean検証 | 11,228 / 11,228 SUCCESS |
| 新規Lean・公開定理 | 4ファイル、1,200行追加、削除0、49定理 |
| 公理依存 | propext・Classical.choice・Quot.sound のみ。sorryAxなし |
| 変更Lean warning / error | 0 / 0 |
| Lean / mathlib | v4.30.0-rc2 / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

workflow・job・実Lean stepのcompleted/success、49件の公理出力、独立completion receipt、source/checkout/squash tree一致を確認した。変更Lean全文・imports・依存署名・固定mathlib APIを読み、積分の型推論、ゲージ連続性の定義展開、実部と条件分岐、部分型ノルムと局所基数定義のelaborationを修正した。公開49定理の仮定・結論は修正前後で不変。旧Lean、root、workflow、依存固定は一切変更していない。

### 6. 次段階 ACL（未証明）

真正連続SU(2)軌道上の共分散ゼロと正の分散の両立、または同じposterior係数を保った残差比の厳格化を調べる。候補となる代数恒等式・連続軌道の議論は、この段階では研究案である。ACJの同一領域GI正値条件の実際の成立、固定bまたは `0<b0<=b(H)<=B0` におけるSの体積一様正下界は未証明。

真正GI二乗モーメントの体積一様正下界、同一配置域の一様質量と振幅、遠方相殺、全物理Hilbert coercivity、共通positive-fine区間、同一endpoint E/F、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills存在・質量ギャップは未解決。ABS・ABM・PZ37ZA・ACC・ACGの既存障害定理を維持する。

以下のACJ以前の「最新」「次段階」は歴史スナップショットとして保存する。

---

## 検証済み定理 — ACJ（2026-10-31 JST）

文書ミラー対応：[正本README／ROADMAP同期 #6065](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6065)。

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACJ #6064](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6064) は元のWilson模型、中心化Gauss-law物理源、Perron代表、transfer norm、二posterior、真正外側pair-Haarを保持する。

### 1. 真正外側共分散モーメントと正負対称性

元の中心化物理源の同じFF受信器について `C(z)=Cov_Haar(F_z,E)`、元の外側pair-Haarを `nu_H` とし、実際の積分 `S=integral_outer C(z)^2` を定義した。ACIの各リンクでの非零共分散とACDの既存Haar開領域を使い、任意の有限H・b>0・真正リンクeで `S>0` を証明。真正center-gauge変換は同じ外側測度を保存しCの符号を反転するため、`integral_outer C=0` と任意の閾値tでの正負tail質量の一致を厳密に証明した。ゼロ平均はCの点ごとの消失を意味せず、ゼロ集合の質量は評価していない。

### 2. 同じ真正配置域で共分散・源残差・Haar質量を定量評価

元のACA/FC上界を `B=norm(T)^(-1)*(exp(8b)^3-1)*norm(f0)` とすると、`4*C(z)^2 <= Var(F_z) <= B^2` と `0<S<=B^2/4` が成立する。実際の同じSから

```text
c = sqrt(S/2), d = B^2-2*S,
Aplus = {z | c < C(z)}, Aminus = {z | C(z) < -c}
```

を構成し、

```text
c>0, d>0, S/d>0,
Aplus and Aminus are open,
nu_H(Aplus) = nu_H(Aminus) >= S/d,
on Aplus:  C >= c and 0 <= D_F <= d,
on Aminus: -C >= c and 0 <= D_F <= d,
D_F = Var(F_z)-4*C(z)^2
```

を証明した。共分散下界、源残差上界、正の外側質量が同じ元配置域で成立し、これらの正値性を新しい前提にしていない。厳密な開集合の境界が零測度だという仮定もない。定数は証明済みの正の元積分Sを含むため、SのH,bだけによる数値下界や体積一様下界を得たとは主張しない。

### 3. 元物理源の数値的残差上界とGI回帰誤差の六次上界

元の有限slab作用予算を `A_H`、真正プラケット数を `P_H` と書く。ACAの受信器上界、ABMの真正transfer逆ノルム評価、ACIのposterior残差評価から、b>0で任意の元物理源f・リンク・境界配置に対し

```text
Var(F), D_F <= 576*b^2*exp((2*A_H+48)*b)*norm(f)^2,
(GI+4*k*C)^2 <= 589824*b^6*exp((2*A_H+112)*b)*norm(f)^2.
```

同じ中心化源f0について、互換なAAI枝の証明済み `norm(f0)^2<=6*P_H` を使い、

```text
D_f0 <= 3456*P_H*b^2*exp((2*A_H+48)*b),
(GI_f0+4*k*C_f0)^2 <= 3538944*P_H*b^6*exp((2*A_H+112)*b)
```

を証明した。六次は回帰誤差の二乗に対する固定有限体積での上界。元の作用予算・プラケット数の体積依存を保持する。

### 4. 検証と次段階

追加Leanは3ファイル・683行、削除0行。公開18定理を検証。

| 項目 | 確定値 |
|---|---|
| exact-source HEAD | `a1b3abc0b0f9b65a7faf486461401e97068c8bda` |
| 実際のCI checkout | `48456fe599712544127eefd16f7a45ad802175ac` |
| ACJ theorem squash | `322bbbeb6e5d5d5730b9db6879b0506c173c0422` |
| source・checkout・squash共通Git tree | `0011f8ca48e1cbcd1a55de0e0444cce670e068e1` |
| exact-source CI | [41198364175](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41198364175) — 11,224 / 11,224 SUCCESS |
| exact-source独立receipt | [124529907827](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41198364175/job/124529907827) — SUCCESS |
| マージ後push CI | [41198757390](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41198757390) — 11,224 / 11,224 SUCCESS |
| マージ後独立receipt | [124531025560](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41198757390/job/124531025560) — SUCCESS |
| 公理依存 | 全18定理とも propext・Classical.choice・Quot.sound のみ。sorryAxなし |
| 変更Lean warning / error | source・マージ後とも 0 / 0 |

変更全文・imports・dependent signatures・固定mathlib APIを確認し、実際のLean stepと独立completion receiptの成功、Git tree一致を確認済み。既存Lean・workflow・依存固定に変更なし。

**次はACK（未証明）**：元のSU(2)ゲージ軌道で共分散と源残差がどう変わるかを解析し、同じ源の四つのHaar直交character成分と残余の分解を検討する。今回の正のSを数値的に下から評価する課題、および `rho(b)=b^2*(exp(32b)-exp(-32b))^2/4` として、負共分散領域でGI正値性の十分条件 `2*b*exp(-32b)*c > sqrt(d*rho(b))` を実際に満たすかという課題は残る。正のSの存在や六次誤差上界だけからこの閾値を推論しない。

固定正結合／正の結合区間での共分散二乗モーメントS・GI二乗モーメントの共通正下界、真正外側pair-Haarの体積一様質量・振幅・遠方相殺、全物理Hilbert coercivity、common positive-fine、同一endpoint E/F、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills mass gapは未解決。ABS・ABM・PZ37ZA・ACC・ACGの障害定理を保持。Lean v4.30.0-rc2／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。

> 以下のACI以前の「最新」「次段階」は歴史スナップショット。現行frontierはACJ。過去本文はバイト単位で保存。

---

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ACI

> このmainは文書ミラー。Lean定理の唯一の正本は `formal/real-hilbert-uniform-coercive-strong-limit`。

## 検証済み定理 — ACI（2026-10-31 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACI #6061](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6061) の新規3Leanファイルが対象。以下の定理は元のWilson模型・中心化Gauss-law物理源・Perron代表・transfer norm・二つの相互作用posterior・真正外側pair-Haarを保持する。

### 1. 真正posteriorのエネルギー直交残差を定量評価

元の `d=p0-ppi`、`Q=∫d² dHaar`、`k=-∫E*d dHaar` に対し、`L=exp(-32b)`、`U=exp(32b)` と置く。ABYの真正行列式傾きを区間の中点と比較し、同じ二つの密度の正規化と完全な反対称二重積分から

```text
Var_Haar(d + b*(U+L)*E) <= b^2*(U-L)^2/4,
0 <= Q-4*k^2
   <= (2*k-b*L)*(b*U-2*k)
   <= rho(b) := b^2*(U-L)^2/4
   <= 1024*b^4*exp(64*b)
```

を証明。すべての有限H・真正リンク・右配置・b>=0に成立する。小残差を仮定へ移さず、元積分から得た体積・リンク・右配置に依存しない明示的上界。除算して定義した傾きの連続性は使わず、連続な行列式誤差そのものを積分する。

ACHの同じ物理FF受信器 `F`、`C=Cov(F,E)`、`D_F=Var(F)-4*C^2` について、`(GI+4*k*C)^2 <= D_F*rho(b)` も証明。元の源残差D_Fの有効な小ささやGI正値閾値までを証明したものではない。

### 2. 元の中心化Gauss-law物理源の共分散は各リンクで非自明

同じFF/JQ受信器について `Cov(F,E)=∫JQ_receiver*(1-E)dHaar / q(z)` を厳密に証明。`q(z)>0` は元のPerron・transfer密度相殺係数であり、省略・置換しない。元のtransferが各選択リンクのidentity fiber上で非零になるOTと、真正SU(2)負指数Haar変換の単射性LA・元の左境界分解LCを接続し、

```text
forall H, b>0, actual link e,
  exists genuine boundary pair z, Cov(F_{H,b,f0,e,z},E) != 0;
  exists z_plus z_minus,
    Cov(F_{H,b,f0,e,z_plus},E) > 0 and
    Cov(F_{H,b,f0,e,z_minus},E) < 0.
```

を証明。f0は元の `p4Q2PZ37ZW_originalCenteredPhysicalDirection`。連続代表・Gauss-law不変性・非零性は既存のAAU2/OV/ZWで実際に充足し、共分散の非零性を仮定していない。正負両配置はACCの真正center-gauge対称性による。これは各有限体積での存在定理であり、体積一様な非零振幅・外側pair-Haar質量・GIの符号を与える定理ではない。

### 3. 検証と次段階

| 検証対象 | 確定結果 |
|---|---|
| 定理PR | [#6061](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6061) — MERGED |
| exact-source HEAD | `c5191eaa5fd9b08669ab1cd05ebe0cc3b2dbe97a` |
| CI checkout | `ba4d05b270ac0bbb5b9c66bd823451f0974ba2de` |
| 定理squash | `932ebe169bca58d1afab73270bfdd3d1deccdf22` |
| source・checkout・squash共通Git tree | `2c85570104a055a45e79870d0443363fc7f834cf` |
| exact-source CI | [#41195518486](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41195518486) — 11,202/11,202 SUCCESS |
| 独立completion receipt | [124521718419](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41195518486/job/124521718419) — SUCCESS、exact-source SHA一致 |
| マージ後push CI | [#41195944256](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41195944256) — 11,202/11,202 SUCCESS |
| マージ後独立receipt | [124522994315](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41195944256/job/124522994315) — SUCCESS、squash SHA一致 |
| 追加Lean／公開定理 | 新規3ファイル・760追加行・削除0行／16定理 |
| 公理依存 | 16/16すべて `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし |
| 変更ファイルwarning/error | exact-source・マージ後とも0/0 |

完全な変更ソース・imports・依存シグネチャ・固定mathlib API・実際のelaboration failure原因を確認し、成功した最終ソースのみをマージ。Lean/mathlib pin・既存Lean・workflow・既存仮定の変更なし。

主要ソース（上記squash固定）：

- [CompactPosteriorEnergyResidual.lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/932ebe169bca58d1afab73270bfdd3d1deccdf22/MGAP4D/MathlibAnalytic/CompactPosteriorEnergyResidual.lean)
- [PhysicalYangMillsWilsonSU2OriginalPosteriorResidualBoundV5_PZ37ACI.lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/932ebe169bca58d1afab73270bfdd3d1deccdf22/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPosteriorResidualBoundV5_PZ37ACI.lean)
- [PhysicalYangMillsWilsonSU2OriginalPhysicalEnergyCovarianceV5_PZ37ACI.lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/932ebe169bca58d1afab73270bfdd3d1deccdf22/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPhysicalEnergyCovarianceV5_PZ37ACI.lean)

**次はACJ（未証明）**：今回の実在する共分散配置と、元物理源の実際の回帰残差D_Fを同時に定量評価する。同じ元配置域で、向き `s in {1,-1}` に対する `-s*C` の正の下界、源残差D_Fの上界、正の外側pair-Haar質量を実際に構成し、`s*GI>0` の定量閾値の成否を調べる。存在だけから一様定数を取り出さない。

共通の正の元GIモーメント、固定正結合／正の結合区間での正の物理共分散振幅・GI下界の体積一様性、遠方相殺、全物理Hilbert coercivity、common positive-fine、同一endpoint E/F、H1–H4、OS/Wightman再構成、4D連続体Yang–Mills mass gapは未解決。ABS・ABM・PZ37ZA・ACC・ACGの障害定理を保持。Lean v4.30.0-rc2／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。

> 以下のACH以前の「最新」「次段階」は当時の歴史スナップショット。現行frontierはACI。過去本文はバイト単位で保存。

---

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ACH

> **main文書ミラー（ACH同期）**：文書のみの反映。定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。

## 検証済み定理 — ACG・ACH（2026-10-31 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。最新定理 [ACH #6058](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6058) はMERGED、定理squash `b609cedfc287923afed651a473d4d22238495877`、exact-source `c0fda4a7947d1c0b5d68244cbda5e156d575dd67`、実CI checkout `f1e25c4e78f566b3f608067b3e3b4d590480df1e`、三者の共通tree `670db41939647f4e18962cc774f080db4c56c9f0`。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、元Wilson模型・物理源・真Perron・転送ノルム・二つの相互作用posterior・外側pair-Haarを保持する。

### CLOSED — ACG：上限だけの結合条件に対する真正GIモーメントの障害

[ACG #6057](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6057) は元のプラケット数P_H・一スラブ作用budget A_H・E_b=exp(8b)(exp(16b)-exp(-16b))を保持して、全真正リンクで

`M(H,b,e) <= [exp(b A_H) P_H E_b/2]^2`。

固定Hの数値上界の連続性と零結合での消失から、任意の正のcap(H),epsilon(H)に対して、全リンクのMをepsilon(H)未満にする0<b(H)<=cap(H)を構成する。従って任意B>0の下で、0<b(H)<=min(B,1/(H+1))かつ全リンクM<1/(H+1)の一つの族が存在し、どのH依存リンク選択にも共通m>0がない。同じ族の各有限HでACEのM>0とACFの正のRayleigh証明書は成立する。これは固定b>0や正の下限を持つ区間の否定ではなく、Rayleighが零へ収束するという定理でもない。

### CLOSED — ACH：元posteriorのエネルギー応答の一様正下界

同じ真正SU(2) Haar、元のWilsonエネルギーE、元の二posterior密度差d=p0-ppiについて `k=-integral E*d` と置く。真の全二コピー積分、ABYの行列式傾き、Var_Haar(E)=1/4を用い、全有限H・全真正リンクe・全右配置r・b>=0で

`(b/2) exp(-32b) <= k(H,b,e,r) <= (b/2) exp(32b)`。

従って指定した0<b0<=b<=Bでは、`k >= (b0/2)exp(-32B)>0` がH・リンク・右配置によらず成立する。領域capへの制限や都合のよいtail削除を使わない。ただしこれはposteriorのエネルギー応答であり、物理源のCov(F,E)が非零だという主張ではない。

### CLOSED — ACH：真正GIの二重回帰残差評価

任意の元Gauss-law物理源の真正FF受信器Fについて `C=Cov(F,E)`、`D_F=Var(F)-4C^2`、元FX感度 `Q=integral d^2` とする。受信器と密度差の両方からエネルギー成分を除くと

`(Delta_GI+4kC)^2 <= D_F*(Q-4k^2)`、`0<=Q-4k^2`。

右辺は二つの実際の回帰残差の分散の積である。真の中心化Haar-L2でのCauchy--Schwarzと厳密共分散恒等式から証明した。D_F=0なら `Delta_GI=-4kC`。D_Fが小さいことやC!=0を新たな物理的事実として仮定しない。元のPerron因子・transfer normはFの中に保持される。

### 検証

ACG exact-source e614d1c657083e0472c06533e160694a7034c231、squash 6d83a3d0c39d8e48d6c117f4b7a3e20b33ea6fd3、[CI #41185081567](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41185081567) SUCCESS、11215成功、9公開定理標準3公理のみ、変更0 warning/0 error。マージ後[CI #41186150614](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41186150614)もbuild・Lean step・独立receipt #124494239210 completed/SUCCESS。

ACH [exact-source CI #41188053582](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41188053582) はworkflow・build・Lean step completed/SUCCESS、11197成功。新規434行・公開16定理・全16件の公理依存はpropext/Classical.choice/Quot.soundのみ、sorryAxなし、変更warning/error 0/0。独立completion receipt #124499925105は同じexact-sourceでsource_result=success。文書だけの更新は新規Lean定理ではなく、不要なLean再実行は行わない。

### OPEN — 次はACI：実残差と物理源を評価する

元の密度差のエネルギー直交残差Q-4k^2を実Wilson積分から定量化し、元中心化物理源のCとD_F、および元外側pair-Haar上での振幅・質量・遠方相殺を評価する。kの一様正値だけからCの非零性や真正GIモーメントMの一様正下界は従わない。固定正結合または正の下限を持つ明示的区間における共通m、全物理Hilbert coercivity、common positive-fine、同一endpoint E/F、H1-H4、OS/Wightman、4D連続体Yang-Mills存在・質量ギャップはOPEN。ABS・ABM・PZ37ZA・ACC・ACGの障害を保持する。

以下のACF以前の本文はバイト単位で完全保存した履歴。旧「最新・次段階・OPEN」よりこの追補を優先する。

---

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ACF

> **main文書ミラー（ACF同期）**：ここでは文書だけを反映する。Lean定理の唯一正本は `formal/real-hilbert-uniform-coercive-strong-limit`。

## 検証済み定理 — ACD・ACE・ACF（2026-10-31 JST）

**唯一のLean定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーであり、定理正本ではない。最新定理 [ACF #6054](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6054) はMERGED。定理squash `a1a7217a4d39e753792a117607db31d86d7e5891`、exact-source `2f83fdde6a2b609e2cf16f4cbc61d056564fde88`、source・checkout・squashの共通Git tree `959be2261c824cfe5092413b02da119efbe620f4`。文書だけの後続マージは新規定理ではない。

Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、元Wilson模型、Gauss-law物理源、真正Perron代表、transfer norm、二つの相互作用posterior、元外側pair-Haarを維持する。

### CLOSED / CONDITIONAL — ACD：真正共分散領域

[ACD #6052](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6052) は元受信器Fの実Haar共分散C(z)=Cov(F_z,E)、分散v(z)=Var(F_z)、ACCの絶対GI marginの連続性を証明した。実際の非零共分散証人C(z0)≠0が与えられれば、c=|C(z0)|/2、V=v(z0)+1、eta=min(1/2,2c²/V)から正の元外側pair-Haar質量を持つ開領域A={c<|C|,v<V}を構成する。領域上で0≤D_F≤(1−eta)v_F、真正PerronのP²恒等式により同じUに0≤D_U≤(1−eta)v_Uが成立する。

**非零共分散証人そのもの、およびACC正値閾値を満たす実回帰欠損は未証明。非零GIから非零エネルギー共分散を推論しない。**

### CLOSED — ACE：元GI二乗モーメントの有限体積正値性

[ACE #6053](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6053) は真正連続GIの二乗可積分性を証明し、AAZの非a.e.ゼロ性と接続した。すべての有限Hとb>0について、ある真正リンクeに対し

`M(H,b,e)=∫ Delta_GI(H,b,e,z)² d lambda_H(z)>0`

が無条件に成立する。同じ連続二乗GIの上界K=‖Delta_GI²‖+1>0から、実開領域A={M/2<Delta_GI²}について`lambda_H(A)≥M/(2K)>0`を証明した。M、K、e、領域はH,bに依存し、共通の正下界はまだ得ていない。

### CLOSED — ACF：真正FX上界を明示したRayleigh評価

現在のJL定理とその公理依存を再検証し、同じ二つの相互作用Wilson posteriorの真正FX感度に

`Q(H,b,e,right)≤q(b):=(exp(16b)−exp(−16b))²`

を適用した。この上界はH・実リンク・右側配置に依存しない。qは非負結合上で単調、b>0でq(b)>0。元の生一リンク応答Jと同じ中心化物理源のRayleigh値Rについて

`M≤q(b)J`、`M/q(b)≤J`、`(M/q(b))/18≤R_H(b)`。

ACEの証人を選ぶと各有限H,b>0で`0<(M/q(b))/18≤R_H(b)`。b=0を正の分母として使用しない。これは一つの元中心化物理源に対する評価であり、全物理Hilbert空間の一様coercivityではない。

ACDの可測領域Sで共分散下限c・分散上限Vが成立し、計算された

`delta=b(exp(32b)+exp(−32b))c−(b/2)(exp(32b)−exp(−32b))sqrt(V)`

が非負なら、独立のFX上界仮定なしに`(lambda_H(S)delta²/q(b))/18≤R_H(b)`。領域モーメントの正の一様性を追加で証明したものではない。

### CLOSED / CONDITIONAL — 体積族への接続

`0<b(H)≤B`と、真正リンクe(H)について共通の`m>0`および`M(H,b(H),e(H))≥m`が別途証明できれば

`0<m/[18(exp(16B)−exp(−16B))²]≤R_H(b(H))`（全H）

が従う。**共通mの存在はこの含意の前提であり、ACFの結論ではない。** FX上界自体はABAで独立に閉じていた。ACFは現在のJLの標準公理のみの依存を確認してACE/ACDの新しい領域評価へ接続したもので、過去のABA成果を新規に数え直さない。下の古いAAZ/JL追加公理の記述は当時の履歴である。

### exact-source検証記録

| 定理 | exact-source CI | 完了したLean検証 |
| --- | --- | --- |
| ACD #6052 | [#41178410965](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41178410965) | 11192/11192 SUCCESS |
| ACE #6053 | [#41180324447](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41180324447) | 11194/11194 SUCCESS |
| ACF #6054 | [#41182927973](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41182927973) | 11195/11195 SUCCESS |

ACFは新規Lean1ファイル216行・公開12定理。JL依存を含む公理報告は標準`propext`・`Classical.choice`・`Quot.sound`のみ、sorryAxなし、変更warning/error 0/0、独立completion receipt #124484776836 SUCCESS。ACFマージ後の[CI #41183571719](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41183571719)も、正本SHAに対するbuild #124485798525・Lean step・独立receipt #124486722205すべてcompleted/SUCCESS。これは古い依存ファイルに警告が皆無という主張ではない。

[ACD Lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/a1a7217a4d39e753792a117607db31d86d7e5891/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCovarianceRegionV5_PZ37ACD.lean) ／ [ACE Lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/a1a7217a4d39e753792a117607db31d86d7e5891/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalMomentMassRayleighV5_PZ37ACE.lean) ／ [ACF Lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/a1a7217a4d39e753792a117607db31d86d7e5891/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExplicitFXMomentRayleighV5_PZ37ACF.lean)。

### OPEN — 次段階P4-Q2-PZ37ACG

元の中心化源の真正GI二乗モーメントに体積一様な正下界を構成する。まず結合領域を明示し、上限のみの族0<b(H)≤Bと、固定b>0または0<b0≤b(H)≤Bを区別する。実Wilson積分、Perron係数、ゲージ対称性、局所変動、全遠方相殺、外側pair-Haar領域の質量と振幅を解析する。結合下限の指定だけでも一様性は証明されない。

共通m、非零エネルギー共分散証人、ACC正値閾値を満たす実欠損、全物理Hilbert coercivity、common positive-fine、同一endpoint E/F、H1–H4、OS/Wightman再構成および非自明な4D連続体Yang–Mills existence/mass gapはOPEN。ABS・ABM・PZ37ZA・ACCの既存障害を保持する。非局所Perron応答を固定supportへ置換しない。

**以下は旧本文をバイト単位で完全保存した履歴である。旧「最新・次段階・OPEN」の記述より上のACF追補を優先する。文書のみの同期ではLeanを再実行しない。**

---

> **main文書ミラー（ACC同期）**：唯一の定理正本は [formal/real-hilbert-uniform-coercive-strong-limit](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。確認済み正本HEAD `bf65a8ec672f565318a69d25f481a7e23e809ce3`（[正本文書同期 #6050](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6050)）、定理squash `e8803e0fcc69d051953d532ed246ff9467c5d616`（[ACC #6047](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6047)）。このmain更新はREADME・ROADMAPの追記だけで、以下のACC検証記録を鏡映する。

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ACC（2026-10-31 JST）

**唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACC定理 PR #6047](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6047) **MERGED**。定理squash `e8803e0fcc69d051953d532ed246ff9467c5d616` とマージ直後の正本HEADを完全一致で確認。exact-source `460d15a44e7b428a5a632f7e37e6132f9050169c`、実CI checkout `87a1db0829b27919a9aeb7d9768bc33d2e04fe46`、定理squashの全Git treeは `ef26f66ec383060030c307bcc00decd117b98942` に完全一致。既に統合されたACB [#6046](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6046) とその文書履歴を保持し、この拡張をACCとして接続した。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。

**検証：** [CI #41174163063](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41174163063) workflow・build job・Lean step **completed / SUCCESS**、Lean **11,181 / 11,181 SUCCESS**。新規4 Leanファイル・1,208行・48公開定理・48件の `#print axioms`。公理依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内、`sorryAx`なし、変更warning/error **0/0**。独立completion receipt [job #124459070461](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41174163063/job/124459070461) とpublish stepは **completed / SUCCESS**、同じexact-source SHAと `source_result=success` を確認。全文・imports・依存署名・固定APIを独立レビューし、既存Lean・元模型・仮定・公開root・workflowを変更していない。

## CLOSED — 元の全GIを実共分散と実分散で直接評価

元のFF受信器について、真正SU(2) Haar μに対し `v_z=Var_μ(F_z)`、`σ_z=sqrt(v_z)`、`C_z=Cov_μ(F_z,E)`、`D_z=v_z-4*C_z²≥0` とする。`Var_μ(E)=1/4` は既証の元Haar恒等式。`u=exp(32b)`、`l=exp(-32b)` と置くと、全有限H、b≥0、元の任意Gauss-law物理源、s²=1について、

`-b*(u+l)*s*C_z-(b/2)*(u-l)*σ_z ≤ s*Δ_GI(z) ≤ -b*(u+l)*s*C_z+(b/2)*(u-l)*σ_z`、

従って

`|Δ_GI(z)+b*(u+l)*C_z| ≤ (b/2)*(u-l)*σ_z`

を証明した。ABYの完全な正負tail比較、ABZの厳密な `M_s-M_{-s}=-4bsC_z`、ACAの全不整合上界を使う。内側長方形、小tail、特定の受信器profileは仮定しない。元の二つの相互作用posteriorと全負寄与を保持し、正寄与の上界を下界として代入していない。

下界を `L_s(z)=-b*(u+l)*s*C_z-(b/2)*(u-l)*σ_z` とする。同じABX rectangle Rの外側領域で、s=R.signとすると、同じ最適不整合上界B_sを使うACAのrectangle marginはL_s以下。元FF/FCの `K=‖T‖⁻¹*((exp(8b))³-1)*‖f‖` によるσ_z≤Kを用いた誤差上界も証明し、真のtransfer normとそのH依存を保持した。

## CLOSED / CONDITIONAL — 実回帰欠損による全tail上界と正値証明条件

`B_s=b*(σ_z+2sC_z)` について `B_s*B_{-s}=b²D_z` を証明。望ましい共分散方向sC_z≤0なら、元の全不整合は

`M_{-s}(z)≤b*sqrt(D_z)`、

元posteriorの全負tailは `exp(32b)*b*sqrt(D_z)` 以下。一般解析葉では分母非零を明示した欠損の商表示、閾値の必要十分条件、D=0かつ望ましい向きでの不整合ゼロも証明した。実際のD_zが小さいことは、ここでは証明していない。

b>0、r=exp(-64b)に対し、**この直接下界が正であること**の厳密な条件は

`L_s(z)>0 ↔ [s*C_z<0 ∧ (1+r)²*D_z<4*r*v_z] ↔ B_s(z)<r*B_{-s}(z)`。

この条件はs*Δ_GI(z)>0の十分条件であり、GI自体の正値性の必要条件とは主張しない。同じABX rectangle Rの外側領域内の点z∈R.outerEventで、ACA rectangle marginが正なら、s=R.signに対して同じ共分散・相対欠損条件が必ず成立する。

同じ真正Perron断面 `F_z=C₀(z)-P(z)U_z`、`P(z)>0` から、条件は

`s*Cov(U_z,E)>0` かつ `(1+r)²*D_U(z)<4*r*Var(U_z)`

と同値。正のP²はこの相対欠損条件から消去できる。GIの中心は正符号の `b*(u+l)*P(z)*Cov(U_z,E)` で、下界・振幅にはPが残る。更新後の真正joint Perron半密度を含むUを別の源や局所量へ置換しない。この厳密条件が元の中心化物理源で成立することは未証明。

## CLOSED — 真正中心化物理源のゲージ変換と全配置tail障害

元のspatial Haar-L²中心化物理源 `f_H=½(W_H-⟨W_H,1⟩1)` を維持する。c=-I∈SU(2)をリンクeの始点だけに置く真正空間ゲージを、両外側境界へ同時に作用させる写像をΓ_eとする。元Perronの物理ベクトルと連続代表、元のkernel、物理源の連続代表を使い、

`P(Γ_e z)=P(z)`、`U_{Γ_e z}(g)=U_z(cg)`、`F_{Γ_e z}(g)=F_z(cg)`

を証明。右リンク更新は元のliteral Function.updateで、H=0も含め端点の相異性を使う。左右独立のゲージ不変性は仮定しない。

真正二コピーHaarの変数変換とE(cg)=2−E(g)から、

`M_s(Γ_e z)=M_{-s}(z)`、`C(Γ_e z)=-C(z)`、`v(Γ_e z)=v(z)`、`D(Γ_e z)=D(z)`、`B_s(Γ_e z)=B_{-s}(z)`

を証明。共分散・分散・欠損の恒等式はFとUの双方で成立する。**二つの固定posteriorアンカーを輸送する定理ではなく、GI自体の符号反転は主張しない。**

ABXの実際の正長方形に接続して、全有限H、b>0について、

`∃e, ∀s=±1, ∀θ<1, ¬[∀z, M_{-s}(z)≤θ*M_s(z)]`

を証明した。量化は**ある真正active linkの存在**であり、全リンクのactivityではない。同じリンクで各固定向きに対し全不整合が正となる外側配置も存在する。これは全配置で一つの向きに厳しいtail比率を課す方法の障害で、選択した外側領域上の制御や配置ごとの向き選択は排除しない。

## CLOSED / CONDITIONAL — 共通符号を要求しない元外側Haar二乗積分

`L_abs(z)=b*(u+l)*|C_z|-(b/2)*(u-l)*σ_z` と置くと `L_abs(z)≤|Δ_GI(z)|`。

元の外側configuration pair-Haar λ_Hの任意の可測集合Aで、実際に `L_abs(z)≥δ≥0` が全z∈Aで検証されれば、

`∫Δ_GI(z)²dλ_H≥λ_H(A)*δ²`

が成立する。A全体に共通の向き・傾き、可測な向き選択、内側長方形を要求しない。補助SU(2)二コピーHaarと元外側pair-Haarは区別する。正のδや有用なλ_H(A)、それらのH一様性は別途証明が必要。

[欠損解析](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e8803e0fcc69d051953d532ed246ff9467c5d616/MGAP4D/MathlibAnalytic/CompactEnergyMismatchDefect.lean) ／ [元GI共分散評価](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e8803e0fcc69d051953d532ed246ff9467c5d616/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCovarianceGIBoundsV5_PZ37ACC.lean) ／ [真正Perron・源のゲージ対称性](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e8803e0fcc69d051953d532ed246ff9467c5d616/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalGaugeTransferSymmetryV5_PZ37ACC.lean) ／ [元物理源の全配置tail障害](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e8803e0fcc69d051953d532ed246ff9467c5d616/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalGaugeMismatchObstructionV5_PZ37ACC.lean)。

## OPEN — 次段階P4-Q2-PZ37ACD

元の中心化Gauss-law源の真正U_zについて、選択した元外側Haar領域上で共分散・分散・相対欠損を評価し、厳密な欠損条件と正の絶対GI marginを証明する。全配置で固定した向きに厳しいtail優越を求める方法には上記の障害がある。領域の質量・振幅とH,b依存を制御し、元の外側pair-Haar二乗GI積分から真Gram／Rayleigh下界へ接続する。

実欠損・全tailの十分な小ささ、固定support cylinder、領域・振幅・Haar質量の体積一様性、遠方相殺、全物理Hilbert coercivityは未解決。元のHaar-L²中心化から固定リンク平均ゼロは導かず、MQの別Riesz商の局所性をUへ転用しない。ABSの粗誤差障害、ABM／PZ37ZA no-goを保持。common fine-positive、同一endpoint E/F、H1–H4、OS/Wightman、4D連続体Yang–Mills mass gapは**OPEN**。

**以下のACB以前の節は当時の履歴として完全に保存する。最新の到達点はこのACC追補を優先する。文書同期はdocs-only。**

---
> **main文書ミラー（ACB同期）**：唯一の定理正本は [formal/real-hilbert-uniform-coercive-strong-limit](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)、確認済み正本文書HEAD `9dde4d0174f85292f5b17eefcdef8e2cf2502701`（[正本docs #6048](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6048)）、定理squash `8721fe3bb5dc283ac55f67f27a254db18581973f`（[Lean PR #6046](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6046)）。ここではACBの検証記録だけを文書として反映し、Lean定理はmainに移さない。

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ACB（2026-10-31 JST）

**唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACB定理 PR #6046](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6046) **MERGED**。定理squash SHA＝マージ直後の正本HEAD `8721fe3bb5dc283ac55f67f27a254db18581973f`。exact-source `8356fc4a72052527d8b446f8b16574fb5a286e60` と定理squashの全Git tree `2befd0cf522bf3fd32fd3e8f4953683a763ff73b` は**完全一致**。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。

**検証：** [CI #41173509336](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41173509336) workflow／build job／Lean step **completed / SUCCESS**、**11,177／11,177 SUCCESS**。新規2 Leanファイル・19公開定理・19件の`#print axioms`は `propext`／`Classical.choice`／`Quot.sound` の範囲内、`sorryAx`なし、変更warning/error **0／0**。独立[completion receipt #124457218765](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41173509336/job/124457218765) **SUCCESS**、同一exact-source SHA・`source_result=success`を確認。既存Lean、真正Wilson模型・Perron・Gauss-law源、両interacting posterior、物理transfer norm、公開rootおよびworkflowを変更していない。

## CLOSED — 真正Perron断面上の符号付きエネルギー相関と回帰欠損

ACAの元の `F_z=C_0(z)-P_z U_z`、`P_z>0` を保持する。ABXで実際に構成された同じ長方形 `R` の外側 `z∈R.outerEvent` に対して、真正 `U_z` の `v_z=Var_μ(U_z)>0` を初めて明示的に証明。元のWilsonエネルギー `E` に対し `C_z=Cov_μ(U_z,E)`、`D_z=v_z-4C_z²≥0`、`s=R.sign∈{±1}` と置くと、

```text
ρ_z = 2 s C_z / sqrt(v_z),    -1 ≤ ρ_z ≤ 1,
1-ρ_z² = D_z/v_z.
B_s(z) = b P_z sqrt(v_z) (1-ρ_z).
```

をLean形式化した。これは真正Haar `Var(E)=1/4` と元のPerron物理受信器を用いる同一量の恒等式であり、独立に作ったテスト源や一リンクHaar posteriorには置換していない。指定 `b>0` では、ACAの最適残差証明書 `B_s<T_R` と `1-ρ_z<T_R/(bP_z sqrt(v_z))` が厳密同値。

## CLOSED / CONDITIONAL — 真の回帰欠損から全負tailと元GIの正値へ

同じABX領域・向き・正閾値 `T_R=e^{-64b}ηκν(V)` を使用。**追加の物理条件** `s C_z≥0` が検証されれば、

```text
B_s(z) sqrt(v_z) ≤ b P_z D_z,
true original negative tail ≤ exp(32b) b P_z D_z / sqrt(v_z).
```

を証明。さらに **`bP_zD_z<T_R sqrt(v_z)`** が別途成立すれば、ACAの正の残差証明書が成立し、実際の変更していない元の符号付き物理GI応答 `s Δ_GI(z)>0` が得られる。負tailは二つの本物のinteracting posteriorの全領域のまま。逆に、`s C_z≤0` かつ `T_R≤bP_z sqrt(v_z)` なら、**ACAの正の傾き残差族**はどの `a>0` を選んでも正の証明書にならない。この数値範囲で証明書が正なら `s C_z>0` が必要。いずれも実際のGIそのものの非正値や消失を意味しない。

[汎用相関／欠損定理](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/8721fe3bb5dc283ac55f67f27a254db18581973f/MGAP4D/MathlibAnalytic/CompactEnergyMismatchRegressionThreshold.lean) ／ [真正Perron物理源定理](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/8721fe3bb5dc283ac55f67f27a254db18581973f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTransferDefectCertificateV5_PZ37ACB.lean)。

## OPEN — 次はP4-Q2-PZ37ACC

真正の中心化Gauss-law源について、望ましい`s C_z≥0`および`bP_zD_z<T_R sqrt(v_z)`を**まだ証明していない**。元のspatial Haar-L²中心化を固定リンク受信器の平均ゼロへ取り違えず、ABR／ABSの元の遠方補正と更新後Perron半密度を保持し、Wilsonエネルギーモード成分と直交残差の実積分を解析する。さらにP、v、A、V、η、κの体積依存、固定support cylinder、遠方符号相殺、一様Gram／Rayleigh下界を独立に証明する必要がある。

ABS／ABM／PZ37ZAの障害は保持。全物理Hilbert coercivity、common fine-positive、同一endpoint E/F、H1–H4、OS/Wightman、非自明な4D連続体Yang–Mills existence/mass gap は**OPEN**。ACAの最適化の必要十分条件とACBの欠損による十分条件を区別する。

**以下のACA以前の記録は当時の履歴として完全に保存する。今回のREADME更新はdocs-onlyで新規Lean定理を追加しない。**

---

> **main文書ミラー（ACA同期）**：定理の唯一の正本は [formal/real-hilbert-uniform-coercive-strong-limit](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。確認済み正本HEAD `f3cb167e576250dd55b630cec1d448cbadf90a6d`（[正本文書同期 #6044](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6044)）。定理squashは `055efd930b9c45a3894282c9a6023db2abe3a753`。このmain文書更新はLean定理を追加・変更せず、以下のACA検証記録を鏡映する。

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ACA（2026-10-31 JST）

**唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACA PR #6043](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6043) **MERGED**。定理squash `055efd930b9c45a3894282c9a6023db2abe3a753` とマージ直後の正本HEADを完全一致で確認。exact-source `cdfdcc1a9150a1716b6f9153b400e25bbdbfc56f` と定理squashのGit tree `644c5d603630fb0266eb2099181dc16fdb5f7b96` も同一。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。

**検証：** [CI #41171556328](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41171556328) workflow・job・Lean step **completed / SUCCESS**、Lean **11,175 / 11,175 SUCCESS**。新規4 Leanファイル・43公開定理・43件の `#print axioms`、標準3公理以内、`sorryAx`なし、変更warning/error **0/0**。独立completion receipt [job #124451395379](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41171556328/job/124451395379) **SUCCESS**。

## CLOSED — 全不整合モーメントの傾きパラメータを除いた上界

元のFF物理受信器について `v_z=Var_μ(F_z)`、`C_z=Cov_μ(F_z,E)`、`s²=1` とする。ABZの元の残差上界 `Q_z(a)=(b/a)Var_μ(F_z+s*a*E)`（a>0）から、

`M_{-s}(z) ≤ B_s(z) := b*(sqrt(v_z)+2*s*C_z)`

を全有限H、b≥0、元のGauss-law物理源について証明した。v_z=0、b=0も含む。元の全負寄与を積分に残し、小tail仮定は使わない。正確な差は

`Q_z(a)-B_s(z) = b/(4*a)*(a-2*sqrt(v_z))² ≥ 0`。

任意の閾値tについて `(∃a>0, Q_z(a)<t) ↔ B_s(z)<t`。これは**ABZの正の傾き残差族における厳密な最適化**であり、B_sと実際のM_{-s}やGIが等しいという主張ではない。一般のv_z=0では下限が正のaで達成されない場合も処理した。

## CLOSED — 真のエネルギー回帰残差とPerron転送断面

真正SU(2) HaarのVar(E)=1/4を使い、

`D_z := Var(F_z)-4*Cov(F_z,E)² = Var(F_z-4*Cov(F_z,E)*E) ≥ 0`、

`Var(F_z+s*a*E)=D_z+(s*a+4*Cov(F_z,E))²/4`

を証明。共分散Cauchy境界 `2*|Cov(F_z,E)|≤sqrt(Var(F_z))` も実残差から導く。**分散を最小にする回帰係数 -4Cov と、v_z>0のときにb/aを含むtail上界を最小にする傾き a*=2sqrt(v_z) は区別する。**

ABZの元の `F_z=C₀(z)-P(z)U_z`、`P(z)=‖T‖⁻¹*sqrtDensity(z)>0`、`U_z(g)=I_f(z₂[e:=g])/sqrtDensity(z₁,z₂[e:=g])` から、

`Var(F_z)=P(z)² Var(U_z)`、`Cov(F_z,E)=-P(z)Cov(U_z,E)`、
`D_F=P(z)²D_U`、`Var(F_z+s*aE)=P(z)²Var(U_z-s*(a/P(z))*E)`

を厳密に輸送した。従って実模型で評価すべき同じ最適上界は

`B_s(z)=b*P(z)*(sqrt(Var(U_z))-2*s*Cov(U_z,E))`。

更新後の真正joint Perron半密度、右リンク更新、元のtransfer normを保持する。元のspatial Haar-L²物理源の中心化は、固定リンク受信器の平均ゼロやPerron真空中心化ではない。MQの別のRiesz商の局所性をUへ転用していない。

## CLOSED — 元の物理量による分散の上下評価

元のFF/FCの係数 `K=‖T_{H,2,b}‖⁻¹*((exp(8*b))³-1)*‖f‖` を保持して、

`Var(F_z)≤K²`、`sqrt(Var(F_z))≤K`、
`M_{-s}(z)≤b*(K+2*s*Cov(F_z,E))`

を証明。最後の粗い上界でも実共分散項を残すが、最適化の必要十分条件をKによる条件へ置き換えない。真transfer normのH依存、ABSの粗誤差障害は残る。

さらに、ABXの実際の長方形 `A,V,η,κ,s` についてz∈Aなら、

`Var(F_z)≥η²*(μ×μ)(V)/2>0`。

これにより同じ領域上で `a*(z)=2sqrt(Var(F_z))>0` が実際に最適値を達成する。ABVの固定capの1/64下界は使っていない。η、V、Kの体積一様性は未証明。

## CLOSED / CONDITIONAL — 正の残差証明書の必要十分条件と元GI

ここでは `s=R.sign` とし、η・κ・Vも同じABX rectangle Rの値を使う。最適化するパラメータは正の傾きaである。

各外側点zで、あるa>0についてABZ残差下界が厳密に正となることは、

`B_s(z)<T_R := exp(-64*b)*η*κ*(μ×μ)(V)`

と**必要十分**。この条件が失敗すれば、aを選び直してもこの残差族から正値は認証できない。これは元GI自体の非正値性を意味しない。

元posteriorの全負tailは `exp(32*b)*B_s(z)` 以下。ABXのz∈Aでは元GIについて

`s*Δ_GI(z)≥L_*(z):=[exp(-32*b)*η*κ*(μ×μ)(V)-exp(32*b)*B_s(z)]/2`。

`L_*(z)≥δ≥0` がA全体で検証されるという明示条件の下で、元の外側configuration pair-Haar λ_Hに対し `∫Δ_GI(z)²dλ_H≥λ_H(A)*δ²` を証明。点ごとの最適上界を直接使うので、A全体に共通のaや可測な傾き選択を仮定しない。補助SU(2)二コピーHaarと元外側pair-Haarは区別したまま。

[最適化解析](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/055efd930b9c45a3894282c9a6023db2abe3a753/MGAP4D/MathlibAnalytic/CompactEnergyMismatchOptimization.lean) ／ [分散・共分散輸送](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/055efd930b9c45a3894282c9a6023db2abe3a753/MGAP4D/MathlibAnalytic/CompactEnergyMismatchAffine.lean) ／ [真正転送断面](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/055efd930b9c45a3894282c9a6023db2abe3a753/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTransferRegressionV5_PZ37ACA.lean) ／ [実物理最適証明書](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/055efd930b9c45a3894282c9a6023db2abe3a753/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOptimizedMismatchCertificateV5_PZ37ACA.lean)。

## OPEN — 次段階P4-Q2-PZ37ACB

元の中心化Gauss-law源の真正U_zから、望ましい共分散方向と回帰欠損D_Uの大きさを評価し、実際の `bP*(sqrt(VarU)-2sCov(U,E))<T_R` を証明する。ACAの必要十分条件がこの実模型で充足されたとは主張しない。小bの係数だけで勝てるとも主張しない。ABXのκ・振幅・領域もb,Hに依存し得る。

実残差の十分な小ささ、固定support cylinder、領域・振幅・Haar質量のH一様性、遠方相殺、真Gram／Rayleigh一様下界は未解決。ABSの粗Haar中心化誤差障害、ABM／PZ37ZA no-goを保持。全物理Hilbert coercivity、common fine-positive、同一endpoint E/F、H1–H4、OS/Wightman、4D連続体Yang–Mills mass gapは**OPEN**。

**以下のABZ以前の節は当時の履歴として完全に保存する。最新の到達点はこのACA追補を優先する。文書同期はdocs-only。**

---
# main文書ミラー更新 — P4-Q2-PZ37ABZ（2026-10-31 JST）

このmainは文書ミラー。唯一の定理正本は [formal/real-hilbert-uniform-coercive-strong-limit](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)、現在の正本HEADは `15783bdb15a9df34e45dacf2629f9c25bac70ba2`（[README・ROADMAP同期 #6041](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6041) MERGED）。ABZ定理squashは `bf7d9575a7f3f25e041b901e00a72f3034ccd244`。その後の正本変更はREADME・ROADMAPへの追記のみ。以下は正本の検証済みABZ追補の文書ミラーであり、定理の正本をmainへ移していない。

---

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ABZ（2026-10-31 JST）

**唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ABZ PR #6040](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6040) **MERGED**。定理squash `bf7d9575a7f3f25e041b901e00a72f3034ccd244` とマージ直後の正本HEADを完全一致で確認。exact-source `f1499f8d2d20e97e0f5a111e60628d35b6c6b7d5` とsquashのGit tree `971fc2f9be67aa8eb9e150d355dceaff037eb29e` も同一。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。

**検証：** [CI #41168743376](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41168743376) workflow・job・Lean step **completed / SUCCESS**、Lean **11,171／11,171 SUCCESS**。新規3 Leanファイル・35公開定理・35件の `#print axioms`、全て標準3公理以内、`sorryAx`なし、変更warning/error **0/0**。独立completion receipt [job #124442869146](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41168743376/job/124442869146) **SUCCESS**。

## CLOSED — 全負tailを真正受信器のエネルギー残差分散で上から評価

ABYの元の物理受信器 `F_z(g)`、元Wilsonエネルギー `E(g)`、全不整合モーメント `M_{-s}(z)` をそのまま用いる。任意の `a>0` に対し `R_{z,s,a}(g)=F_z(g)+s*a*E(g)` と定義すると、**全有限H、b≥0、元の任意Gauss-law物理源について、tailの小ささを仮定せず**

`M_{-s}(z) ≤ (b/a) Var_μ(R_{z,s,a})`

をLean証明した。元の `Ψ_s=2bs(F(g)-F(h))(E(h)-E(g))` に対する点ごとの平方完成

`max(-Ψ_s(g,h),0) ≤ b*(R(g)-R(h))²/(2a)`

と、真の二コピー積分 `∫(R(g)-R(h))² d(μ×μ)=2 Var_μ(R)` から導く。主上界は `s=±1` に限らず任意の実数sで成立し、`b=0` も含む。**全負寄与を捨てたり、残差を新しい物理源へ置換したりしていない。**

元SU(2) Haarの既証character定理から `∫E=1`、`∫E²=5/4`、`Var_μ(E)=1/4` を導き、

`Var_μ(R)=Var_μ(F_z)+2*s*a*Cov_μ(F_z,E)+(s*a)²/4`

も厳密に証明。s=±1なら最後の項はa²/4となる。全負tailの**実物理量による上界**が得られた一方、この上界が正寄与を上回らないほど小さいことは別の未解決問題である。

## CLOSED — 真正Perron転送断面と共分散の障害

`L=‖T‖⁻¹`、`P(z)=L*sqrtDensity(z)>0`、
`U_z(g)=I_f(B[e:=g])/sqrtDensity(z.left,B[e:=g])` とすると、元GN/FFの署名のまま

`F_z(g)=L*I_f(B)-P(z)*U_z(g)`、
`F_z(g)-F_z(h)=P(z)*(U_z(h)-U_z(g))`

を証明。更新後の真正joint Perron半密度・元transfer norm・右リンク更新を保持する。Uの連続性、b>0でのエネルギー順序との符号同値、全不整合積分の厳密転送表示も証明した。Harnackの大きさ比較やMQのRiesz商の局所性からUの単調性・遠方消滅は導いていない。

さらに `M_s-M_{-s}=∫Ψ_s=-4bs Cov_μ(F_z,E)`。従って `s Cov_μ(F_z,E)≥0` なら、**ABYの十分条件である `[e^{-32b}M_s-e^{32b}M_{-s}]/2` は非正**になる。これはこの比較下界に対するobstructionであり、実係数kの変動が残る元GI自体の非正値性ではない。

## CLOSED / CONDITIONAL — ABX実長方形から元GI・外側pair-Haarへ接続

元posteriorの**全**負tailは `e^{32b}*(b/a)*Var_μ(R)` 以下。ABXの実際の `A,V,η,κ,s` で、z∈Aなら

`s Δ_GI(z) ≥ [e^{-32b}ηκ(μ×μ)(V) - e^{32b}(b/a)Var_μ(R_{z,s,a})]/2`。

従って、この下界から厳密正値へ進むための具体的な目標は `(b/a)Var_μ(R_{z,s,a}) < e^{-64b}ηκ(μ×μ)(V)` を元の物理源で証明することになる。この比較は未証明。

この右辺がA全体でδ≥0以上という**明示的なresidual margin条件の下でのみ**、元の外側configuration pair-Haarについて

`∫ Δ_GI(z)² dμ_H(z) ≥ μ_H(A)*δ²`

を証明。補助SU(2)二コピーHaarと元の外側pair-Haarは別の測度のまま保持。ABXのVはABVの固定capとは限らず、1/64の下界を転用していない。

[一般解析Lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/bf7d9575a7f3f25e041b901e00a72f3034ccd244/MGAP4D/MathlibAnalytic/CompactEnergyMismatchMoment.lean) ／ [真正転送断面Lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/bf7d9575a7f3f25e041b901e00a72f3034ccd244/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalReceiverTransferSectionV5_PZ37ABZ.lean) ／ [実物理残差分散Lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/bf7d9575a7f3f25e041b901e00a72f3034ccd244/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalMismatchResidualVarianceV5_PZ37ABZ.lean)。

## OPEN — 次段階P4-Q2-PZ37ACA：実残差の小ささと体積一様性

元の中心化Gauss-law源について、真Perron転送断面から `Var_μ(F_z+s*a*E)` と共分散を評価し、正寄与との大小関係を証明する。aの最適化は可能な次の解析課題だが、実残差の小ささを自動的に与えない。ABXの領域・振幅・質量のH依存、固定support cylinder、遠方相殺、Gram／RayleighのH一様下界は未解決。ABSの粗いHaar中心化絶対誤差の障害、ABM／PZ37ZA no-goを保持。全物理Hilbert coercivity、common fine-positive、同一endpoint E/F、H1–H4、OS/Wightman、4D連続体Yang–Mills mass gapは**OPEN**。

**以下のABY以前の節は当時の履歴として完全に保存する。最新の到達点はこのABZ追補を優先する。文書同期はdocs-only。**

---


# MGAP4D main文書ミラー — ABX–ABY（2026-10-31 JST）

この `main` は唯一のLean定理正本 `formal/real-hilbert-uniform-coercive-strong-limit` の**文書ミラーのみ**であり、主張するLean定理をmainに移したものではない。正本docs-only [PR #6038](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6038) のsquash `344e3a857bea068a83e071d787cfcde56a42b9db` に基づく。最新定理bearing squashはABY [PR #6037](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6037) の `e9641c02a2830455ac8fec3ce288561acf589914`。ABX [PR #6036](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6036) も正本へ統合済み。mainの既存本文は以下に完全に保存する。

---

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ABX–ABY（2026-10-31 JST）

**唯一の定理正本**は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は**文書ミラー**であり定理正本ではない。ABXの定理PR [#6036](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6036) と、最新のABY定理PR [#6037](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6037) はともに **MERGED**。最新のABY定理squash `e9641c02a2830455ac8fec3ce288561acf589914` がマージ直後の正本HEADに完全一致。検証したABYのexact source `6070d795822f9908b359d3e58bca63c43ca3b10a` はsquashとは異なるコミットで、**全tree `49c34e6dbdc33a8b6f00fad606dd0ead73da35d1` が同一**。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変。

**独立検証：** ABX [CI #41162615381](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41162615381) は **11,166/11,166 SUCCESS**、新規10公開定理、標準3公理のみ、`sorryAx`なし、変更warning/error 0/0、独立completion receipt [#124424290535](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41162615381/job/124424290535) SUCCESS。ABY [CI #41165349729](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41165349729) は **11,168/11,168 SUCCESS**、新規16公開定理、標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更warning/error 0/0、独立completion receipt [#124432651768](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41165349729/job/124432651768) SUCCESS。

## CLOSED — ABX：真正物理受信器の整合領域を実模型から構成

AAZの既証定理「すべての有限H・b>0で、同一の中心化Gauss-law源の真正GI gapがあるリンクで非零」を、ABTの厳密な符号付き二点表示とFFの**変更していない真正受信器**へ接続。新規の整合仮定なく、ある真正リンク `e`、向き `s∈{1,-1}`、非空**開**の外側真正pair-Haar境界event `A` と、非空**開**の内側補助二コピーSU(2) Haar event `V` を構成し、両方の元のHaar質量が**厳密正**であること、`η,κ>0` があって `∀z∈A, ∀(g,h)∈V, s(F_z(g)-F_z(h))≥η, c_b(g,h)≥κ` を証明した。その結果、`∀z∈A, ∫_V s Φ_z d(μ×μ)≥ηκ exp(-32b)(μ×μ)(V)>0`。向きsは受信器の符号記録であり**物理源の置換ではない**。新規 `V` はABVの固定cap `U` と一致するとは限らず、固定capのHaar下界 `1/64` は移植しない。

[ABX全Lean本文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/72ea17713148f75bc59be714e0211a8b710e5a6d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalActualReceiverAlignmentV5_PZ37ABX.lean)。

## CLOSED — ABY：真正密度行列式・全符号付きtailの厳密両側比較

ABUの元の二つの相互作用Wilson posteriorの行列式 `D_b(g,h)` と、元の時間Wilsonエネルギー交差 `c_b(g,h)=2b(E(h)-E(g))` に対し、全点で **`D_b=k_b c_b`** を証明した。`c_b≠0` で `k_b=D_b/c_b`、`c_b=0` では `k_b=1` と定義し、`exp(-32b)≤k_b≤exp(32b)` を全有限H・真正リンク・右背景について証明。零交差でのこの総関数の**連続性は主張しない**。係数は新しいposteriorでも新しい物理測度でもない。

`Φ_z(g,h)=(F_z(g)-F_z(h))D_b(g,h)`、`Ψ_{z,s}(g,h)=s(F_z(g)-F_z(h))c_b(g,h)`、`M_s(z)=∫_{G×G} max(Ψ_{z,s},0)d(μ×μ)` とすると、全域で `sΦ_z=k_b Ψ_{z,s}`、負領域の一致、完全正・負部分の両側評価

`exp(-32b)M_s≤∫max(sΦ_z,0)≤exp(32b)M_s`、

`exp(-32b)M_{-s}≤∫max(-sΦ_z,0)≤exp(32b)M_{-s}`

と、**元のGI gap** の両側下界／上界

`(exp(-32b)M_s-exp(32b)M_{-s})/2 ≤ sΔ_GI(z) ≤ (exp(32b)M_s-exp(-32b)M_{-s})/2`

を新たなtail上界の**仮定なしでLean証明**した。ABXの実整合長方形で `M_s(z)≥ηκ(μ×μ)(V)` を得るため `∀z∈A` で

`sΔ_GI(z) ≥ [exp(-32b)ηκ(μ×μ)(V)-exp(32b)M_{-s}(z)]/2`。

これは**全負寄与の小ささの証明ではない**。実物理受信器に依存する全不整合積分 `M_{-s}` が定量的に露出したことが成果。

[ABY密度係数Lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e9641c02a2830455ac8fec3ce288561acf589914/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalDeterminantSlopeV5_PZ37ABY.lean) ／ [ABY全符号付きtail Lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e9641c02a2830455ac8fec3ce288561acf589914/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullSignedTailV5_PZ37ABY.lean)。

## OPEN — 次段階P4-Q2-PZ37ABZ（仮称）：実物理不整合・体積一様性

最重要の未解決入力は `M_{-s}` の**真正Wilson物理源からの**小ささと、ABXで構成された `A,V,η,κ` の**Hに依存しない**局所・固定support構成または適切な割合評価である。さらにABW／ABX／ABYの補助 `μ×μ` と元の外側pair-Haar `μ_H` を混同しない。他プラケット・遠方相殺、ABSの粗いHaar中心化絶対誤差obstruction、ABM／PZ37ZA no-goを維持。全物理Hilbert coercivity、共通positive-fine、同一endpoint E/F、任意深さ、H1–H4、OS/Wightmanおよび4D連続体Yang–Mills mass gapは**OPEN**。

**以下のABW以前の節は当時の履歴として無修正で保持する。** この文書同期はdocs-onlyで、Leanを不要に再実行しない。

---

# MGAP4D — main文書ミラー（P4-Q2-PZ37ABW・2026-10-31 JST）

このdefault `main` は **README・ROADMAPのみの文書ミラー**であり、唯一のLean定理正本 `formal/real-hilbert-uniform-coercive-strong-limit` ではない。[正本docs-only #6034](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6034) の統合commit `7c6b3f093fa17939d6a54b8c3827bb4d6a620053` に基づき、定理 #6033 の検証済み成果を文書として反映する。ABW定理squash `f37f4fceb0ee6b74d3d30e63be9cb1006e3c1e4e`、exact-source `405aae45e47501ca868bad5258ead2c0fa7efd7e`、[CI #41159498041](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41159498041) はいずれも別々の証拠であり、mainにLean定理を移すものではない。

---

# MGAP4D — 最新検証済み定理 P4-Q2-PZ37ABW（2026-10-31 JST）

**唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーであり、Lean定理正本ではない。[ABW PR #6033](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6033) は **MERGED**。最後の定理bearing squash SHA とマージ直後の正本HEADは `f37f4fceb0ee6b74d3d30e63be9cb1006e3c1e4e` で完全一致した。検証したsource SHAは `405aae45e47501ca868bad5258ead2c0fa7efd7e` で、squash SHAとは区別する。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を固定。

**exact-source検証：** [CI #41159498041](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41159498041) は workflow・Lean step **completed / SUCCESS**、依存先を含め **11,008 / 11,008 SUCCESS**。新規Lean 1ファイル（218行、8公開定理）のwarning/error **0/0**、8件の `#print axioms` は `propext`／`Classical.choice`／`Quot.sound` のみ、`sorryAx` なし。独立completion receipt [#124415047421](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41159498041/job/124415047421) も **SUCCESS**。検証sourceと定理squashの全ファイルtree `bc481a3ac39226e8a9426436f83cc67222c5c88c` は完全一致。

## CLOSED — 真正物理受信器についての条件付き正Haar領域・負tail接続

既存ABTの**元のGauss-law物理Hilbert源** `f`、FFの**元のsigned receiver** `F(g)`、二つの正規化された**元の相互作用Wilson posterior** `p₀,p₁` をそのまま保ち、ABUの `D_b(g,h)=p₀(g)p₁(h)-p₁(g)p₀(h)` と `Φ=(F(g)-F(h))D_b(g,h)` を同一視した。ABVの変更されていない固定SU(2) Haar領域 `U={E(g)≤1/2}×{E(h)≥3/2}` は `(μ×μ)(U)≥1/64`、`D_b≥2b exp(-32b)` を持つ。

**今回の条件付き定理：** 実際の元の受信器について `b≥0`、`η≥0`、`∀(g,h)∈U, F(g)-F(h)≥η` を**明示的な前提**とすると、

`Φ(g,h)≥2ηb exp(-32b)`（領域 `U` 上）、

`∫_U Φ d(μ×μ) ≥ η b exp(-32b)/32`、

`∫_(G×G) max(Φ,0) d(μ×μ) ≥ η b exp(-32b)/32`。

さらに**全負部分** `∫max(-Φ,0)≤N` を独立に証明できれば、実際の同じ物理GI expectation gapについて

`Δ_GI ≥ (η b exp(-32b)/32 - N)/2`

が従う。`b>0` かつ `N<η b exp(-32b)/32` なら `Δ_GI>0`。代替として**実際の符号付き補集合積分** `∫_(Uᶜ)Φ≥-N` を前提にしても同じ下界をLean証明した。負tailも他プラケットも削除していない。

[完全な新規Lean定理本文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f37f4fceb0ee6b74d3d30e63be9cb1006e3c1e4e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalReceiverHaarRegionMarginV5_PZ37ABW.lean)。8定理には全て `#print axioms` が付く。ABV以前の定理・正規化・Perron代表・public rootを変更していない。

## OPEN — 今回は証明していない独立した物理入力

- 実際の元の物理受信器での、`η>0` となる点ごと・領域一様の**符号整合と振幅**。元のFF定義で `F` は正のWilson joint半密度×逆Perron因子で割った**真正joint receiverの右リンク更新差**であり、`D_b>0` だけから受信器差の符号は出ない。次はこの更新差の符号・定量範囲を元の物理源ごとに分析する。
- 元の `∫max(-Φ,0)`、または `∫_(Uᶜ)Φ` に対する**実モデル内の全寄与制御**。この `N` の量的制御、他プラケット・遠方相殺、真正外側境界pair-Haar `A_p/G` の体積一様下界はOPEN。
- 全物理Hilbert coercivity、共通positive-fine、同一endpoint E/F、任意深さ、H1–H4、OS/Wightman、非自明な4D連続体Yang–Millsとmass gapは**OPEN**。ABSの粗いHaar中心化絶対誤差の障害、ABM・PZ37ZAの量化されたno-goを保持する。

**以降のABVまでの「最新」「OPEN」記述は、証明当時の履歴として原文を保持する。現在の到達はABWの上記条件付き定理であり、未証明条件はCLOSEDにしない。** この文書の追記はdocs-onlyで、Strict Leanを不要に再実行しない。

---

# MGAP4D

## 現在の定理チェックポイント — 2026-10-31 JST · P4-Q2-PZ37ABR–ABV

**この `main` は文書ミラーであり、Lean定理正本ではない。** 唯一の定理正本は [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。この追補は正本の検証済み結果を文書として反映する。Lean定理を `main` へ移したという意味ではない。

**文書ミラー同期元：** 正本のdocs-only commit [`e30f72afe94c8023cc7d185ee059a1a08a58bc88`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/e30f72afe94c8023cc7d185ee059a1a08a58bc88) の [README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e30f72afe94c8023cc7d185ee059a1a08a58bc88/README.md)／[ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e30f72afe94c8023cc7d185ee059a1a08a58bc88/ROADMAP.md)。この文書同期SHAとABVの検証source・定理squashを区別する。

**検証済み基準点：** [ABV / PR #6030](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6030) の定理squash [`3b0974b18ad4d7843298ce92be2365fd1e2409e6`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/3b0974b18ad4d7843298ce92be2365fd1e2409e6)。このSHAはABR–ABVの統合を含む。ABVのexact-sourceは [`af809652c2ee4d77949fea7c9881c3aada45bacf`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/af809652c2ee4d77949fea7c9881c3aada45bacf)。検証したPR source SHAと定理squash SHAを区別し、後続のdocs-onlyマージは新しい定理の証明と数えない。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持する。

### ABR–ABV — 元の相互作用Wilson模型で閉じたこと

| 段階 | 証明済みの内容 | 量化・限界 |
| --- | --- | --- |
| [ABR #6026](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6026) | 元のsourceにPerron因子を挿入しない遠方重み `S_B`、既存Perron遠方重み `R_B`、正の補正 `V_B=S_B/R_B` を区別。真の四辺Perron周辺密度と元のsourceの厳密積分表示、正負部分への分解。 | `V_B=1` を仮定しない。真の物理転送ノルム `t_(H,b)` と `Ω_b(B)` を保持。 |
| [ABS #6027](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6027) | `b≥0` で `S_B` の相対比較係数 `exp(24b)`、`V_B` の相対比較係数 `exp(80b)`、任意の符号付き連続四辺テストの厳密な絶対誤差評価。 | 全絶対値費用は負部分を含む。正値性は明示したsigned-margin条件の下でのみ成立し、絶対質量の体積一様下界は得ていない。 |
| [ABT #6028](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6028) | 同じ物理受信器と二つの元の相互作用posteriorについて、GI gapを二変数の符号付き積分として厳密表示。正負の積分の差と正値性の必要十分条件。 | Haarの二変数は補助的な一リンク群の二コピー。posterior独立性や元の外側境界pair-Haarの置換を意味しない。 |
| [ABU #6029](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6029) | 実際のposterior密度行列式 `D_b` を時間Wilson crossing `c_b` と正の実密度積で表示し、体積に依存しない点ごとの下界を導出。 | `c_b` の定義は `H`・選択リンク・右背景に依存しない。密度行列式の正値性と物理受信器の符号・振幅の整合は別の入力。 |
| [ABV #6030](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6030) | 元のSU(2) Haar上の固定領域 `U={E(g)≤1/2}×{E(h)≥3/2}` に質量 `≥1/64` を与え、実際の `∫_U D_b≥b exp(-32b)/32` を導出。 | 全有限 `H`・実リンク・右背景に共通。`b>0` で厳密正値。物理受信器差を掛けたGI積分の下界は別途必要。 |

正本 `39b481be...` の完全な物理定理本文：[ABR](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/39b481be7bc2e64e406c66414f0a4224048727ef/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceRemoteCorrectionV5_PZ37ABR.lean)／[ABS](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/39b481be7bc2e64e406c66414f0a4224048727ef/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceSignedErrorV5_PZ37ABS.lean)／[ABT](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/39b481be7bc2e64e406c66414f0a4224048727ef/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalGITwoPosteriorPairingV5_PZ37ABT.lean)／[ABU](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/39b481be7bc2e64e406c66414f0a4224048727ef/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPosteriorDeterminantBoundsV5_PZ37ABU.lean)。

**ABRの正規化。** 元の四辺時間核を `K₄`、元の空間半重みを `hW` とし、`M_B=∫K₄(x,B_four)R_B(x)dμ⁴(x)`、`d_B(x)=K₄(x,B_four)R_B(x)/M_B` と置く。`d_B>0`、`∫d_B=1`、`hW(B)M_B=t_(H,b)Ω_b(B)` が成立し、元のsourceについて

`∫K_b(A,B)f(A_four)dHaar_H(A) = t_(H,b)Ω_b(B) ∫d_B(x)V_B(x)f(x)dμ⁴(x)`。

`d_B` はこのPerron四辺周辺密度であり、以下の二posterior行列式 `D_b` とは異なる。`Z_b⁴` や `Z_b^|L_H|` を物理転送ノルムに代入しない。

**ABSの解析的注意（この段落の障害はABSで新しいLean定理として形式化したものではない）。** Haar中心化 `∫f=0` の場合、`q=K₄`、`J=∫qf`、`L=∫q|f|` とすると、元の一リンク核の評価から `exp(-8b)≤q≤1`、従って `|J|≤(exp(8b)-1)L≤(exp(24b)-1)L`。このため粗い絶対誤差による厳密十分条件 `(exp(24b)-1)L<J` は成立しない。この障害は元の符号付きsourceが消えるという定理ではなく、符号付き相関を保持する必要性を示す。

**ABTの厳密な符号付きpairing。** 同じ元のGI物理受信器を `F`、二つの元の正規化相互作用Wilson posterior密度を `p₀,p₁` とし、

`D_b(g,h)=p₀(g)p₁(h)-p₁(g)p₀(h)`、`Φ(g,h)=(F(g)-F(h))D_b(g,h)`

と置く。連続性・可積分性を伴って

`Δ_GI = (1/2) ∫_(μ×μ) (F(g)-F(h))D_b(g,h) = (1/2)(∫Φ₊-∫Φ₋)`

を証明した。ここで `Φ₊=max(Φ,0)`、`Φ₋=max(-Φ,0)`。従って `Δ_GI>0` と `∫Φ₋<∫Φ₊` は同値であり、正部分の下界と全負tailの上界を独立に与えた場合に定量的GI下界が従う。その入力を無条件に成立したものとは扱わない。

**ABUの実密度行列式下界。** `b≥0` について、同じ元のposteriorから

`D_b(g,h)=p₁(g)p₀(h)(exp(c_b(g,h))-1)`、`exp(-32b)≤p₁(g)p₀(h)≤exp(32b)`

を証明した。`D_b≥0 ↔ c_b≥0`、`c_b≥0 ⇒ D_b≥exp(-32b)c_b`、および `|D_b|≥exp(-32b)|c_b|`。元のSU(2)の `R(π)` に対し `c_b(1,R(π))=4b` なので、`b>0` なら全有限 `H`（`H=0` を含む）、全実リンク、全右背景で

`D_b(1,R(π))≥4b exp(-32b)>0`。

ABU単独では一対の群要素での点ごとの証明である。下のABVが正Haar測度領域とその行列式積分を閉じるが、`F(g)-F(h)` の正の下界や積分後の正のGI gapは別の入力として残る。

### ABV — 固定の正Haar測度領域と実posterior行列式の積分下界

`E` は変更されていないSU(2) Wilsonエネルギー、`μ` は元の正規化compact Haarである。`A={g:E(g)≤1/2}`、`C={h:3/2≤E(h)}`、`U=A×C` と置く。この領域は結合 `b`、体積 `H`、リンク、右背景に依存しない。

元の四つのquaternion平行移動と `χ=1-E` から `Σ_(j<4)χ(q_j g)²=1` を導く。従って元のSU(2)の**八つのHaar保存左平行移動**による `A` の逆像が全群を覆い、`μ(A)≥1/8`。真正の中心元による平行移動で `μ(C)=μ(A)≥1/8`、よって `(μ×μ)(U)≥1/64`。八つの点を別の有限群Haarに置き換えていない。

元の `R(π)` が中心の負単位元と等しいこと、`E(R(π)⁻¹g)=2-E(g)`、および

`c_b(g,h)=2b(E(h)-E(g))`

を厳密に証明した。このcrossingは連続で、`b≥0` なら `|c_b(g,h)-4b|=2b(E(g)+2-E(h))`。可測な `U` は `(1,R(π))` の近傍であり、厳密不等式 `E(g)<1/2`、`E(h)>3/2` の開近傍を含む。

`b≥0` で `U` 上の `c_b≥2b` とABUの実密度行列式下界から、元の二つの相互作用posteriorについて

`D_b(g,h)≥2b exp(-32b)`、`∫_U D_b(g,h)d(μ×μ)≥b exp(-32b)/32`

を証明した。実行列式の連続性・可積分性も証明し、`b>0` なら右辺は厳密に正である。全有限 `H`（`H=0` を含む）、全実リンク、全右背景に同じ評価が成立する。

定理本文：[元のSU(2) Haar capと八平行移動](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/3b0974b18ad4d7843298ce92be2365fd1e2409e6/MGAP4D/MathlibAnalytic/SpecialUnitaryTwoWilsonEnergyHaarCapsV5_PZ37ABV.lean)／[実posterior行列式の正領域・積分下界](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/3b0974b18ad4d7843298ce92be2365fd1e2409e6/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPosteriorPositiveHaarRegionV5_PZ37ABV.lean)。これはABTの**補助的な二コピーHaar上での制限積分**であり、物理受信器差 `F(g)-F(h)` の整合、全負tail、元の外側境界pair-Haar上の下界は引き続き必要である。

### 検証記録 — source・squash・CIを区別

| PR | exact PR source SHA | 定理squash SHA | 完了したPR Lean Fast Check |
| --- | --- | --- | --- |
| ABR #6026 | `08c5d63bafa0e344ac1e7c34812f427d1cfcadea` | `bb6c8559693dd7bb48806408829b42c79828477a` | [#41139912350](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41139912350)：11,012/11,012 SUCCESS、18公開定理 |
| ABS #6027 | `b448b6c183142433720a9450e0c0e3d47db1a831` | `59814cd69781b6ebae9bcf605e79441dad4b88bf` | [#41150355205](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41150355205)：11,014/11,014 SUCCESS、10公開定理 |
| ABT #6028 | `4933d4f0dd7e8e3155d15c73b7fafb795a467893` | `dd5409990c522ec7dc86e2042e469521d8d718bc` | [#41153079696](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41153079696)：10,652/10,652 SUCCESS、17公開定理 |
| ABU #6029 | `105023f814c64e6044263ea965a43e155634ad35` | `39b481be7bc2e64e406c66414f0a4224048727ef` | [#41155882313](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41155882313)：10,654/10,654 SUCCESS、14公開定理 |
| ABV #6030 | `af809652c2ee4d77949fea7c9881c3aada45bacf` | `3b0974b18ad4d7843298ce92be2365fd1e2409e6` | [#41157968798](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41157968798)：11,007/11,007 SUCCESS、27公開定理 |

いずれも変更Leanのwarning/error **0/0**、上記公開定理の `#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、別のexact-source completion receipt **SUCCESS**。ABVの別receiptは [job #124410035502](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41157968798/job/124410035502)。ABRのPR本文に残る初期の検証待ち記述は、完了した上記runとreceiptを現在の検証状態として読む。ABRには任意の旧direct diagnosticが既存flagを尊重するための最小workflow修正が含まれるが、必須の依存関係付きLake検査は維持された。ABS–ABVは新規Lean leafと計画文書の追加であり、既存の物理定義・前提・依存pin・public root・workflowを変更していない。

### OPEN — 真正GIから全物理Hilbert・4D連続体へ

二つの元の相互作用posteriorと同じ物理受信器についての**体積一様な正のGI下界**、受信器差の符号・振幅と密度crossingとの整合、全負tailと他プラケット相殺の制御、元の完全外側pair-Haar上の `A_p`／`G` の一様正下界は **OPEN**。密度行列式下界を物理GI応答の下界へ自動的に読み替えない。

**次のABW候補は条件付きの元の物理受信器整合。** ABVの同じ `U` 上に `F(g)-F(h)≥η≥0` という明示的な入力を置いた場合のsigned pair積分下界を、元の物理受信器のまま形式化する。その条件の実際の成立、正の一様 `η` の構成、および全負tailとの正の余裕は、条件付き命題の証明とは別のOPEN入力である。

全物理Hilbert coercivity、共通positive-fine区間、同一endpoint E/F、任意深さの一様評価、H1–H4、OS/Wightman再構成、非自明な4D連続体Yang–Mills構成とmass gapも **OPEN**。ABMの上限のみの結合条件に対する障害、PZ37ZAの別の補償済み二文脈量のno-go、および全ての先行定理・履歴を保持する。詳しい次の独立入力は[正本ROADMAP](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/formal/real-hilbert-uniform-coercive-strong-limit/ROADMAP.md)。

## 歴史的記録 — ABQ2以前の本文（原文保持）

**この見出し以降の「最新」「現行」「Current」「OPEN」とSHAは各記述時点の履歴である。** ABQ2の「現在の正本は上記ABQ2」という文言も当時の状態を示す。現在の検証済み範囲は本追補による。以下の歴史的本文は削除・改変していない。

---

**Main-branch documentation mirror | 2026-10-29 JST.** Formalized four-dimensional Yang–Mills / genuine interacting Wilson SU(2) research in Lean 4 / pinned mathlib, by Hidetoshi Itakura.

## 最新の定理チェックポイント — 2026-10-31 JST · P4-Q2-PZ37ABQ2 (#6023)

**唯一のLean定理正本：** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。 [PR #6023](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6023) は **MERGED**、定理正本 HEAD は [`26632456e8c74d3f36453b4242a67cdbd9ae26a7`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/26632456e8c74d3f36453b4242a67cdbd9ae26a7)（squash SHA と完全一致）。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。

**厳密検証：** source HEAD `9efc3034670654289f3ddb147f23f7562b9ada33` に対する [exact-source CI #41132500130](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41132500130) は **11,010 / 11,010 SUCCESS**。変更 Lean 2ファイルの warning/error **0/0**。新規公開定理の `#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` **0件**、独立 completion receipt **SUCCESS**。

### CLOSED — 元の空間Wilson半重み・Perron代表を保持した真正四辺積分

MY の**実際の四辺単射** `e : Fin 4 ↪ L_H` と実際の全補集合 `R_(H,p) = {i : L_H // i ∉ Set.range e}` について、積Haarの座標再構成、選択座標・遠方座標の保存、有限積分の Fubini を Lean 4 で証明した（汎用5定理）。元の四辺以外の時間因子と、相互作用を含む**元の空間半重み × 正値のPerron代表**を保持して遠方積分 `R_(H,p,b,B)(x)` を定義し、その積分関数の可積分性、厳密正値性、および全有限 `H`（`H=0` を含む）、全真正プラケット `p`、`b≥0` での体積一様な相対比較

`exp(-56b) R(y) ≤ R(x) ≤ exp(56b) R(y)`

を証明した。これは**相対比較**であって、遠方重みの絶対質量に体積一様な正下界を与える主張ではない。

元の全one-slab核 `K_b(A,B)`・元の連続Perron代表 `Ω_b(A)` に対し、任意の連続な実数値四辺テスト `f` について

`∫ Ω_b(A) K_b(A,B) f(A∘e) dHaar_H(A) = hW_b(B) ∫ K_b⁽⁴⁾(x,B∘e) R_(H,p,b,B)(x) f(x) dμ⁴(x)`

を厳密に証明した。特に `f=1` では、元の物理的転送ノルム `t_(H,b)` による**真の質量**

`hW_b(B) ∫ K_b⁽⁴⁾(x,B∘e) R_(H,p,b,B)(x) dμ⁴(x) = t_(H,b) Ω_b(B)`

を得る。`Z_b^|L_H|` や `Z_b⁴` を物理ノルム `t_(H,b)` に代入していない。

定理ファイル：[汎用有限積再構成・Fubini](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/26632456e8c74d3f36453b4242a67cdbd9ae26a7/MGAP4D/MathlibAnalytic/FiniteProductEmbeddingAssemblyIntegral.lean)／[ABQ2 元の遠方Perron積分と真正核表示](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/26632456e8c74d3f36453b4242a67cdbd9ae26a7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalRemotePerronMarginalV5_PZ37ABQ2.lean)。Lean 4 の最終型照合障害は、遠方補集合の `Fintype` に使う `DecidableEq Link` の異なる実装が不透明な `Measure.pi` 内へ入り込むことにあり、同じ `Classical.propDecidable` への局所統一で解消した。元の模型・定理文は不変。

### OPEN — 真正GI・全物理Hilbert・4D連続極限

二つの相互作用 posterior に対する**符号付きGI応答の体積一様正下界**、他プラケットとの相殺・負tail制御、完全pair-Haar `A_p`／`G` の一様正下界、全物理Hilbert coercivity、同一endpoint E/F・共通positive-fine区間、任意深さ、H1–H4、OS/Wightman、4D連続体 Yang–Mills mass gap は引き続き **OPEN**。相対密度比較・正値性だけからこれらを推論しない。

**以下の過去の「最新」「OPEN」節は当時の歴史的チェックポイントとして保持する。現在の正本は上記ABQ2である。**

---

## 最新の定理チェックポイント — 2026-10-29 JST · P4-Q2-PZ37ABP (#6019)

**文書ミラー同期元：** 正本の文書 [PR #6020](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6020)、squash [`170030b4503ca5f7b50c6fd144a68195bee1d463`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/170030b4503ca5f7b50c6fd144a68195bee1d463)。

**唯一のLean定理正本：** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラー。[PR #6019](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6019) の検証sourceは [`85617e213deb0cb8101fde98f656d096b7f47899`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/85617e213deb0cb8101fde98f656d096b7f47899)、定理squashは [`d3879ed7352b68f68af0f1b467369f91cab11f19`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d3879ed7352b68f68af0f1b467369f91cab11f19)。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。

**検証結果：** [exact-source CI #40878551912](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40878551912) は依存関係を含む対象ビルド **11,007 / 11,007 SUCCESS**。新規Lean 2ファイルのwarning/error **0/0**、公開定理11件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、独立completion receipt SUCCESS、独立最終レビューPASS。CI実checkout `e6ec3bf2ee7006c103127bf2e4d7268d09dd607e` とsourceの全ファイルtreeは `ad2fcf3d82a810dbbbb8578d350ba4de000ca231` で完全一致。

### 全空間リンクの元の時間核から、真正四辺への制限を証明

実際の全空間リンク集合を `L_H`、MYの真正四辺embeddingを `ι_(H,p):Fin 4 ↪ L_H` とする。元の定義そのもの

`T_(H,b)(A,B)=periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2 b A B=∏_(e∈L_H) k_b(A_e⁻¹B_e)`

に対し、ABPは全有限 `H`、全真正プラケット `p`（`H=0`を含む）、全実数 `b` で

`[∫ T_(H,b)(A,B) f(A∘ι_(H,p)) dHaar_H(A)] / Z_b^|L_H| = [∫ K⁽⁴⁾_b(x,B∘ι_(H,p)) f(x) dμ⁴(x)] / Z_b⁴`

を証明した。有限リンク集合をembeddingの像と補集合へ実際に分割し、積測度の保存同型・分離積のBochner積分公式・選択座標の再添字付けを使用する。各遠方リンクの積分は、同じ目標配置 `B_e` を保って厳密に `Z_b`。補集合 `R_(H,p)` の時間因子質量は `Z_b^|R_(H,p)|`、全リンク質量は `Z_b^|L_H|` である。

一般補題はLeanのtotal integralの約束で任意の実数値 `f` に成立し、連続な物理テストについては通常の可積分性も別途証明した。ABO3の中心化半エネルギー伝送は、いまや**元の全リンク時間積分**として

`F_all(B):=[∫ T_(H,b)(A,B)(E_p(A)−1)/2 dHaar_H(A)]/Z_b^|L_H| = r_b⁴(E_p(B)−1)/2`

と同定され、`∫F_all² dHaar_H=r_b⁸/16`。指定した `0<b₀≤b≤b_max` では `∀H,p, ∫F_all²≥(b₀ exp(−2b_max)/4)⁸/16>0`。

証明：[有限積の重み付きembedding積分](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d3879ed7352b68f68af0f1b467369f91cab11f19/MGAP4D/MathlibAnalytic/FiniteProductWeightedEmbeddingIntegral.lean)、[ABP 元の全リンク時間Haar制限](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d3879ed7352b68f68af0f1b467369f91cab11f19/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAllLinkTemporalHaarRestrictionV5_PZ37ABP.lean)。

### 次のOPEN — 空間相互作用・Perron・符号付き受信器

閉じたのは**全リンク時間因子から真正四辺への制限**。元の全one-slab核は引き続き `spatialHalfWeight(A) · T_(H,b)(A,B) · spatialHalfWeight(B)` である。既存の一リンク作用変動・Perron Harnack・posterior密度の局所評価は保持する。その上で、空間半重みとPerron因子を残した四実リンクの遠方重みの厳密表示・体積一様比較、これと元の二つのinteracting posteriorの符号付き受信器との接続、全物理源の他プラケットとの相殺・負tail制御、一様な完全pair-Haar `A_p`／`G` 下界はOPEN。`Z_b^|L_H|` は全時間因子のHaar質量であり、真正物理転送ノルム `t` ではない。

ABK・ABL・ABMと旧no-goを保持する。全物理Hilbert coercivity、共通positive-fine区間、同一endpoint E/F、任意深さ、H1–H4、OS/Wightman、連続体4D Yang–Mills質量ギャップはOPEN。

**以下のABO以前の「最新」「次のOPEN」は当時の履歴として原文を保持する。** 現在の到達点は本節による。README/ROADMAP同期はdocs-onlyで、Lean CIを実行しない。

---

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


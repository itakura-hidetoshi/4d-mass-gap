## 検証済み定理 — ADB（2026-11-01 JST）

唯一の定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAP文書ミラーのみ。P4-Q2-PZ37ADBの定理PR #6118はMERGED（定理squash SHA `02a8b1ccd55e373d7faeb98bf39d50958f7dc4d0`）。既存ACZ/ADAと真正有限体積Wilson SU(2)模型、中心化Gauss-law物理源、FF受信器、正Perron代表、更新後transfer、元の二つのinteracting posterior・境界pair-Haar測度を変更しません。

### 真正Wilsonの無次元四成分信号と高次Haar残差

元のFC上界 `B`、真正四成分共分散二乗モーメント `S>0`、真正高次Haar残差平均 `Wbar>=0`、`tau=(exp(64*b)-1)^2>0` から、`u=16*S/B²`、`v=Wbar/B²` を定義します。すべて元の同じH・b>0・物理リンクeに属する量です。

- **無条件の物理的エネルギー配分**：`B²>0`、`0<u<=1`、`0<=v`、`u+v<=1`。これは既存ACKの厳密な分散恒等式 `Vbar=16*S+Wbar` と元のFC上界 `Vbar<=B²` により成立します。従って`Wbar<=B²-16*S`、`v<=1-u`。
- **ADA閾値の厳密無次元化**：元のHaar質量下界`F=u/(2-u)`、元のnegative-FC閾値比`C/(C+32*S)=tau/(tau+2*u)`。最適な内点閾値を選べる条件は`F>C/(C+32*S)` **iff** `u²>tau*(1-u)`。
- **元GI二乗平均証明書の厳密符号判定**：既存ACPとの同一物理模型内の等価として、`M_GI>0` **iff** `tau*v<4*u`。その否定`M_GI<=0` **iff** `4*u<=tau*v`もLean4で証明。二乗平均証明書と実signed GI応答を同一視しません。
- **具体的な条件付き十分性**：真の物理残差配分`v<=1-u`により、`u>tau/(tau+4)`（iff `tau*(1-u)<4*u`）なら`M_GI>0`。さらにADAの強い内点条件`u²>tau*(1-u)`だけでも`M_GI>0`。どちらの場合も既存ACOにより、同じ元二interacting posteriorのsigned GI応答が非零となるOPEN・正pair-Haar質量領域が存在します（すべて数値条件付き）。
- **障害**：`M_GI<=0`なら`4*u<=tau*(1-u)`かつ`u²<=tau*(1-u)`。また`u=1`を仮定した場合のみ`v=0`と正の平均証明書を導きます。これらは実signed GI応答の消滅を示しません。

### exact-source Lean4 verification／公理／境界

- PR #6118 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6118 — MERGED。変更は新規Leanファイル1件、3定義・27定理・27`#print axioms`、515行追加・削除0。既存Lean、元模型、theorem root、Lean pin、mathlib pin、workflowは無変更。
- 最終exact-source HEAD `4cc326a7c9bc87c227dc440a5b00f3edeb2e4e57` と定理squash SHA `02a8b1ccd55e373d7faeb98bf39d50958f7dc4d0` は同一Git tree `f65a2b373f9e04010729c6e126da31c153d58f8d`。
- PR exact-source CI #41285676155 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41285676155 — 11252/11252 Lean SUCCESS、27/27公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立completion receipt SUCCESS。
- マージ後push CI #41286073640 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41286073640 — 実Lean step／workflow／独立completion receiptいずれもSUCCESS。
- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 維持。docs-onlyではStrict Leanを起動しません。
- **未解決の物理条件**：真正Wilsonデータが`u>tau/(tau+4)`または`u²>tau*(1-u)`を実際に満たすことは未証明。体積に一様な正の下界、再構成、連続体4D質量ギャップも未証明。

### 次の定理課題 — ADC／固定結合と定数化（OPEN）

真正正結合`b0=log(3/2)/64`を固定すると`tau(b0)=1/4`、`tau/(tau+4)=1/17`。各H,eで`u(H,b0,e)>1/17`なら元GI二乗平均証明書が正となる条件付きの厳密定数閾値をLean証明する。同時に、H,eに依存しない下界`c>1/17`の存在は別の未証明課題として分離し、固定結合から一様性を偽って導かない。

---

## 検証済み定理 — ADA（2026-11-01 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAP文書ミラーであり定理正本ではありません。P4-Q2-PZ37ADA／定理PR #6115 はMERGED、squash SHAは `d85c361bb368ba97c784a0d0c84087ad0cee22e0`。ACY・ACZ以前の全形式定理・no-goを維持し、append-only／tighten-only／overwrite-forbidden／same-rootを遵守しています。

### 真正有限体積Wilson SU(2)・二閾値の閉形式最適化と障害

元の相互作用Wilson SU(2)、中心化Gauss-law物理源、FF受信器、正Perron ground代表、更新後transfer section `U_z`、同じ二つのinteracting posterior、元の境界pair-Haar測度 `ν_H` と元空間リンク `e` は一切変更なし。各有限体積H・b>0・真正eで、四成分共分散二乗モーメント `S>0`、元FC上界 `B`、高次Haar残差平均 `Wbar>=0`、`tau=(exp(64b)-1)^2>0`、`C=tau*B²`、`F=4S/(B²/2-4S)`、`Q=32S` を使います。

- **無条件の真正物理境界**：ACKの元の `S<=B²/16` とACNの正分母から `0<F<=1`、`0<C`、`0<Q` をLean4で証明。高信号Haar質量を独立確率モデルに置換していません。
- **全閾値に対する平方完成**：`g(delta)=(Q-delta)*(F-C/(C+delta))`、`t=sqrt(C*(C+Q)/F)`、`delta_star=t-C`。すべての`delta>0`に対して `g(delta_star)-g(delta)=F*(delta-delta_star)^2/(C+delta)>=0` をLean4で証明。最適値は厳密に `g(delta_star)=(sqrt(F*(C+Q))-sqrt(C))²`。微分や数値的近似ではなく正確な代数的証明です。
- **内点成立と真の必要十分条件**：元物理量の`F>C/(C+Q)`を満たせば `0<delta_star<Q`、ACZの`r_star=(Q-delta_star)/tau>0`、`delta_star+tau*r_star=Q`。さらに `Phi(delta)=g(delta)-tau*Wbar` とすると、`exists delta: 0<delta<Q and Phi(delta)>0` **iff** `F>C/(C+Q)` **and** `(sqrt(F*(C+Q))-sqrt(C))²>tau*Wbar` を元物理量に対して形式証明。
- **条件付き正値性**：この二つの明示的数値条件が真正Wilsonデータに成立すれば、ACI/ACOの元平均GI**二乗証明書** `M_GI>0`。既存ACOから元の同じ二interacting posteriorの実signed GI応答が非零となるOPEN・正pair-Haar質量領域が帰結します。`M_GI`とsigned GI応答そのものを同一視しません。
- **障害の完全分離**：`F<=C/(C+Q)`なら全`0<delta<Q`で `Phi(delta)<=0`。他方`M_GI<=0`かつ`F>C/(C+Q)`なら閉形式最適余剰`Phi(delta_star)<=0`。どちらもこの平均証明書に対するACZ閾値法の阻害であり、実signed GI応答の消失を含意しません。正の閉形式余剰なら既存ACPの厳密残差条件`tau*Wbar<64*S`も従います。
- 元真正Wilson模型について上記二つの厳密数値条件を**無条件に証明したものではありません**。体積Hに一様なcoercivity、OS/Wightman再構成、連続体4D Yang–Mills質量ギャップも依然OPENです。

### exact-source Lean4 CI・独立検証・正本保全

- 定理PR #6115: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6115 — MERGED。新規Leanファイル1件・2定義・19定理。追加486行・削除0行、既存Lean・物理模型・import root・workflow・pinは変更なし。
- 最終exact-source HEAD `c7f84d3469c54afbc9219ccca79542a498f53a5b` と定理squash SHA `d85c361bb368ba97c784a0d0c84087ad0cee22e0` のGit treeは `c6602053b4edb6e8b826bade1ebc7497a835e3c7` で完全一致。
- exact-source CI #41277266869: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41277266869 — workflow／11251/11251 Lean SUCCESS、19/19公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt job #124762791493 SUCCESS。
- マージ後push CI #41277632795: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41277632795 — squash HEAD上の実Lean step／workflow SUCCESS、独立completion receipt job #124763731246 SUCCESS。
- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 維持。docs-only Strict Leanは起動しません。

### 次の研究課題 — ADB（OPEN）

ADAで得た閉形式必要十分条件を、真正元Wilson模型のS、FC境界B、高次Haar平均Wbarの間の追加の**証明済み**関係へ還元できるかを検討する。特に`F>C/(C+Q)`の実モデルでの実現可能性、最適閉形式余剰の厳密正値性と必要な物理追加境界、有限H依存性を区別する。勝手な独立Haar模型・Perron一様下界・連続体質量ギャップの主張は導入しません。

---

## 検証済み定理 — ACZ（2026-11-01 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAP文書ミラーであり定理正本ではありません。P4-Q2-PZ37ACZ／定理PR #6112 はMERGED、定理squash SHAは `fcc93417cca1e50af56543777bad74b857547b23`。ACY以前の全Lean定理・no-goを保持し、append-only／tighten-only／overwrite-forbidden／same-rootを維持しています。

### 元Wilson受信器の残差・Perron判別量二閾値の最適化

有限体積相互作用Wilson SU(2)、中心化Gauss-law真正物理源、元FF受信器、正Perron ground代表、更新後transfer section、同一の二interacting posterior、真正境界pair-Haar測度 `ν_H` と元空間リンク `e` は一切変更していません。各有限H、b>0、eについて、四成分共分散二乗モーメント `S>0`、元FC上界 `B`、高次Haar残差平均 `Wbar`、真正指数差 `tau=(exp(64b)-1)^2>0`、`C=tau B²`、ACYの元高信号領域Haar質量下界 `F=4S/(B²/2-4S)>0` を用います。

- ACYの真正同一境界上の包含条件 `delta+tau*r<=32S` から、任意の `0<delta<32S` に対して `r_max(delta)=(32S-delta)/tau>0` を厳密定義し、`delta+tau*r_max=32S` を証明。許容される任意の `r` は `r<=r_max`。`F-C/(C+delta)>=0` なら、固定deltaのACY moment-overlap surplusはこの選択で最大になります。真のPerron²因子を削除しません。
- **一変数に還元した元の物理十分条件**：`Phi(delta)=(32S-delta)*(F-C/(C+delta))-tau*Wbar`。`0<delta<32S` かつ `Phi(delta)>0` が実物理量で成立すれば、ACOの元平均GI**二乗証明書**`M_GI>0`。さらに同一の真正two-posterior signed GI応答が非零のOPEN・正pair-Haar質量領域が成立します。これらは実模型で無条件に成立したとは主張しません。
- **逆向きの量的障害**：真正`M_GI<=0` なら、全適格`0<delta<32S`で`Phi(delta)<=0`。`delta=16S` に固定した分数型の物理十分条件もLean4で証明。正の最適化余剰には`tau*Wbar<32S*F`が必要で、十分とはしていません。
- **元FC残差上限を直接使う別の経路**：ACYで無条件に証明した `Rcap=B²-8S>0` と `nu_H(High)>=F` を保持。`delta_FC=32S-tau*Rcap>0` かつ `F>C/(C+delta_FC)` が元物理量で確かめられれば`M_GI>0`、真正signed GIのOPEN・正Haar質量領域が存在します。元`M_GI<=0`なら`F<=C/(C+delta_FC)`という必要な障害も形式証明しました。
- この成果は元の有限H,b,eにおける**条件付き物理数値判定**です。真正元Wilson模型での`Phi>0`、`delta_FC>0`、`F>C/(C+delta_FC)` の無条件成立、体積一様coercivity、OS/Wightman再構成、連続体4D Yang–Mills質量ギャップはいずれもOPEN。平均GI二乗証明書と実際のsigned GI応答は同一視しません。

### exact-source CI・正本保全

- 定理PR #6112: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6112 — MERGED。新規Leanファイル1件・2定義・14定理。追加390行・削除0行、既存Lean／物理模型／import root／workflow／pinの変更なし。
- 最終source HEAD `ec90952440bbecf1e0a5a7d8d6536eeaf12a99e6` と定理squash SHA `fcc93417cca1e50af56543777bad74b857547b23` のGit treeは `0736a73d34fc4dd0a96042a92e50de16f9a20cbc` と完全一致。
- exact-source CI #41275287127: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41275287127 — workflow／Lean実検証11250/11250 SUCCESS、14/14の公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更warning/error 0/0。独立MCP completion receipt job #124757333145 SUCCESS。
- マージ後push CI #41275728172: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41275728172 — squash HEAD上のLean step／workflow SUCCESS、独立completion receipt job #124758367406 SUCCESS。
- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は維持。文書同期はdocs-onlyでありStrict Leanは再起動しません。

### 次の研究課題 — ADA（OPEN）

残った一変数`delta`の閉形式最適化をLean4で追加形式化。解析上、内部候補は`delta*=sqrt(C*(C+32S)/F)-C`、`r*=(32S-delta*)/tau`。**この平方根最大化自体はACZの14定理には含まれていない**ため、候補の適格性`0<delta*<32S`、境界障害、真正モデルでの判定を別途証明する。元の物理模型、Perron重み、独立性なしのHaar法は保持する。

---

## 検証済み定理 — ACY（2026-11-01 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAPのみの文書ミラーであり定理正本ではありません。P4-Q2-PZ37ACY・定理PR #6109 はMERGED、squash SHA `a06b288f113227fa28da01669ca3f0021306206f`。ACX以前の全定理・no-goを保持し、append-only／tighten-only／overwrite-forbidden／same-rootを維持しています。

### 真正同一境界の四成分高信号・高次Haar低残差の交差

元の有限体積相互作用Wilson SU(2)、中心化Gauss-law物理源、元FF受信器、正Perron ground代表、真正transfer norm、更新後のjoint Perron半密度を分母に持つ元transfer section `U_z`、元の二つの相互作用posterior、境界対とそのpair-Haar測度 `ν_H` を変更していません。全有限H・b>0・元の真正空間リンクeについて、元の受信器四成分エネルギー `A(z)²`、高次SU(2) Haar残差 `W(z)`、真正共分散二乗モーメント `S>0`、受信器FC上界 `B_b` を使用します。

- ACT/ACUの真正Perron二乗重み付き局所判別量 `w_b(z)=P_z²[16A_U(z)²−τ(b)W_U(z)]` は **同じ元受信器エネルギー**を用いて `w_b(z)=16A(z)²−τ(b)W(z)` と厳密一致。双方に同じ境界依存のPerron²因子を保持し、独立Haar法を導入しません。
- 真正の元境界対上で `High={A²>2S}`、`Low_r={W<r}`、`Good_r=High∩Low_r` を定義し、すべてOPENと証明。元の受信器FC分散配分 `4A(z)²+W(z)≤B_b²` から、**High上では必ず** `W(z)<B_b²−8S`。ACNより `Rcap=B_b²−8S>0` を無条件に証明し、`Good_Rcap=High` という全配置での集合等式も証明しました。
- さらに既存ACNの厳密な元pair-Haar量的下界 `F=4S/(B_b²/2−4S)>0` を保持し、`F≤ν_H(Good_Rcap)` を無条件に証明。このOPEN領域上で `w_b(z)>32S−τ(b)(B_b²−8S)`。ただし**右辺の正値性そのものは真正Wilsonデータについて未証明**です。
- **新規の一般残差閾値の交差質量評価**：任意の `r>0` について元の受信器高次残差平均 `Wbar=∫W dν_H` だけを使って `r ν_H(High)≤r ν_H(Good_r)+Wbar`、従って `rF−Wbar≤rν_H(Good_r)` をLean4形式証明。独立性・濃度仮定・Perron密度一様下界は不要。右辺への正の下界には実モーメントの追加関係 `Wbar<rF` が必要で、これを実模型で仮定なしに示したとはしていません。
- 元のACW閾値領域 `T_δ={z:δ<w_b(z)}` は `δ≤32S−τ(b)r` のとき `Good_r⊆T_δ`。よって `rF−Wbar≤rν_H(T_δ)`。実物理入力で `rF−Wbar>r C_b/(C_b+δ)` かつ `0<δ≤32S−τ(b)r`、`C_b=τ(b)B_b²` が成立すれば、元の平均GI**二乗証明書**が正となり、従来ACOにより真正のsigned二posterior GI応答が非零のOPEN・正Haar質量領域が導かれます。**この十分条件の真正Wilson模型での成立は未証明**です。
- 逆に元の平均GI二乗証明書が非正なら、上記すべての適格`r,δ`について `rF−Wbar≤r C_b/(C_b+δ)` が必要。実際のsigned GI応答の消滅、H一様な下界、H1–H4、OS/Wightman再構成、連続体4D Yang–Mills存在・質量ギャップは主張しません。

### 定理正本・exact-source Lean4 CI／独立再検証

- 定理PR #6109: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6109 — MERGED。新規Leanファイル1件・5定義・19公開定理。旧Lean・物理模型・root・workflow・pinの変更なし。最終exact-source HEAD `617473379cb8def1ce582ed66f1bc825f34adaa2`、squash SHA `a06b288f113227fa28da01669ca3f0021306206f` のGit treeはともに `83562463c9c6020438c2b44fe5077bbfdc63dbaf` と完全一致。
- exact-source CI #41270835764: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41270835764 — workflow／11249/11249 Lean／独立completion receipt SUCCESS、19/19公理は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0。
- マージ後push CI #41271160320: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41271160320 — head=squash、workflow／実Lean step／11249/11249 SUCCESS、19/19公理標準3のみ、`sorryAx`なし、変更Lean warning/error 0/0。独立MCP completion receipt job #124744914566 もSUCCESS。
- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は変更なし。

### 次の課題 — ACZ（OPEN）

真正交差領域のモーメント下界と既存ACW/ACXの閾値Haar質量判定を、`r,δ` の最適選択・局所残差分布の追加情報により鋭くする。各有限H,b,eの本来のPerron代表、元受信器、元の二posteriorと境界pair-Haar法を保持し、未証明の正値性・独立Haar模型・体積一様coercivityを導入しません。

---

## 検証済み定理 — ACX（2026-11-01 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAPの文書ミラーであり、定理正本ではありません。P4-Q2-PZ37ACX／定理PR #6106 はMERGED、定理squash SHAは `d1654e1bd5de789397dd659ed3753472b9ed484d` です。ACW以前の全形式定理とno-goを保持し、append-only／tighten-only／overwrite-forbidden／same-rootを維持しました。

### 真正Perron閾値Haar質量の二側分布評価

有限体積・相互作用Wilson SU(2)の元FF受信器、中心化Gauss-law物理源、正Perron ground代表、真正transfer normと更新後のjoint Perron半密度を分母に持つtransfer section `U_z`、二つの実interacting posterior、元境界対と元pair-Haar法 `ν_H` は変更しません。全有限H、b>0、真正空間リンクeで、ACT/ACWの本来のPerron二乗重み付き局所判別量 `w_b(z)=P_z²[16A_U(z)²−τ(b)W_U(z)]`、平均 `D_b=∫w_b dν_H=64S−τ(b)Wbar`、閾値領域 `T_δ={z:δ<w_b(z)}`、その質量 `m_δ=ν_H(T_δ)` を用います。

- 元のFC境界上界を `Ucap_b=4B_b²`、負側上界を `C_b=τ(b)B_b²` とすると、**元の物理的wに対して無条件に** `−C_b≤w_b(z)≤Ucap_b` が成立。任意実数δについて `−C_b+(δ+C_b)m_δ≤D_b≤δ+(Ucap_b−δ)m_δ` をLean4で厳密に形式証明しました。
- `0<δ<Ucap_b` なら真正の同じpair-Haar測度における**鋭い両側分布評価** `(D_b−δ)/(Ucap_b−δ)≤m_δ≤(D_b+C_b)/(δ+C_b)` が成立。左辺が負の場合は非自明な質量下界を主張せず、両分母の正値条件を保持しています。元Perron因子を積分から除去せず、独立Haar法へ置き換えていません。
- `δ<D_b` なら真正閾値集合はOPENかつ元pair-Haar質量が厳密正。さらに`δ≥0`なら同じ真正境界対に更新後transfer四成分Haarエネルギー正のwitnessが存在することを証明しました。
- **物理入力に直接還元した下界**：元高次SU(2)Haar残差の平均 `Wbar≤B_b²` を既存ACRの真正受信器FC上界から無条件に証明。`L_b=64S−τ(b)B_b²≤D_b` とすると、`δ<L_b` が元模型で検証できる場合に `(L_b−δ)/(4B_b²−δ)≤m_δ`、かつ`m_δ>0`が従います。`δ<L_b`の物理的成立は未証明です。
- **非正平均GI証明書の定量的阻害**：もし元の`M_GI≤0`なら、全`δ>0`に対して `m_δ≤τ(b)B_b²/(δ+τ(b)B_b²)`、さらに `64S≤τ(b)B_b²` が必要です。これは正の平均GI**二乗証明書**に関する阻害であり、実際のsigned two-posterior GI応答の消滅を主張しません。
- 正の平均判別量 `D_b>0`、元Wilsonの正側質量閾値達成、体積一様coercivity、H1–H4、OS/Wightman再構成、連続体4D Yang–Mills存在・質量ギャップはいずれも依然OPENです。新しい数値下界や残差優越を仮定していません。

### exact-source Lean4 CIと正本保全

- 定理PR #6106: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6106 — MERGED。新規Leanファイル1、2定義・15公開定理、既存Lean／root／workflow／物理模型／pinは不変。source HEAD `a21b7a7b6b52addb084e9be1081ced79e2586e3a` とsquash SHA `d1654e1bd5de789397dd659ed3753472b9ed484d` のGit treeは共に `c525a438bf955a5787877faaacbd971fb4bc9d48` で完全一致。
- exact-source PR CI #41268428773: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41268428773 — workflow／Lean実ビルド／独立completion receipt SUCCESS、11248/11248、15/15公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0。
- マージ後独立push CI #41268785456: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41268785456 — head=squash、workflow／Lean job／実Lean step SUCCESS、11248/11248、15/15公理標準3のみ、`sorryAx`なし、変更Lean warning/error 0/0。独立MCP completion receipt job #124738066988 もSUCCESS。
- Pin維持：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

### 次の課題 — ACY（OPEN）

ACXの元物理モーメント由来の閾値Haar質量両側評価を使い、局所四成分正信号領域と高次残差の共起・交差を元の境界pair-Haar測度上で定量評価します。元Perron代表／更新後transferの局所情報と平均を分離し、`m_δ`の下界を改善できるか、または具体的阻害条件を特定します。未証明の一様下界・独立Haar置換・連続体質量ギャップ主張は導入しません。

---

## 検証済み定理 — ACW（2026-11-01 JST）

唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAPの文書ミラーであり定理正本ではありません。P4-Q2-PZ37ACW／定理PR #6103 はMERGED、定理squash SHAは `f2308ed9706e29410dced3f350d03f7135613569`。ACS・ACT・ACU・ACV以前の全証明・no-goを保持し、append-only／tighten-only／overwrite-forbidden／same-rootを維持しました。

### 真正Perron重み付き閾値領域と補集合のFC負寄与比較

変更していない有限体積相互作用Wilson SU(2)模型、中心化Gauss-law物理源、元FF受信器、正Perron ground代表、元transfer norm、更新後joint Perron半密度に依存する元transfer section `U_z`、二つの真正interacting posterior、元境界対と元pair-Haar法 `ν_H` を保持します。全有限H・b>0・真正リンクeにおいて、ACT/ACUの真の局所判別量 `w_b(z)=P_z²[16A_U(z)²−τ(b)W_U(z)]` と元受信器FC上界 `B_b` を用います。

- 新しく元の負側FC予算 `C_b=τ(b)B_b²≥0` と閾値領域 `T_δ={z:δ<w_b(z)}` を定義し、`T_δ` がOPENであることを証明。`δ≥0` なら同じ元境界配置で `T_δ` 上は真正四成分振幅`A_U(z)²>0` と `d_b(z)>0` が成立します。未証明のPerron密度一様下界は不要です。
- 元の正負寄与 `Eplus=∫max(w_b,0)dν_H`、`Eminus=∫max(−w_b,0)dν_H` に対し、`m_δ=ν_H(T_δ)` として**両側の定量不等式** `δm_δ≤Eplus`、`Eminus≤C_b(1−m_δ)` をLean4で証明。従って真正平均判別量 `D_ACT=Eplus−Eminus≥δm_δ−C_b(1−m_δ)` と、`16M_GI≥κ(b)[δm_δ−C_b(1−m_δ)]` が成立します。
- **直接判定できる十分条件**：`δ>0` で元pair-Haar質量が `m_δ>C_b/(C_b+δ)` なら、元平均GI**二乗証明書**`M_GI>0`。従って既存ACOの真正二posterior GI応答が非零のOPEN正Haar質量集合が成立します。逆に`M_GI≤0`なら、すべての`δ≥0`で `δm_δ≤C_b(1−m_δ)` が必要です。これらは実模型の符号について無条件な結論ではありません。
- **新たな条件付き直接Haar質量下界**：元ACO二乗GI証明書のFC上界から`w_b(z)≤4B_b²`を無条件に証明。`D_ACT>0`が元模型で確認された場合には、`T_{D_ACT/2}` がOPEN、`8B_b²−D_ACT>0` かつ `D_ACT/(8B_b²−D_ACT)≤ν_H(T_{D_ACT/2})` です。
- 証明書`M_GI`を実際のsigned two-posterior GI応答そのものと同一視していません。真正Wilson模型で`D_ACT>0`または上記領域質量閾値を満たすかは依然**OPEN**です。全体積一様coercivity、H1–H4、OS/Wightman、連続体4D Yang–Mills存在・質量ギャップも主張しません。

### exact-source Lean4 CI・定理正本保全

- 定理PR #6103: https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6103 — MERGED。新規Lean定義2、公開15定理、新規Leanファイル1件のみ、既存Lean・model・workflow・theorem root変更なし。
- 定理exact-source HEAD `37c0f3e5262b594f6cee243993a08e5e3ec89689`、squash SHA `f2308ed9706e29410dced3f350d03f7135613569` のGit treeは両方 `7fb83bb9952db1b0e58d305d4910bed8f60760a6` と完全一致。
- exact-source PR CI #41267094810: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41267094810 — workflow・実Lean step・独立completion receipt SUCCESS。依存11247/11247、15/15公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0。
- マージ後独立push CI #41267548975: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41267548975 — head=squash、workflow/Lean job/実Lean step SUCCESS、11247/11247、15/15公理標準3のみ、`sorryAx`なし、変更Lean warning/error 0/0。独立MCP completion receipt job #124734422977 もSUCCESS。
- PinはLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` のまま。

### 次の課題 — ACX（OPEN）

元のboundary Perron密度、更新後transferの真正Haar四成分と高次残差、境界pair-Haar測度から`m_δ`を直接評価し、`m_δ>C_b/(C_b+δ)`を実際に満たすか、あるいはその阻害がどこにあるかを調べます。新しい体積一様下界・残差優越・独立Haar模型を置かず、元の各H,b,eでの局所情報と符号を区別します。

---

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

# MGAP4D ROADMAP — ACI検証済み、次はACJ

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

# MGAP4D ROADMAP — ACH検証済み、次はACI

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

# MGAP4D ROADMAP — ACF検証済み、次はACG

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

# MGAP4D — 定理正本ロードマップ追補（2026-10-31 JST／P4-Q2-PZ37ACC）

**唯一の定理正本：** `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラー。[ACC定理 PR #6047](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6047) **MERGED**。定理squash `e8803e0fcc69d051953d532ed246ff9467c5d616` とマージ直後の正本HEADを完全一致で確認。exact-source `460d15a44e7b428a5a632f7e37e6132f9050169c`、実CI checkout `87a1db0829b27919a9aeb7d9768bc33d2e04fe46`、定理squashの全Git treeは `ef26f66ec383060030c307bcc00decd117b98942` に完全一致。既に統合されたACB [#6046](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6046) とその文書履歴を保持し、この拡張をACCとして接続した。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。

**検証：** [CI #41174163063](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41174163063) workflow・build job・Lean step **completed / SUCCESS**、Lean **11,181 / 11,181 SUCCESS**。新規4 Leanファイル・1,208行・48公開定理・48件の `#print axioms`。公理依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内、`sorryAx`なし、変更warning/error **0/0**。独立completion receipt [job #124459070461](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41174163063/job/124459070461) とpublish stepは **completed / SUCCESS**、同じexact-source SHAと `source_result=success` を確認。全文・imports・依存署名・固定APIを独立レビューし、既存Lean・元模型・仮定・公開root・workflowを変更していない。

## CLOSED — 元の全GIの直接共分散評価

`u=exp(32b)`、`l=exp(-32b)`、`v=Var(F_z)`、`C=Cov(F_z,E)`、`D=v-4C²≥0` とする。全有限H、b≥0、元の任意Gauss-law物理源について

`|Δ_GI+b*(u+l)*C|≤(b/2)*(u-l)*sqrt(v)`

を証明。完全なABY正負比較、ABZのM_s−M_{-s}=−4bsC、ACAの全不整合上界から導く。内側長方形や小tail仮定なし。s²=1の直接下界L_s=−b(u+l)sC−(b/2)(u−l)sqrt(v)は、同じABX rectangle Rの外側領域でs=R.signとしたとき、同じB_sを使うACA rectangle marginを支配する。

## CLOSED / CONDITIONAL — 実回帰欠損と真正Perron条件

B_s=b(sqrt(v)+2sC)に対しB_sB_{-s}=b²D。sC≤0なら全M_{-s}≤b sqrt(D)、元posterior全負tail≤exp(32b)b sqrt(D)。

b>0、r=exp(-64b)では `L_s>0 ↔ [sC<0 ∧ (1+r)²D<4rv]`。これは直接下界の正値性の必要十分条件で、元GIの正値性には十分条件。元GI自体の正値性の必要条件ではない。

真正F=C₀−PU、P>0から、同じ条件は `sCov(U,E)>0` と `(1+r)²D_U<4rVar(U)` に同値。正のP²が相対条件から消える一方、真のPerron半密度とtransfer normはUおよびGI振幅に残る。元中心化源がこの条件を満たすことは未証明。

## CLOSED — 真正中心化源のゲージ対称性と全配置障害

同じ真正中心ゲージΓ_eを左右の元境界に作用させ、P(Γ_e z)=P(z)、F_{Γ_e z}(g)=F_z((-I)g)、Uも同じ輸送を証明。真のPerron物理代表、元kernel、literal右リンク更新を維持する。F/U共分散は反転、分散・回帰欠損は不変、全M_sとM_{-s}、B_sとB_{-s}が交換する。

全有限H、b>0で**あるABX-active link e**について `∀s=±1,∀θ<1,¬[∀z,M_{-s}(z)≤θM_s(z)]`。各向きには正の全不整合を持つ配置がある。全linkに拡張しない。選択した外側領域や配置ごとの向きは排除しない。固定posteriorアンカーを変換しないためGI自体の符号反転は主張しない。

## CLOSED / CONDITIONAL — 元外側pair-Haarへの向きに依存しない接続

`L_abs=b(u+l)|C|−(b/2)(u−l)sqrt(v)≤|Δ_GI|`。元外側configuration pair-Haar λ_Hの任意可測Aに対し、全z∈AでL_abs≥δ≥0なら `∫Δ_GI²dλ_H≥λ_H(A)δ²`。共通の向き・傾き・内側長方形は不要。補助二コピーSU(2) Haarとの同一視はない。

## OPEN — 次段階P4-Q2-PZ37ACD

1. 元中心化源の真正U_zのCov・Var・D_Uを選択した元外側Haar領域で解析し、相対欠損条件と正の絶対GI marginを実模型から証明する。
2. 領域質量・振幅のH,b依存を定量化し、固定support cylinder、体積一様性、遠方相殺を目指す。元Haar中心化を固定リンク平均ゼロやPerron中心化と混同しない。
3. 元外側二乗GI積分を真Gram／Rayleigh下界へ接続する。実際の閾値充足・一様性は未証明。
4. ABS、ABM／PZ37ZA障害を保持。全物理Hilbert coercivity、common fine-positive、同一endpoint E/F、H1–H4、OS/Wightman、4D連続体Yang–Mills mass gapはOPEN。

**以下のACB以前の履歴は完全保存。この追補が最新到達点。docs-only同期では定理Leanを変更しない。**

---
> **main文書ミラー（ACB同期）**：唯一の定理正本は [formal/real-hilbert-uniform-coercive-strong-limit](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)、確認済み正本文書HEAD `9dde4d0174f85292f5b17eefcdef8e2cf2502701`（[正本docs #6048](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6048)）、定理squash `8721fe3bb5dc283ac55f67f27a254db18581973f`（[Lean PR #6046](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6046)）。ここではACBの検証記録だけを文書として反映し、Lean定理はmainに移さない。

# MGAP4D — 定理正本ロードマップ追補（2026-10-31 JST／P4-Q2-PZ37ACB）

**定理正本** `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラー。[ACB #6046](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6046) **MERGED**。定理squash／マージ直後正本HEAD `8721fe3bb5dc283ac55f67f27a254db18581973f`、exact-source `8356fc4a72052527d8b446f8b16574fb5a286e60`、共通tree `2befd0cf522bf3fd32fd3e8f4953683a763ff73b`。[CI #41173509336](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41173509336) **11,177/11,177 SUCCESS**、新規2 Lean葉／19定理／全19公理依存標準三公理のみ／`sorryAx` 0／変更warning・error 0/0、独立[receipt #124457218765](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41173509336/job/124457218765) SUCCESS。Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6不変。

## CLOSED — 実物理Perron断面の分散正値と欠損証明書

ABXの同じ外側領域で `v=Var(U_z)>0`。真正SU(2) Haar `Var(E)=1/4` と同じ元物理源について、

```text
C=Cov(U_z,E),  D=v-4C²≥0,  ρ=2sC/sqrt(v),
-1≤ρ≤1,  1-ρ²=D/v,
B=bP(sqrt(v)-2sC)=bP sqrt(v)(1-ρ).
```

さらに、`b>0`なら `B<T_R ↔ 1-ρ<T_R/(bP sqrt(v))`。`sC≥0`という**明示的方向条件**から `B sqrt(v)≤bPD` と実際の全interacting-posterior負tail `≤exp(32b)bPD/sqrt(v)`。同じABX閾値について `bPD<T_R sqrt(v)` が**別途証明されれば**元GI `sΔ_GI(z)>0`。逆向き `sC≤0` と `T_R≤bP sqrt(v)` はACA残差族での正の証明書を排除するが、実GIのno-goではない。全て元Wilson核・Perron・源・二posterior・元の外側pair-Haarを保持する。

## OPEN — 次段階P4-Q2-PZ37ACC

1. **真正Uのエネルギー方向の係数と直交残差。** 元のABRのsource遠方重み `S_B`、Perron重み `R_B`、ABSの正の補正 `V_B=S_B/R_B` と更新後joint Perron分母を保持して、`Cov(U_z,E)` と `D_z=Var(U_z-4Cov(U_z,E)E)` を真正積分から定量評価する。spatial Haar中心化を固定リンク平均零へ置換しない。
2. **実モデルでの厳密閾値の成立。** 単に`D≥0`や`ρ≥0`を使うだけでは不足。`sC_z≥0` と `bP_zD_z<T_R sqrt(v_z)` の成立、または既存ACAの必要十分条件 `B_s<T_R` を元の源で独立に証明する。MQの異なるRiesz商の局所性をUへ移植しない。
3. **体積一様性と遠方相殺。** 固定support cylinder、元外側pair-Haar事象質量、ABXの`A,V,η,κ`、実PとvのH依存、全負tail、他プラケットの符号付き補償を評価し、真Gram/Rayleigh一様下界へ進む。ABV固定cap`1/64`をABXのVに流用しない。
4. **下流の独立ゲート。** 全物理Hilbert coercivity、共通positive-fine、同一endpoint E/F、任意深さH1–H4、OS/Wightman、4D連続体Yang–Mills mass gapは未証明。ABS／ABM／PZ37ZAのno-go・旧履歴・fixed pins／公開rootを保持する。

GitHub MCPで正本exact HEAD、変更Lean全文・imports／依存署名／固定mathlib API、exact-source workflow／job／Lean step、公理・独立receipt、source/squash tree一致を確認した。今回のdocs-only同期ではStrict Leanを追加起動しない。

**以下のACA以前の節は当時の履歴として完全に保存する。**

---

> **main文書ミラー（ACA同期）**：定理の唯一の正本は [formal/real-hilbert-uniform-coercive-strong-limit](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。確認済み正本HEAD `f3cb167e576250dd55b630cec1d448cbadf90a6d`（[正本文書同期 #6044](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6044)）。定理squashは `055efd930b9c45a3894282c9a6023db2abe3a753`。このmain文書更新はLean定理を追加・変更せず、以下のACA検証記録を鏡映する。

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
# main文書ミラー更新 — P4-Q2-PZ37ABZ（2026-10-31 JST）

このmainは文書ミラー。唯一の定理正本は [formal/real-hilbert-uniform-coercive-strong-limit](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)、現在の正本HEADは `15783bdb15a9df34e45dacf2629f9c25bac70ba2`（[README・ROADMAP同期 #6041](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6041) MERGED）。ABZ定理squashは `bf7d9575a7f3f25e041b901e00a72f3034ccd244`。その後の正本変更はREADME・ROADMAPへの追記のみ。以下は正本の検証済みABZ追補の文書ミラーであり、定理の正本をmainへ移していない。

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


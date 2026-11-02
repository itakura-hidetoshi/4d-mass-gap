## 検証済み定理 — ADV（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADV定理PR [#6175](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6175) はMERGED、定理squash SHA `1855cbbdc96f22bb8e1cf973c1156ecf4bc34dd7`。元interacting Wilson SU(2)、中心化Gauss-law源、FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootは不変更。

### 真正SU(2)のS³左作用の等長性・推移性と全中心Haar球質量

- **元ADKの弦距離の厳密左不変性**：実物理Wilsonエネルギーの `d_J(g,h)^2=2 E(g⁻¹h)` と真正SU(2)群則から、任意`a,g,h`で `d_J(ag,ah)=d_J(g,h)` をLean4無条件証明。別の距離・物理モデルへの置換なし。
- **球面上の真正SU(2)作用の等長性と推移性**：ADUの `T_g(x)=Φ(g*Ψ(x))` について単位作用・合成作用・`g⁻¹`による左右逆作用、全`x,y`で `dist(T_g x,T_g y)=dist(x,y)` を証明。各`g`の具体的な`S³ ≃ᵢ S³`を構成し、任意の球面`x,y`間には `T_g x=y` を満たす元のSU(2)要素`g`が存在することを形式化。
- **球集合の移送と元Haar球質量の中心不変性**：全半径`r`で `T_g⁻¹(ball(T_g a,r))=ball(a,r)` を証明。ADUの真正元SU(2) Haar押し出し`ν_G`と左作用による測度保存・推移性から、全球面中心`a`について `ν_G(ball(a,r)).toReal=m(r)` を無条件でLean4証明。ここで`m(r)`はADMの元normalized SU(2) Haar半径質量であり、固定mathlibの別の球面測度ではない。
- **残存の独立測度obstruction**：固定mathlib `Measure.toSphere(volume)` を確率正規化した`σ̂`が各`T_g`で不変であることは未証明。従ってADUの一意性を使った`ν_G=σ̂`、元SU(2) Haarの無条件半径依存明示下界、全H一様強制性、連続体4D Yang–Mills質量ギャップは未達成。次は各`T_g`を実4次元線形直交変換として延長し、`toSphere`の不変性へ接続する。

### exact-source Lean4・公理依存

- 新規10定理・`#print axioms`10件。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41382808932](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41382808932) は **11,271/11,271 SUCCESS**。変更Lean warning/error 0/0、全10件は標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` なし、独立completion receipt SUCCESS。
- 定理source/test-merge/squash Git treeは `dae10eff95da311a5eb0ec8b8559bd98fc166a11` で一致。docs-onlyではStrict Leanを再実行しない。default mainにはLean定理本体をコピーしない。

---

## 検証済み定理 — ADU（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADU定理PR [#6172](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6172) はMERGED、定理squash SHA `7a7b01f8083d884d62c08872cf37329600b6f538`。元のinteracting Wilson SU(2)、centered Gauss-law物理源、FF受信器、Perron/transfer、二interacting posterior、boundary pair-Haar、定理rootは不変更。

### 真正SU(2) HaarのS³押し出し、左作用不変性、Haar一意性への還元

- **元の位相による真正Homeomorph**：ADSの元SU(2)↔S³双方向写像とADTの元`d_J`-球面Euclidean距離一致を利用し、ADKの元`J`連続性・SU(2)コンパクト性・S³のHausdorff性から `Φ : SU(2) ≃ₜ S³` をLean4証明。正逆写像ともBorel可測。
- **元Haarを保持した球面確率測度**：元normalized compact Haar `μ_G` の真正押し出し `ν_G = Measure.map Φ μ_G` を定義し、確率測度性、`Φ`による測度保存、`Ψ`による元Haarの厳密復元、元ADMの半径球質量 `m(r) = ν_G(ball(Φ(1),r)).toReal` を無条件でLean4証明。有限群Haar・別の任意分布への置換はない。
- **真正SU(2)作用と測度不変性**：球面上の作用 `T_g(x)=Φ(g*Ψ(x))` を元の群演算から構成し、各`T_g`の連続性・`MeasurePreserving T_g ν_G ν_G` をLean4証明。さらに、この元SU(2)作用に対して不変な**任意の球面確率測度**は`ν_G`と等しいことを、固定mathlibの確率Haar測度一意性から証明。
- **別個の標準球面測度と残存obstruction**：固定mathlib `Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin 4)))` を独立に確率正規化した`σ̂`を定義。`∀g, Measure.map (T_g) σ̂ = σ̂` という**具体的な作用不変性を前提**とすれば `ν_G=σ̂` が成立する条件付き定理を形式証明。しかしこの作用不変性そのものはADUでは未証明。元SU(2) Haarに対するADQの無条件半径依存数値下界、全H一様強制性、連続体Yang–Mills質量ギャップは未達成。

### exact-source Lean4・公理依存

- 新規14定理・`#print axioms`14件。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41374989708](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41374989708) は **11,270/11,270 SUCCESS**、変更Lean warning/error 0/0、公理依存は14件すべて標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし。[定理マージ後push CI #41375511861](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41375511861) もSUCCESS、独立completion receipt SUCCESS。
- 定理source/squash Git treeは `7d67e47e31fe5f3cb7ff2fbccff0a40fc3252f5b` で一致。次のADVでは固定球面測度 `σ̂` が真正SU(2)作用に対して不変であることを、実4次元の正規直交作用と固定mathlibの`toSphere`との整合性から証明する。docs-onlyでStrict Leanを実行しない。

---

## 検証済み定理 — ADT（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADT定理PR [#6169](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6169) はMERGED、定理squash SHA `1e5ceac8e72c3f0b83e31b35e0c253ef2a0918e8`。元有限体積interacting Wilson SU(2)、元centered Gauss-law源、FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootは不変更。

### 元SU(2)弦距離とS³ Euclidean距離の真正等長性

- **真正相対トレース内積同定**：ADRで既に証明した元SU(2)の第1列からの厳密な2×2行列復元を使用し、`Re Tr(gᴴh)=2*⟪V(g),V(h)⟫_ℝ` を固定mathlibの元行列積と複素数計算でLean4証明。元のnormalized SU(2)相対トレースkernelが`EuclideanSpace ℝ (Fin 4)`上の実内積に厳密一致する。新規の代替ゲージ・カーネルは導入しない。
- **元ADKの8実次元Wilson特徴と4実次元球面の厳密距離一致**：ADKの真正 `J` の単位ノルム、ADRの4実次元 `V` の単位ノルム、両者の内積一致から `d_J(g,h)^2=‖V(g)-V(h)‖²`、非負性から**`d_J(g,h)=dist(Φ(g),Φ(h))`** をLean4で無条件証明。ADSで構成済みの真正 `SU(2)≃S³` 全単射が元のWilson特徴弦距離を厳密に保存。
- **ADQの球集合条件を無条件に解消**：すべての元SU(2)中心`a`、すべての実数半径`r`で `B_J(a,r)=Φ⁻¹(B_{S³}(Φ(a),r))` を形式証明。ADQで明示的だった元の半径球のinverse-image条件はもはや仮定ではない。
- **未解決の独立obstruction**：元normalized compact SU(2) Haarから正規化S³ `Measure.toSphere` への**測度保存・全質量整合性**は未証明。等長全単射のみから測度移送を自動主張しない。したがってADQの半径だけによる正の下界は元SU(2) Haarへ無条件には移送していない。H一様強制性、共分散数値Lipschitz定数、連続体4D Yang–Mills質量ギャップも未証明。

### exact-source Lean4・公理依存

- 新規7定理・`#print axioms` 7件。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source PR CI #41371772326](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41371772326) は **11,269/11,269 SUCCESS**。変更Lean warning/error 0/0、全7件は標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、独立completion receipt SUCCESS。
- Source/test-merge/squash Git treeは `0bb7f516836f75615dcacf434bce8ff44cc48f64` で一致。次のADUの主要目標は、ADS/ADTの具体的な等長全単射の連続性および元normalized Haarと球面測度の正規化・測度保存を真正Lean4で確立すること。docs-onlyでStrict Leanは再実行しない。

---

## 検証済み定理 — ADS（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADS定理PR [#6166](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6166) はMERGED、定理squash SHA `04ad63891f9b24e7a62c09dfb5ddd0a22115939c`。元の有限体積interacting Wilson SU(2)、固定結合、中心化Gauss-law物理源、元FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootは不変更。

### 真正SU(2)と単位3球の両方向の逆写像・具体的全単射

- **真正S³→SU(2)逆写像の構成**：固定mathlibの `S³=Metric.sphere (0:EuclideanSpace ℝ (Fin 4)) 1` の全点 `x` に対して、実4座標から複素 `a=x₀+i x₁`、`b=x₂+i x₃` を取り、`|a|²+|b|²=1` をLean4で証明。代替の群構造や測度は導入しない。
- **本物のspecial-unitary行列への所属**：真正行列 `[[a,-conj(b)],[b,conj(a)]]` に対し、固定mathlibの `Matrix.adjugate_fin_two` と `Matrix.mul_adjugate` を用いて、`det=1`、`conjTranspose=adjugate`、`M*star(M)=1` を形式証明。よってまさに元の `Matrix.specialUnitaryGroup (Fin 2) ℂ` に所属する。
- **双方向の恒等写像と完全な全単射**：ADRの元第1列写像 `Φ:SU(2)→S³` に対し、新しい `Ψ:S³→SU(2)` を定義。全 `x∈S³` で `Φ(Ψ(x))=x`、全 `g∈SU(2)` で `Ψ(Φ(g))=g` をLean4証明。元 `Φ` の全射性・全単射性と、逆写像を備えた真正 `Equiv` を構成。
- **未解決の本質的橋渡し**：この `Equiv` は**集合としての全単射**であり、元ADK `J` 弦距離とS³弦距離の一致・位相同型・正規化 `SU(2)` Haarと正規化S³球面測度の測度保存性はまだLean4で証明していない。したがってADQの半径依存S³ Haar下界は元SU(2)へ無条件移送しておらず、`c*r³`、H一様強制性、連続体Yang–Mills質量ギャップも主張しない。

### exact-source Lean4・公理依存

- 新規7定理・`#print axioms`7件。固定Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source PR CI #41368903703](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41368903703) は **11,268/11,268 SUCCESS**。変更Leanファイルwarning/error 0/0、全7件は標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` なし、completion receipt SUCCESS。
- Source/test-merge/squash Git treeは `9acc6f7e740db0e17bbd9fe8a80219337982d4cd` で一致。今後は同じ `Equiv` の連続性・元弦距離同定・正規化Haar測度保存を独立に形式化し、初めてADQの明示的半径下界を元物理SU(2)へ移送する。docs-onlyでStrict Leanを再実行しない。

---

## 検証済み定理 — ADR（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。P4-Q2-PZ37ADR定理PR [#6163](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6163) はMERGED、定理squash SHA `c43658962ec2c2caeab7cf1f5028668c8e0347c5`。元のinteracting Wilson SU(2)、中心化Gauss-law物理源、元FF受信器、Perron/transfer、二interacting posterior、boundary pair-Haar、定理root、固定toolchainは不変更。default mainは文書ミラーのみ。

### 真正SU(2)行列の4実次元単位球面への単射と四元数形復元

- **本物のSU(2)第1列の単位条件**：任意の元の特殊ユニタリ2×2行列 `g` で `Complex.normSq(g₀₀)+Complex.normSq(g₁₀)=1` を既存のunitary groupのstar積条件からLean4で証明。独立した四元数群の仮定は挿入しない。
- **4実次元単位球面の実際の点**：行列成分の `(Re(g₀₀),Im(g₀₀),Re(g₁₀),Im(g₁₀))` を `EuclideanSpace ℝ (Fin 4)` に構成し、Euclidean normの2乗=1、norm=1、`S³` への真正写像を形式証明。従来の行列8実次元表現から4実次元表示へ還元。
- **行列全体を第1列から厳密に復元**：元SU(2)の`det(g)=1`と`gᴴg=ggᴴ=I`を使用し、`adjugate(g)=conjTranspose(g)` と `g₁₁=conj(g₀₀)`、`g₀₁=-conj(g₁₀)` を証明。よって元の行列は `[[a,-conj(b)],[b,conj(a)]]` で完全に表され、第1複素列写像および `SU(2)→S³` 写像が**単射**であることを証明。
- **未解決obstruction**：今回は`S³→SU(2)`逆写像・全射性・元ADK特徴弦距離との等長性・球面測度のnormalized SU(2) Haarへの移送はまだ証明していない。ADQの半径依存球面測度下界は現時点で元SU(2)上へ無条件移送していない。H一様強制性や連続体Yang–Mills質量ギャップは主張しない。

### exact-source Lean4・公理依存

- 新規8定理・`#print axioms`8件。固定Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41366463730](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41366463730) は **11,267/11,267 SUCCESS**。変更Leanファイルwarning/error 0/0、全8件 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし。Source/test-merge/squash Git tree `4a60cc5e85fa8281fa90b08409b22a9cce557cfe` 一致。
- 次の形式化候補：同じ本物のSU(2)行列から具体的な `S³→SU(2)` 逆写像を構成し全射性を証明した後、元弦距離の一致と正規化Haar測度の移送を個別に証明する。docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — ADQ（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADQ定理PR [#6160](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6160) はMERGED、定理squash SHA `481ac27155d7137dbf16f8e42e826cb09f966a7e`。元の有限体積interacting Wilson SU(2)、元Gauss-law物理源、元FF受信器、元boundary pair-Haar、固定Lean・mathlib・定理rootは不変更。

### 実4次元単位球面の半径依存Haar評価と真正SU(2)移送の明示的条件

- **固定mathlibの真正S³球面測度**：`E4 = EuclideanSpace ℝ (Fin 4)` は実次元4、`S3 = sphere(0,1)`。元Euclidean `volume` の `Measure.toSphere` をそのまま使用し、球面測度の総質量 `σ(S³)=4*volume(ball(0,1))` をLean4で証明。**`toSphere` を正規化済み確率測度と誤認しない**。
- **球面の半径のみの陽な下界**：`κ(r)=((Measure.toSphereBallBound 4 r : NNReal):ℝ)/4` を定義し、全 `r` で `κ(r)>0`、全 `r>0` と `x∈S³` で `σ(ball(x,r))≥κ(r)*σ(S³)` をLean4証明。これは球面に関する**無条件**定理で、固定mathlibの `toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball` と総質量恒等式を使用する。
- **元SU(2) Haarへの条件付き移送**：元ADKの `BallJ`、ADMの `m(r)=μ_G(BallJ(1,r))`、元normalized SU(2) Haar `μ_G` を保持したまま、写像 `f:G→S³` について (i) 元弦距離球の逆像一致、(ii) `μ_G(f⁻¹s)*σ(S³)=σ(s)`、(iii) `σ(S³)>0` を**明示的前提**として、`m(r)≥κ(r)` と任意中心の同じ下界を形式証明。
- **未解決obstructionを保全**：このPRでは `SU(2)≃S³` の具体的等長写像、元 `J` 弦距離との一致、正規化Haarの測度保存移送は**まだ証明していない**。したがって元SU(2)上の**無条件**半径下界、`c*r³` の鋭い3次スケーリング、全有限Hに一様な強制性、連続体4D Yang–Mills質量ギャップは主張しない。次の実装は四元数・実4次元球面への写像と元Haarの正当な測度対応の個別証明。

### exact-source Lean4・公理依存

- 新規6定理・`#print axioms`6件、固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41364001721](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41364001721) は **11,266/11,266 SUCCESS**、変更Leanファイルwarning/error 0/0、6件すべて標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし。
- Source/test-merge/squash Git treeは `8e7c38ee32bc76ceabc54890b6112f026e508b6c` で一致。定理正本HEADは `481ac27155d7137dbf16f8e42e826cb09f966a7e`（文書同期前）。default mainへLean定理ソースはコピーしない。

---

## 検証済み定理 — ADP（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADP定理PR [#6157](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6157) はMERGED、定理squash SHA `472b95ec8070088d66030c7ad067cc731f1f4ce2`。元の有限体積interacting Wilson SU(2)、固定結合、中心化Gauss-law物理源、元FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootは不変更。

### 真正SU(2)弦距離の有限被覆と小球Haar数値証明書

- **任意正半径での真正SU(2)有限net**：ADKの元の正規化行列特徴 `J` が定める `B_J(a,r)={g:d_J(a,g)<r}` は元位相で開き、真正 `SU(2)` はコンパクト。全 `r>0` について有限集合 `s:Finset SU(2)` を元のSU(2)内部から選び、全 `g` がある `a∈s` の球 `B_J(a,r)` に入ることをLean4証明。被覆集合 `s` は非空。
- **元normalized SU(2) Haarの評価可能な数値下界**：ADMの中心不変な元Haar球質量 `m(r)=μ(B_J(1,r))` に対して、被覆が成立する任意の実際の有限 `s` について `1≤card(s)*m(r)`、従って **`m(r)≥1/card(s)`** をLean4証明。被覆と `card(s)≤N` を具体的に検査できれば **`m(r)≥1/N`**。真のnormalized Haarと測度劣加法性のみを使用し、有限群上の一様分布は使わない。どの真正SU(2)中心でも同じ質量下界が成立。
- **元の全リンク・二境界D_H球への厳密移送**：元の有限`H`リンク集合`Link_H`と`R>0`について、被覆半径 `r=R/(2*card(Link_H)+1)` の真正net `s` から `ν_H(B_{D_H}(a,R))≥(1/card(s))^(2 card(Link_H))`。さらに`card(s)≤N`なら `ν_H(B_{D_H}(a,R))≥(1/N)^(2 card(Link_H))` を形式証明。元のpair-Haar法則とADMの箱⊆球をそのまま使用し、半径 `R=1/2` の元全リンク球でも存在証明書を構成。
- **数値化に関する正確な境界**：全`r>0`で有限整数分母が存在することと、その値 `N(r)` を計算したことは異なる。今回の `s` はコンパクト性による存在証明であり、**明示した`r↦N(r)`・`c*r^3`等の半径だけによる数値下界は未証明**。ADI/ADHの厳密68条件、元Perron/FF共分散の定量Lipschitz係数、ACI非零点振幅、H一様強制性・連続体4D Yang–Mills質量ギャップも未解決。
- **次の橋渡し**：固定mathlib `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` に球面Haarの `toSphereBallBound` がある。ただし、これを真正SU(2)へ移すには元の四元数・単位3球表示と元normalized Haarの測度保存対応を先にLean4証明する必要がある。現段階でその対応は仮定にも結論にも入れていない。

### exact-source Lean4・公理依存

- 新規12定理と `#print axioms` 12件。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source PR CI #41361036521](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41361036521) は **11,265/11,265 SUCCESS**、変更Leanファイルwarning/error 0/0、12件すべて標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` なし、独立MCP completion receipt SUCCESS。
- Source/test-merge/squash Git treeは `d940b7e31c9632dacd73e696576dbd7e89fc9f6e` で一致。定理正本はPR #6157のsquashに保持し、default mainにはLean証明をコピーしない。

---

## 検証済み定理 — ADO（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAPの文書ミラーのみ。P4-Q2-PZ37ADO定理PR [#6154](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6154) はMERGED（squash `a1d8563a055198509557072de33666809a2420d6`）。元の有限体積interacting Wilson SU(2)、固定結合、中心化Gauss-law物理源、元FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haarと定理rootは不変更。

### 真正異半径SU(2)反対極Haarと元全リンク球の数値障害拡張

- **真正反対極の2球距離恒等式**：ADK・ADNの元正規化行列8実次元特徴による`d_J`と実際の中心元`z=-I`について、全真正`g∈SU(2)`で`d_J(1,g)^2+d_J(z,g)^2=4`をLean4証明。`r,s>0`かつ`r^2+s^2≤4`なら元の異半径OPEN球は交わらず、同じnormalized SU(2) Haarに対して`m(r)+m(s)≤1`。
- **真正Haar質量の有理数半径上界**：元ADKの`m(5/4)≥1/8`と新しい2球非交差性から、全`r>0`、`r²≤39/16`で`m(r)≤7/8`を形式証明。とくに`1/2≤m(3/2)≤7/8`。さらに全`0<r<2`について、正Haar質量の反対極球を使い`m(r)<1`を証明。ただし`m(r)`の小半径での明示正下界ではない。
- **元の零時刻格子に12本以上の物理空間リンク**：側長`2(H+1)≥2`の元の`ZMod`格子について、原点と3つの座標単位頂点が異なることをLean4証明し、3空間方向との積から全有限`H`について`card(Link_H)≥12`を形式証明。元幾何からの結論であり、人工的なリンク数の仮定なし。`Nat.card_prod`でFintypeインスタンスの不一致を回避。
- **本物の全リンク距離球に対する強い数値obstruction**：元ADM/ADNの真正`D_H`全リンク球のpair-Haar上界を利用し、任意の元中心a・有限H・`0<R`・`R²≤39/16`について`ν_H(B_D(a,R))≤(7/8)^(2 card(Link_H))≤(7/8)^24<1/17`をLean4証明。半径`3/2`を含み、ADNの`R²≤2`から真に拡張された。
- **元物理源のADI/ADH 68条件に直接接続**：同じ真正`C_e(a)`と`K_H`で`68*C_e(a)^2*ν_H(B_D(a,R))≤K_H`を上記半径範囲に対して形式証明。これはこの球を用いる**ADHの特定の68十分条件が成立しない**ことを意味し、GI非零性・物理質量ギャップそのものの不成立を意味しない。
- **未証明の本質的障害**：元normalized SU(2) Haarの任意小半径での計算可能な正下界・四元数/単位3球への測度保存対応・元Perron/FF共分散の定量Lipschitz係数・ACI非零点の数値振幅・共分散が安定する大質量球での`ν_H>1/17`・H一様強制性・連続体4D Yang–Mills質量ギャップ。元の一様連続性をLipschitz性と混同しない。

### exact-source Lean4 CI・公理依存

- 新規14定理、`#print axioms`14件。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。 [exact-source PR CI #41358770192](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41358770192) は **11,264/11,264 SUCCESS**、変更Leanファイルwarning/error 0/0、14件全て`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、独立MCP completion receipt SUCCESS。
- Source/test-merge/squash Git treeは`cd2132bb473d25c7d2ed8b19605d1af478973319`で完全一致。定理PR #6154はMERGED。default mainは文書ミラーであり、Lean定理源は正本branchにだけ保持する。

---

## 検証済み定理 — ADN（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAPの文書ミラーのみ。P4-Q2-PZ37ADN定理PR [#6151](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6151) はMERGED（定理squash `0bdcc7da613baa448638605a41b08172e9c0960c`）。元の有限体積interacting Wilson SU(2)、固定結合、中心化Gauss-law物理源、元FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haarと定理rootは不変更。

### 真正SU(2)反対極Haar球と元全リンク球の定量的上界

- **真正中心反対極の弦距離**：ADKの元行列特徴 `J`、真正Wilsonエネルギー `E`、既存のSU(2)中心元 `z=-1` について `d_J(1,g)^2=2E(g)` と `d_J(z,g)^2=2(2-E(g))` をLean4証明。新しい測度模型・任意の正則性仮定は導入しない。
- **元normalized SU(2) Haarの半径別数値境界**：ADMの真正 `m(r)=μ{g:d_J(1,g)<r}` に対し、`0<r` かつ `r^2≤2` なら反対極OPEN球は互いに素で `m(r)≤1/2`、`0<r` かつ `r^2>2` なら両球はSU(2)を覆い `m(r)≥1/2`。とくに `m(3/2)≥1/2`。ADKの単純な `1/8` cap質量とは異なる半径別校正である。
- **元全リンク・二境界の球と箱の比較**：ADLの真正 `D_H` 球は同じ半径の真正全リンク箱に含まれる。ADMの厳密Haar積測度から `ν_H(B_{D_H}(a,R))≤m(R)^(2 card(Link_H))` をLean4証明。空間リンク型は実際の零時刻頂点×3空間方向であり、`card(Link_H)≥3` を元幾何から証明した（`Nat.card_prod` によってインスタンスに依らず計数）。
- **数値的 `1/17` obstruction**：任意の元境界中心a・有限H・`0<R`・`R^2≤2` に対し `ν_H(B_{D_H}(a,R))≤(1/2)^(2 card(Link_H))≤1/64<1/17`。従ってADIの元物理共分散・元FC上界 `K_H` による `68 C_e(a)^2 ν_H(B_{D_H}(a,R))≤K_H` を証明し、ADHの厳密な68十分条件は**この半径領域の同じ元全リンク球では成立しない**。これは十分条件の数値的障害であり、真の物理mass gapの否定ではない。
- **残る厳密な課題**：任意の小半径における `m(r)` の計算可能な正の数値下界、元物理共分散の計算可能なLipschitz係数、非零振幅の数値下界、より大きい真の安定球での `ν_H>1/17` の成立可否、有限体積一様強制性、連続体4D Yang–Mills mass gap はいずれも未証明。ADMの一様連続性をLipschitz性と混同しない。

### exact-source Lean4検証

- 新規定理14件・`#print axioms` 14件。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41356437448](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41356437448) は **11,263/11,263 SUCCESS**、変更Lean file error/warning 0、全14定理で公理は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし。独立MCP completion receiptもSUCCESS。
- Source/test-merge/squashのGit treeはすべて `e677d0fd47e4209c4bd63cd6ee05d23cdad90081` で一致。定理正本はPR #6151のsquashであり、default mainには定理Leanをコピーしない。

---

## 検証済み定理 — ADM（2026-11-02 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`、default `main`はREADME・ROADMAPの文書ミラーのみ。P4-Q2-PZ37ADM定理PR #6148はMERGED、定理squash SHA `454006a79a2332d45bdb3887db1f5be6e1e594d4`。元の有限体積interacting Wilson SU(2)、固定結合`b0=log(3/2)/64>0`、中心化Gauss-law物理源、元FF受信器、Perron/transfer、元二interacting posterior、元boundary pair-Haar確率は一切変更していない。

### 真正SU(2)の任意半径Haar質量と全リンク弦距離での共分散一様連続性

- **真正行列特徴弦距離の左平行移動不変性**：ADKの既存厳密校正式`d_J(a,g)^2=2*E(a^{-1}g)`とノルム非負性から、すべての真正`a,g∈SU(2)`で`d_J(a,g)=d_J(1,a^{-1}g)`をLean4証明。従って真正normalized SU(2) Haarの弦距離OPEN球質量は中心aに依存しない。真正SU(2)球質量関数`m(r)=μ{g:d_J(1,g)<r}`を定義し、**任意のr>0で厳密に`m(r)>0`**を元compact Haarのopen-positive性から証明。代替有限群Haarやposteriorへの置換なし。
- **元の全リンク・二境界Haar箱の厳密な半径別積測度**：実際の`Link_H`と元`Pair_H=Cfg_H×Cfg_H`において、任意中心aと半径rに対する左右全リンク弦距離箱`Q_H(a,r)`について、元のpair-Haar`ν_H`の厳密等式`ν_H(Q_H(a,r))=m(r)^(2*card(Link_H))`を形式証明。これはADLの粗い`8^(-2card(Link_H))`からの前進であり、rが小さいときも成立する。`m(r)`自体は元の真正Haar測度の値で、**数値評価は未実施**。
- **任意の正半径での真正全座標距離球の質量下界**：元の全リンク距離`D_H(z,w)=Σ_e[d_J(z.left(e),w.left(e))+d_J(z.right(e),w.right(e))]`について、すべての`R>0`で`Q_H(a,R/(2card(Link_H)+1))⊆B_{D_H}(a,R)`を証明。ゆえに`ν_H(B_{D_H}(a,R)) >= m(R/(2card(Link_H)+1))^(2card(Link_H))>0`が全有限H・全中心a・全R>0で真正pair-Haarについて成立。半径が小さい場合も有効だが、この下界の具体的な実数値はまだ未知。
- **真正元物理共分散の全配置一様連続性**：元の`Pair_H`は真正SU(2)有限積のコンパクト空間、ADLの`D_H`は点を分離し、今回は`(z,w)↦D_H(z,w)`の**同時連続性**を証明。genericなcompact bad-pair最小距離補題をLean4証明し、ACDの真正元共分散`C_e(z)=Cov_Haar(F_original,e(z),E)`へ適用。全有限H・真正リンクe・全ε>0で**共通のδ>0が存在し**、`D_H(z,w)<δ`なら全元境界対z,wについて`|C_e(z)-C_e(w)|<ε`が成立。これは真のreceiver/transferに由来する一様連続性だが、数値δ・線形Lipschitz係数Lは導いていない。
- **同じ真正D_H球で非零共分散・Haar質量・二乗momentを接続**：ACIによる同じ中心化Gauss-law物理源の非零真正Cov点`a`を選択し、ε=`|C_e(a)|/2`で上記一様連続性から`R>0`を取得。元の全リンクOPEN球`B_{D_H}(a,R)`全域で`|C_e(z)|>=|C_e(a)|/2`、同じ球の元pair-Haar質量`>=m(R/(2card(Link_H)+1))^(2card(Link_H))>0`、ADEの`(|C_e(a)|/2)^2*ν_H(B_{D_H}(a,R))<=S_e`を形式証明。物理元ソース・受信器・正Perron代表・二posterior・元Haar法則は不変更。
- **残る厳密な数値障害**：存在する半径Rと一リンク小球質量`m(R/(2card(Link_H)+1))`、真正Cov非零点での振幅、および実線形Lipschitz係数は**数値評価されていない**。一様連続性を一様Lipschitz性と同一視しない。ADIで必要な`ν_H(ball)>1/17`、ADHの厳密`K_H<68*C_e(a)^2*ν_H(ball)`、H一様物理強制性・連続体4D Yang–Mills質量ギャップは引き続きOPEN。

### exact-source CI・公理監査・独立completion receipt

- 定理PR #6148 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6148 — MERGED。唯一の新規Leanファイル`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullChordalCovarianceModulusV5_PZ37ADM.lean`、17定理・17件`#print axioms`、追加488行・削除0行。既存Lean・定理root・モデル・workflow・Lean/mathlib pin不変更。
- 最終exact-source SHA `bf3e784fd9f852c9db6b4bafefedf59afef7f8be`、PR test-merge `9b4c45a29997eb0960d45577f45d1de161c2fcfa`、定理squash `454006a79a2332d45bdb3887db1f5be6e1e594d4`は**完全一致Git tree**`d75f7637916dab3f51a428dea8c6357cd81abd0b`。
- source CI #41352932167 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41352932167 — **11262/11262 SUCCESS**。17/17公理が`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更警告・エラー0/0、独立completion receipt SUCCESS。
- マージ後push CI #41353451974 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41353451974 — 正本squashで**11262/11262 SUCCESS**、17/17標準公理のみ、`sorryAx`・変更警告・エラー0/0、独立completion receipt SUCCESS。
- 初回CI #41352489549の唯一のelaboration errorは`Finset.univ.card`と`Fintype.card Link`の同値正規化不足で、固定mathlibの`Finset.card_univ`を追加し修正。Leanファイル全文・imports・依存定理型・固定APIを確認。定理主張・仮定・数値定数を弱めず、Lean`v4.30.0-rc2`・mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。docs-onlyのStrict Leanは起動しない。

### 次の研究課題 — ADN（OPEN）

ADMで実際の全リンク距離`D_H`、元pair-Haar全半径質量の厳密関数`m(r)^(2card(Link_H))`、元共分散一様連続性と同球二乗moment下界を確立。次は真正SU(2)の実8次元特徴＝S³上の球から**小半径Haar質量m(r)の計算可能な明示下界**を形式化し、真正Perron/transfer/FF受信器から共分散変動の数値モジュラスまたはLipschitz係数を評価する。元の同じ球についてADIの`1/17`とADHの68条件を独立数値比較する。有限Hの条件付き結果を、全H一様強制性・連続体mass gapと混同しない。

---
## 検証済み定理 — ADL（2026-11-02 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`、default `main`はREADME・ROADMAP文書ミラーのみ。P4-Q2-PZ37ADL定理PR #6145はMERGED、定理squash SHA `c74c5aef86f89debdc6e97f1501b44be384e0073`。元の有限体積interacting Wilson SU(2)、固定結合`b0=log(3/2)/64>0`、中心化Gauss-law物理源、元FF受信器、Perron/transfer、元の二interacting posterior・真正境界pair-Haar測度は不変更。

### 真正SU(2)正規化実8次元特徴の単射性と全境界リンク弦距離

- **既存元SU(2)特徴Jの真正単射性**：既存`complexMatrixRealFeature 2`は元の複素2×2行列の全要素の実部・虚部を8座標として記録するため、`Complex.ext`と座標ごとの等式により単射であることをLean4証明。既存正規化係数`sqrt(1/2)≠0`でのスカラー倍も単射。従ってADKの数値校正弦距離`d_J(g,h)=||J(g)-J(h)||`について`d_J(g,h)=0 ↔ g=h`、正値分離性を真正SU(2)上で形式化。既存校正式`d_J(g,h)^2=2*E(g^-1*h)`を保持。
- **元の全リンク・二境界の真正距離**：元の有限`Link_H`と`Pair_H=Cfg_H×Cfg_H`で`D_H(z,w)=Σ_{e∈Link_H}[d_J(z.left(e),w.left(e))+d_J(z.right(e),w.right(e))]`を定義。非負性、自己距離0、対称性、三角不等式、`D_H(z,w)=0 ↔ z=w`をLean証明。`D_H(z0,·)`は元のSU(2)有限積位相で連続であり、その数値距離OPEN球は元位相でOPEN。距離公理・連続性を主張し、別の物理確率法則を導入しない。
- **全リンクを同時に制約した本来のHaar箱の正確な質量**：各元リンクe、左右両境界に同じ数値半径rの真正SU(2)弦距離球を課す実OPEN集合`Q_H(z0,r)`を構成。固定mathlibの`Measure.pi_pi`・`ENNReal.toReal_prod`と元の真正境界pair-Haar`ν_H=(⊗_{e∈Link_H}μ)⊗(⊗_{e∈Link_H}μ)`から、その実質量が**すべての2|Link_H|個のSU(2)球質量の積そのもの**であることを証明。ADKの`r>1`で各因子`>=1/8`を使い、`ν_H(Q_H(z0,r))>=(1/8)^(2*|Link_H|)>0`を無条件に証明。
- **真正全リンク距離OPEN球への数値接続**：全座標半径r箱は`D_H`の中心z0、明示半径`R_H(r)=2*|Link_H|*r+1`のOPEN球に包含。具体的な数値`r=5/4`では`R_H=(5/2)|Link_H|+1`で、**元境界pair-Haarの真正全座標距離球**に対し`ν_H(B_{D_H}(z0,R_H)) >= 8^(-2*|Link_H|)>0`をLean証明。全リンク数に対する有限積質量低下を隠さない。
- **元物理共分散の中心**：ACIが真正リンクeで与えた同じ中心化Gauss-law物理源の`C_e(z0)≠0`を、上記OPEN全座標距離球の実中心に選ぶことができる。中心で非零であることと、球全域で`|C_e|`が明示的な正下界を持つことは別。現段階で後者やLipschitz定数は未証明。
- **数値障害・適用範囲**：`8^(-2|Link_H|)`は**H依存の数値下界**で、ADKの単一座標`1/8`と同一視しない。正Haar質量の構成だけではADIの球質量`>1/17`やADHの真正`K_H<68*C_e(z0)^2*ν_H(ball)`は得られない。全H一様な物理強制性、正の連続体4D Yang–Mills質量ギャップも未証明。

### exact-source Lean・公理監査・マージ後push CI

- 定理PR #6145 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6145 — MERGED。新規Leanファイル`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullBoundaryChordalMetricV5_PZ37ADL.lean`1件のみ、25定理・25件`#print axioms`。既存Leanファイル、定理root、model、workflow、toolchain pin不変更。
- 最終exact-source HEAD `6b4959aca31335d2e32e34aa5fad611eece1d055`、PR test-merge `3a0cdcf4b48c47c7f23ecf5b539a840c47d338be`、定理squash `c74c5aef86f89debdc6e97f1501b44be384e0073`のGit treeはすべて`daaa0f493f5b788d83c9fcb90b0d1c3b1fe01cb5`で完全一致。
- exact-source CI #41350558042 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41350558042 — **11261/11261 Lean SUCCESS**、25/25公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更警告・エラー0/0、独立completion receipt`event=pull_request`・`source_result=success`。
- マージ後push CI #41351035719 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41351035719 — 正本squash HEADで**11261/11261 SUCCESS**、25/25標準3公理、`sorryAx`・変更警告・エラー0、独立completion receipt`event=push`・`source_result=success`。
- 初回CI #41349647417のSU(2)型変数と同名の等式証拠、`slice.prod`局所記法、対称性rewrite方向を修正。次のCI #41350120558の`SFinite`型推論停止を、元pair-Haarを完全修飾して`measureReal_prod_prod`を対象指向`rw`で適用して解消。全文・imports・依存定理型・固定mathlib APIを検証し、定理主張・仮定・数値定数を一切弱めていない。Lean`v4.30.0-rc2`、mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。文書のみのStrict Leanは起動しない。

### 次の研究課題 — ADM（OPEN）

ADLで**真正の全リンク距離とH依存Haar球質量下界**まで形式化完了。次は同じ全リンク距離の元位相との同値性を明示し、半径依存のSU(2) Haar球質量を強化して粗い`8^(-2|Link_H|)`の衰退を評価する。最重要の未解決課題は、元FF受信器とPerron/transferの同じ物理模型から数値Lipschitz係数`L_H,e`と非零Cov点での数値振幅を導き、**同じ全座標球**の実Haar質量と比較してADH/ADIの`1/17`および68閾値を検証すること。正値の存在と数値閾値通過、固定HとH一様性、有限体積と連続体質量ギャップを区別する。

---
## 検証済み定理 — ADK（2026-11-02 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`、default `main`はREADME・ROADMAP文書ミラーのみ。P4-Q2-PZ37ADK定理PR #6142はMERGED、定理squash SHA `de512ca9efd2cfb3477d4e63524f8c3e16406be8`。元の有限体積interacting Wilson SU(2)、固定結合`b0=log(3/2)/64>0`、中心化Gauss-law物理源、元FF受信器、Perron/transfer、元二interacting posterior、元境界pair-Haar確率は不変更。

### 真正行列実8次元特徴からの数値校正弦距離と物理的Haar球

- **既存真正SU(2)特徴の距離校正**：normalized SU(2)実トレース核の既存行列実8次元Hilbert特徴`J(g)=sqrt(1/2)*realify(g)`を使用し、弦距離`d_J(g,h)=||J(g)-J(h)||`を定義。既存の元SU(2)相対トレース核内積と単位特徴ノルムから、元Wilsonエネルギー`E(g)=1-Re(tr(g))/2`に関する**厳密等式**`d_J(g,h)^2=2*E(g^{-1}h)`をLean4証明。`d_J>=0`、`d_J(g,g)=0`、対称性・三角不等式も証明。`J`の連続性から数値弦距離OPEN球は**元のSU(2)位相でOPEN**。`J`の単射性による距離分離性は別途形式化するため、ADK時点では校正済み**擬距離**と呼ぶ。
- **全中心における具体的半径と真正Haar質量**：ABVの元normalized SU(2) compact Haarに対するquaternion8平行移動による真正Wilson閉cap`{g:E(g)<=1/2}`の数値下界`μ(cap)>=1/8`を再利用。任意の真正中心`a∈SU(2)`、任意の数値半径`r>1`で、元の閉capの`a`による実左平行移動は真の弦距離OPEN球`B_J(a,r)={g:d_J(a,g)<r}`に包含。実Haar左不変性から`μ(B_J(a,r))>=1/8`が成立。特に**明示半径`5/4`**で`μ(B_J(a,5/4))>=1/8>1/17`。
- **元の有限体積Haar pairへの定量移送**：元境界`Pair_H=Cfg_H×Cfg_H`と真の`ν_H=(⊗_{e∈Link_H}μ)⊗(⊗_{e∈Link_H}μ)`に対し、`z↦z.left(e)`の真正測度保存射影から、一リンク弦距離円筒`V_{H,e,a,r}={z:d_J(a,z.left(e))<r}`はOPENで、`ν_H(V)=μ(B_J(a,r))>=1/8`、任意`H,e,a,r>1`で成立。ACIの真正中心化Gauss-law共分散非零点`z0`を選び、その**真の第1境界リンク値`z0.left(e)`を円筒の中心**にでき、中心点で`C_e(z0)≠0`、円筒Haar質量`>1/17`を同時に証明。ただし円筒全域で共分散が非零または一定振幅を保つとは主張しない。
- **真正二境界座標での質量**：元の`(z.left(e),z.right(e))`射影は真正pair-Haarから`μ×μ`への測度保存。二つの独立した数値半径`5/4`弦距離球を同時に課す**元物理境界上の二座標円筒**は、実質量が各SU(2)球質量の積に正確に等しく`>=1/64`。これを全リンク制約の球、posterior法則、またはGI受信器の振幅と取り違えない。
- **引き続きOPENな本質的障害**：全リンクの数値校正積距離での**真正全座標球**のHaar質量、SU(2)特徴単射性の独立Lean証明、元FF受信器の実Lipschitz係数`L_H,e`、非零点共分散の実数値下界、円筒の共分散安定部分の質量`>1/17`、ADHの`K_H<68*C_e(z0)^2*ν_H(ball)`、全H一様強制性および連続体4D Yang–Mills質量ギャップは未証明。`1/8`は一座標円筒、`1/64`は二座標円筒の数値下界に限定。

### exact-source Lean・公理依存・独立completion receipt

- 定理PR #6142 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6142 — MERGED。新規Leanファイル`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCalibratedChordalHaarBallsV5_PZ37ADK.lean`のみ、21定理・21件`#print axioms`、追加430行・削除0行。既存Lean・root・物理模型・workflow・toolchain pin変更なし。
- source SHA `3d2ce2128538a7c765b7dc61f8e5e1d8d7644fd1`、test-merge SHA `5253f765eaa54f86408ebe69a077026126dfdc88`、定理squash SHA `de512ca9efd2cfb3477d4e63524f8c3e16406be8`はすべて共通Git tree `c4cd8713a6e348184e1e4a8f40d631e2041c9881`。
- exact-source CI #41347960546 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41347960546 — **11260/11260 Lean SUCCESS**。21/21公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立completion receipt`event=pull_request`・`source_result=success`。
- マージ後push CI #41348415962 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41348415962 — theorem squash正本HEADで**11260/11260 SUCCESS**、21/21標準公理、`sorryAx`・変更警告・エラー0、独立completion receipt`event=push`・`source_result=success`。
- 初回source CIから追加修正なし。既存normalized-trace Hilbert特徴、Mathlibのノルム二乗等式・連続性・Haar測度保存射影を直接組み合わせて証明。Lean`v4.30.0-rc2`、mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`維持。docs-onlyではStrict Leanを起動しない。

### 次の研究課題 — ADL（OPEN）

ADKの数値校正されたSU(2)実8次元特徴について**単射性・元位相との同値性を形式化した真正距離**を確立する。その距離を元の有限リンク積・左右二境界の**全座標**に拡張し、真正pair-Haarの全座標球質量を`H`依存の実数値として評価する。単一/二座標円筒下界を全座標球へ無根拠に流用しない。その後、同じ全座標球で元FF受信器の物理共分散振幅・Lipschitz係数を導出し、ADH/ADIの数値`1/17`および68閾値を評価する。全H一様性・連続体mass gapは別ゲートとする。

---
## 検証済み定理 — ADJ（2026-11-02 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。P4-Q2-PZ37ADJ定理PR #6139はMERGED、定理squash SHA `0517a9bf440ba8fda37db56bb04ff3c657cdd662`。元の有限体積interacting Wilson SU(2)、固定結合`b0=log(3/2)/64>0`、中心化Gauss-law源、元FF受信器、Perron/transfer、元二interacting posteriorと真正境界pair-Haar確率は変更していない。

### 元SU(2)単一リンクOPEN capと真正有限体積境界pair-Haarの定量下界

- **既存の真正ABV数値Haar capをOPEN化**：元Wilsonエネルギー`E(g)=1-Re(tr g)/2`について、既存ABVの真正SU(2) quaternion8平行移動による閉cap`A={g:E(g)<=1/2}`の元normalized compact Haar質量`μ(A)>=1/8`を再利用。厳密なOPEN cap`U={g:E(g)<3/4}`は`A⊆U`を満たすので`μ(U)>=1/8`。補助的な有限群Haarには置換しない。
- **元境界pair-Haarへの実際の測度保存移送**：元境界`Pair_H=Cfg_H×Cfg_H`、真の`ν_H=(⊗_{e∈Link_H}μ)⊗(⊗_{e∈Link_H}μ)`について、元の第1境界の指定リンク射影`z↦z.left(e)`は`MeasureTheory.measurePreserving_eval`と元productの`measurePreserving_fst`から真正測度保存。従ってすべての有限H・真正リンクeで`V_{H,e}={z:E(z.left(e))<3/4}`はOPEN、かつ`ν_H(V_{H,e})=μ(U)>=1/8>1/17`。これは**単一リンク円筒領域の真のH非依存質量下界**であって、共分散球やphysical coercivityのH一様下界ではない。
- **八つの実quaternion平行移動で全元境界を被覆**：ABVの8個のSU(2)平行移動から、各`e`に対する8個の真正OPEN円筒領域`V_{H,e,i}={z:E(q_i*z.left(e))<3/4}`を作り、各領域に`ν_H(V_{H,e,i})=μ(U)>=1/8>1/17`を証明。さらに`⋃_i V_{H,e,i}=Pair_H`。元pair-Haarを任意の代替法則へ変更していない。
- **元の非零物理共分散との交差**：ACIの元中心化Gauss-law物理源の真正`C_e(z0)≠0`から、この非零点が上の大質量OPEN円筒の少なくとも一つに属する。ACDの元Cov連続性と元pair-Haarのopen-positive性で、その内部に**より小さい**OPEN `W_e`、`a_e>0`、`ν_H(W_e)>0`を構成し、全`z∈W_e`で`|C_e(z)|>=a_e`とADEの`a_e²*ν_H(W_e)<=S(H,b0,e)`を形式証明。大きな親円筒の`>=1/8`を小領域の質量として誤って代入しない。
- **元の二境界座標の実pair-Haar**：同じ元リンクeでの`z↦(z.left(e),z.right(e))`は真正`ν_H`から元の`μ×μ`への測度保存。ABVの真正low/high ordered capの`(μ×μ)(capPair)>=1/64`を、元の物理境界pair上の対応円筒の実質量`>=1/64`として形式証明。これは二posteriorのsigned GI応答下界ではない。
- **未証明の正確な境界**：`ν_H(V)>=1/8`は成立しても、`ν_H(W_e)>1/17`、共分散の明示振幅`C_e(z0)^2>K_H/68`、真正Wilson共分散の数値Lipschitz係数、物理的に数値校正したSU(2)積距離球の質量、ADI/ADHの厳密`K_H<68*C_e(z0)^2*ν_H(ball)`、全体積一様強制性、連続体4D Yang–Mills質量ギャップは未証明。OPEN円筒と元のADH擬距離球を同一視しない。

### exact-source CI・公理監査・マージ後push CI

- 定理PR #6139 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6139 — MERGED。新規Leanファイル`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalBoundaryHaarCylindersV5_PZ37ADJ.lean`のみ、18定理・18件`#print axioms`、追加408行・削除0行。既存Lean、模型、root、workflow、Lean/mathlib pin不変。
- 最終exact-source HEAD `d572a5a58264aae332e10c78052e50971dae8a1c`、test-merge `96fdbeed8c170317137c595bc69f992d9688cece`、定理squash `0517a9bf440ba8fda37db56bb04ff3c657cdd662`はすべて同一Git tree `7a27ee4d2922e7c9f6c329bb9c7b87c52f85ee96`。
- exact-source CI #41343426933 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41343426933 — 11259/11259 Lean SUCCESS、18/18公理が`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更warning/error 0/0、独立completion receipt `event=pull_request`・`source_result=success`。
- マージ後push CI #41343909762 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41343909762 — 定理squash HEADで11259/11259 SUCCESS、18/18標準3公理のみ、`sorryAx`・変更警告・エラーなし、独立completion receipt `event=push`・`source_result=success`。
- 初回CIのLean局所記法`μ`と名前付き引数、`slice`・`outer`のドット記法、冗長な`dsimp`、最後の`μ.prod`名前解決エラーを、変更ファイル全文・依存定理型・固定mathlib APIを確認して完全修飾で修正。数学的主張・仮定・数値定数の緩和なし。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。docs-onlyではStrict Leanを起動しない。

### 次の研究課題 — ADK（OPEN）

今回の`>=1/8`は元Haarの**単一リンクOPEN円筒**に対する数値下界であり、真正Cov下界が保たれる小領域の数値質量ではない。次は元SU(2)の具体的な行列／四元数座標に沿った数値校正距離、真正有限リンク積上の明示的なmetric ballとその元pair-Haar下界、元FF受信器の真正Lipschitz係数、およびACIの非零Cov振幅をそれぞれ形式化し、**同じ領域**で`ν_H(ball)>1/17`と`|C_e(z)|`を両立できるかを検証する。球半径・共分散振幅・Haar質量の存在と実数値評価、固定HとH一様性、有限体積と連続体を分離する。

---
## 検証済み定理 — ADI（2026-11-02 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。P4-Q2-PZ37ADI定理PR #6136はMERGED、定理squash SHAは`b48204a99e89a454aac1bda0fd9d11fd34dfc303`。元の有限体積interacting Wilson SU(2)、固定結合`b0=log(3/2)/64`、中心化Gauss-law源、元FF受信器、Perron/transfer、元の二interacting posterior、元の境界pair-Haar確率とADHの位相適合擬距離は不変更。

### 真正Cov上界からのHaar球質量1/17障害

- **元模型の無条件の点評価**：ACJの真正共分散分散上界`4*C_e(z)^2<=B_H^2`とADFの真のtransfer/プラケット上界`B_H^2<=K_H`を、各有限体積H、元の物理リンクe、元の境界対zにそのまま適用して`4*C_e(z)^2<=K_H`をLean4証明。独立した確率分布・抽象Covモデル・仮想距離へすり替えない。
- **数値的必要条件（単一球の証明書に限る）**：元pair-Haar実質量`ν_H(A)<=1/17`の任意集合Aについて`68*C_e(z0)^2*ν_H(A)<=K_H`。従ってADHのstrict条件`K_H<68*C_e(z0)^2*ν_H(ball)`を満たす元Haar球には必ず`ν_H(ball)>1/17`（約5.882%）が必要。元pair-Haar確率正規化`ν_H(A)<=1`から別途`C_e(z0)^2>K_H/68`も必要。これらはADHの**特定の十分条件**に対する必要条件であり、GI応答そのものの必要条件ではない。
- **同じ擬距離における真正Lipschitz半径の単調性**：`0<L1<=L2`なら`r(L)=|C_e(z0)|/(2L)`は`r(L1)>=r(L2)`。したがって**同一の元pair-Haar法則**に対して`ν_H(ball(r(L1)))>=ν_H(ball(r(L2)))`であり、68条件の右辺も悪化しない。さらに改善されたL1の真正Cov Lipschitz評価を**別途検証した場合**に限り、L2でのstrict数値条件からADHの元GI二乗平均証明書正値と、元二posteriorのsigned GI応答非零OPEN・正Haar質量領域に条件付き接続。
- **未証明の境界**：元SU(2)受信器に対する実数値Lipschitz定数、非零Cov点の数値振幅、元Haar球質量の具体値、1/17超過、68閾値の成立、全H一様評価、連続体4D Yang–Mills質量ギャップは未証明。ADHの擬距離は元位相と適合するが、物理的な数値距離として未校正である。

### exact-source CI・公理依存・マージ後push CI

- 定理PR #6136 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6136 — MERGED。新規Leanファイル`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNumericHaarMassObstructionV5_PZ37ADI.lean` 1件のみ、8定理・8件`#print axioms`、追加284行・削除0行。既存Lean・真正模型・root・workflow・pin不変更。
- 最終exact-source HEAD `635ac1fab2f281c6e062a1aca4ea530ca56e0fdb`、test-merge commit `f9fa80d685e99e7cf9b8e3fdecb9fd536bcebb87`、定理squash `b48204a99e89a454aac1bda0fd9d11fd34dfc303`のGit treeはすべて`8eab57b6412e94d2b087a1bc1cce4b52256584f1`で完全一致。
- exact-source CI #41329768683 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41329768683 — 11258/11258 Lean SUCCESS、8/8公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立completion receipt `event=pull_request`・`source_result=success`。
- マージ後push CI #41330387235 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41330387235 — 正本squash HEADで11258/11258 Lean SUCCESS、8/8標準3公理のみ、`sorryAx`・変更警告・変更エラーなし、独立completion receipt `event=push`・`source_result=success`。
- 初回CI #41329233315では元`CompactEnergyMismatchMoment.variance μ`が一変数関数であるのに対し`Var(F) E`と余分な引数を渡したLean elaboration errorが3箇所あった。依存ACJ定理の完全な引数と既存分散記法を確認し、`Var(F)`へ訂正。定理主張・仮定の緩和なし。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。docs-onlyではStrict Leanを起動しない。

### 次の研究課題 — ADJ（OPEN）

真正SU(2)境界配置の**数値校正された具体的な積距離**と元pair-Haar球質量下界、ACIの真正非零共分散の**数値振幅**、元FF受信器の真正Lipschitz定数をそれぞれ導出する。まずADHの特定十分条件に必要な球質量`>1/17`と点振幅`>sqrt(K_H/68)`の実現可能性を、有限Hの正確な物理量で検証する。存在・条件付き定理を数値的成功と同一視せず、全H一様性や連続体質量ギャップは別ゲートに保持する。

---

## 検証済み定理 — ADH（2026-11-01 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。P4-Q2-PZ37ADH定理PR #6133はMERGED、定理squash SHA `729b2138ffa234e2c0f57f5e21abc8107fca3be0`。元の有限体積interacting Wilson SU(2)、中心化Gauss-law源、元FF受信器、Perron代表・transfer、元の二interacting posteriorと元境界pair-Haar測度は不変更。

### 真正Cov非零点を含むOPEN Haar球と有限体積共通の球下界

- 固定結合は既存ADCの`b0=log(3/2)/64>0`。元の実共分散`C_e(z)=Cov_Haar(F_e(z),E)`と真正共分散二乗モーメント`S_e=∫C_e(z)^2 dν_H(z)`、ADFの元transfer/プラケット上界`K_H=6*P_H*exp(2*b0*A_H)*(exp(8*b0)^3-1)^2`を維持。
- 境界配置の**元の位相に適合する擬距離**によって`Metric.ball`を用いる。これは元のboundary pair-Haar確率法則・物理模型の置換ではなく、擬距離自体の物理的数値スケールを主張しない。
- **各真正リンクの無条件Haar球構成**：ACIの元共分散非零点`z_e`とACDの実Cov連続性から、各`e`について`r_e>0`が存在し、`z∈ball(z_e,r_e)`なら`|C_e(z)|>=|C_e(z_e)|/2>0`。元pair-Haarのopen-positive性から球は`ν_H(ball(z_e,r_e))>0`。ADEの元積分評価により`(|C_e(z_e)|/2)^2*ν_H(ball(z_e,r_e))<=S_e`をLean4証明。
- **固定H・全リンクに共通する実Haar球証拠**：真正リンク型が非空で固定有限`H`なら、有限個の半径、非零Cov振幅、正pair-Haar球質量の各最小値を取ることで、一組の`r_H>0`、`a_H>0`、`m_H>0`が存在。全真正リンク`e`について元境界点`z_e`を選べて、`ν_H(ball(z_e,r_H))>=m_H`かつ球上で`|C_e(z)|>=a_H`、従って`S_e>=a_H²*m_H`。`z_e`はリンク依存、三定数は固定H内でリンク非依存。
- **条件付き明示半径**：もし元の真正Covに`L>0`かつ全境界`z`に対して`|C_e(z)-C_e(z_e)|<=L*dist(z,z_e)`が別途検証されれば、`r_e=|C_e(z_e)|/(2*L)>0`が具体的に使え、同じ元Haar球の正質量とモーメント下界が従う。Lipschitz定数`L`自体がこの元Wilson模型で数値的に得られるとは未証明。
- **厳密68条件**：`K_H<68*C_e(z_e)^2*ν_H(ball(z_e,|C_e(z_e)|/(2L)))`が別途成立するなら、元GI二乗平均証明書`M_GI>0`、元の二interacting posteriorの実signed GI応答が非零となるOPEN・正pair-Haar質量領域が存在する。`272*(|C_e(z_e)|/2)^2=68*C_e(z_e)^2`は純代数的な等式。GI二乗平均の正値と実signed応答の符号を混同しない。
- **未証明の境界**：Lipschitz定数の具体値、球半径・元Haar球質量の具体的数値、`K_H<272*a_H²*m_H`および上記68比較、全Hで一様な下界、連続体4D Yang–Mills質量ギャップは未証明。証明済みなのは真正有限体積・各リンクに関する存在と厳密な条件付き数値還元。

### exact-source CI・公理依存・マージ後独立検証

- ADH定理PR #6133 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6133 — MERGED。新規Leanファイル`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCovarianceHaarBallsV5_PZ37ADH.lean`のみ、10定理・10件`#print axioms`、既存ファイル削除0。元模型・root・workflow・Lean/mathlib pin不変更。
- 最終exact-source HEAD `2c3a2078f736e8557e34a54514942c0081074dd4`、PR test-merge commit `d2059e95733f471751c09d9d3be983a21090641f`、定理squash `729b2138ffa234e2c0f57f5e21abc8107fca3be0` のGit treeはすべて `758fffa12c2b0e7a69830896420423bf6074819c` で完全一致。
- exact-source CI #41307792780 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41307792780 — 11257/11257 Lean SUCCESS、10/10公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立completion receipt `event=pull_request`・`source_result=success`。
- マージ後push CI #41308202510 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41308202510 — 定理squash HEADで11257/11257 Lean SUCCESS、10/10標準公理のみ、`sorryAx`・変更warning/errorなし、独立completion receipt `event=push`・`source_result=success`。
- 初回CIの局所記法`outer`・`μ`と`.IsOpenPosMeasure`の名前解決、`field_simp`後の余分な`ring`、`(|C|/2)^2`の`div_pow`/`sq_abs`正規化を、全ファイル・imports・固定mathlib APIを確認して修正。証明条件緩和なし。Lean`v4.30.0-rc2`、mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。文書のみのStrict Leanは起動しない。

### 次の研究課題 — ADI（OPEN）

同一の真正Wilson受信器について、非零Cov点での数値的下界、元境界配置上の物理的な距離と定量Lipschitz定数`L_H`、元SU(2)・有限リンク積のHaar球質量の明示的下界を別途確立し、`K_H<68*C_e(z_e)^2*ν_H(ball)`の有限体積数値判定へ接続する。半径・Haar測度の存在を数値評価や体積一様性と同一視しない。

---
## 検証済み定理 — ADG（2026-11-01 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`、default `main`は文書ミラーのみ。P4-Q2-PZ37ADG定理PR #6130はMERGED、squash SHAは`41cd7430003e284f3d5ec59b9740bcd68d5de227`。元の有限体積interacting Wilson SU(2)、中心化Gauss-law物理源、FF受信器、正Perron代表、更新後transfer section、元の二interacting posteriorと境界pair-Haarを厳密に保持しています。

### 固定有限体積・全真正リンクに共通する両符号Cov領域

- ADCの真正固定結合`b0=log(3/2)/64>0`、ACJの元境界Cov`C_e(z)`・二乗モーメント`S_e=∫ C_e(z)^2 dν_H(z)>0`、ADFの元transfer・プラケット明示上界`K_H=6*P_H*exp(2*b0*A_H)*(exp(8*b0)^3-1)^2`を同一模型で使用。
- ADEの有限リンク最小値から`s_H=min_e S_e>0`が存在。ACJの真正正負のOPEN領域`A_e^+={C_e>sqrt(S_e/2)}`、`A_e^-={-C_e>sqrt(S_e/2)}`は各リンクで実pair-Haar質量`ν_H(A_e^±)>=S_e/(B_H²-2*S_e)>0`を持つ。
- **ADGの新規全リンク共通定量証拠**：`a_H=sqrt(s_H/2)>0`、`m_H=s_H/(K_H-2*s_H)>0`とすると、各有限Hのすべての真正リンク`e`について両領域がOPENで`ν_H(A_e^+)>=m_H`、`ν_H(A_e^-)>=m_H`、領域内でそれぞれ`C_e(z)>a_H`、`-C_e(z)>a_H`が成立。分母の正値はACJの`B_H²-2*S_e>0`、ADEの`s_H<=S_e`、ADFの`B_H²<=K_H`による形式証明。
- **Sの値を入力しない独立の局所証拠**：ACI・ACD・ADEから各真正リンク`e`で実CovのOPEN集合`U_e`、振幅`a_e>0`、実Haar質量`ν_H(U_e)>0`、全`z∈U_e`で`|C_e(z)|>=a_e`が存在。有限個の真正リンク上でこれらの振幅・質量をそれぞれ最小化して別の`a'_H>0`、`m'_H>0`を構成し、全リンクで`ν_H(U_e)>=m'_H`、`|C_e(z)|>=a'_H`、`S_e>=(a'_H)^2*m'_H`をLean4証明した。選択したOPEN集合はリンクに依存するが、二定数はリンクに依存しない。
- **数値条件は別問題**：局所証拠について`K_H<272*(a'_H)^2*m'_H`を別途満たせば、固定Hの全真正リンクで元GI二乗平均証明書`M_GI>0`。元の二interacting posteriorの実signed GI応答が非零となるOPEN・正pair-Haar質量集合も各リンクで存在する。これは既存ADE・ADFへの厳密な条件付き接続であり、signed応答の符号を断定しない。
- **証明と未証明の境界**：両符号OPEN領域の存在、リンク共通の正振幅・正Haar質量下界、および局所領域からの正モーメント下界は無条件で形式化完了。正の共通定数の**数値評価**、`K_H<272*(a'_H)^2*m'_H`、全Hに一様な定数、連続体4D Yang–Mills質量ギャップは未証明。存在の定理を数値優越の証明と混同しない。

### exact-source CI・squash・マージ後push CI

- 定理PR #6130 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6130 — MERGED。新規Leanファイル`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformTwoSignCovarianceV5_PZ37ADG.lean` 1件のみ、2定義・9定理・9件`#print axioms`、405行追加・削除0。既存Lean・root・toolchain・workflow・物理模型は不変。
- 最終exact-source HEAD `432998c404d4d3553e642e95e7914338d38fa6f9`、test-merge commit `5e7f4257c82e1f24cfbcb5f9730b8a29af237418`、定理squash `41cd7430003e284f3d5ec59b9740bcd68d5de227`はすべて同じGit tree `5f4796263704cf58227db3efa017dd83c3a0d266`。単一新規ファイルによるappend-only。
- exact-source CI #41303675413 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41303675413 — `11256/11256` Lean SUCCESS、9/9公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error `0/0`、独立receipt`event=pull_request`・`source_result=success`。
- マージ後push CI #41304074956 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41304074956 — squash HEADで`11256/11256` SUCCESS、9/9標準公理のみ、`sorryAx`・変更警告・変更エラーなし、独立receipt`event=push`・`source_result=success`。
- 初回CI #41303150874のLean局所記法`S`と同名束縛変数の構文衝突を小文字変数に修正。連鎖した定理名解決エラー・未証明依存は全て解消。9定理の主張・仮定を弱めていない。Lean`v4.30.0-rc2`、mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。
- docs-onlyはREADME・ROADMAPの同文追記のみ。Strict Leanを別途起動しない。

### 次の研究課題 — ADH（OPEN）

実Covを非零にする具体的な元境界配置`z0`における`|C_e(z0)|`の数値的下界、受信器の局所連続性に対する**明示的な近傍半径**、その近傍の真正pair-Haar質量の明示的下界を調べる。これらが分かれば`(a'_H)^2*m'_H`を数値比較へ進められる。固定Hの成立、全リンク共通、全H一様を区別し、未証明の正値・質量ギャップを仮定しない。

---

## 検証済み定理 — ADF（2026-11-01 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。P4-Q2-PZ37ADF／定理PR #6127 MERGED、定理squash SHA `104a6d2dde97b6fcbe5d2031942d0bfba4b0cfb4`。ADE以前の証明を保持し、元の有限体積interacting Wilson SU(2)、中心化Gauss-law物理源、FF受信器、正Perron代表、更新後transfer section、元の二interacting posterior、境界pair-Haar、根・workflow・toolchain pinは無変更。

### 真正物理transfer・プラケットに基づく明示的FC上界

- 固定結合は既存ADCの`b0=log(3/2)/64>0`。元の実Wilson一スラブ作用量の上界を`A_H=2*(length(原空間plaquette list)+length(原空間link list))`、実空間プラケット数を`P_H=Fintype.card(原空間plaquette)`とする。
- **追加仮定なしの真正transfer下界**：既存の原kernel global minorizationと定数物理単位ベクトルから`||T_(H,b0)||>=exp(-b0*A_H)>0`、従って`||T||^(-1)<=exp(b0*A_H)`。別の形式証明から元中心化Gauss-law源`||f0_H||²<=6*P_H`。定量性は有限Hに限定。
- **ADF新規無条件定理**：元FC上界`B(H,b0)`に対して`B(H,b0)² <= K_H`、`K_H := 6*P_H*exp(2*b0*A_H)*(exp(8*b0)^3-1)^2`。従来の未知の物理transferノルムを、実格子作用量と実プラケット数で明示的に支配する。固定`b0`では`exp(8*b0)^3=exp(24*b0)`。
- **真正Cov二乗モーメントとの条件付き比較**：各原リンク`e`で`K_H<272*S(H,b0,e)`を別途示せば、既存ADEより真正GI二乗平均証明書`M_GI(H,b0,e)>0`。さらに元の二interacting posteriorの実signed GI応答が非零となるOPEN・正pair-Haar質量集合が存在する。証明書の正値性とsigned応答の符号は同一視しない。
- **実Cov開領域による十分条件**：OPEN集合`U`で`a>0`かつ`a<=|Cov(z)|`が全`z in U`に成り立ち、`K_H<272*a²*ν_H(U)`が別途成立すれば、同じ真正GI二乗平均証明書とsigned GI非零開領域が得られる。
- **固定Hの全リンクへ**：既存ADEの正定数`s_H=min_e S(H,b0,e)>0`について`K_H<272*s_H`が別途成立すれば、固定有限Hの全真正リンクで`M_GI>0`。有限H依存定数と全H一様定数は区別する。
- **非正証明書の障害**：元`M_GI<=0`なら`272*S(H,b0,e)<=B(H,b0)²<=K_H`。十分条件の障害のみを述べ、実signed GI応答の全消失を導かない。
- **未解決の本質**：真正Wilson模型で`K_H<272*S`または`K_H<272*a²*ν_H(U)`が成立することは未証明。global actionの指数因子は粗い証明経路の体積依存性を露わにするだけで、物理transferの実際の悪化、全H一様性、連続体4D Yang–Mills質量ギャップは示さない。

### exact-source CI・公理監査・マージ後独立検証

- 定理PR #6127 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6127 — MERGED。新規Leanファイル1件、1定義・8定理・8`#print axioms`、257行追加・削除0行。原模型、既存Lean、pin、root、workflowは不変更。
- 修正済みexact-source HEAD `6ba61fd075d9e16db47f73869532480ca9fdb1c8`、CI test-merge commit `21028d9b3c9de6ae3aee38308f66e932063fe044`、squash `104a6d2dde97b6fcbe5d2031942d0bfba4b0cfb4` のGit treeはすべて `bb3a6fd435dcb08cdd6314f46816b541ff5da051` で一致。
- exact-source CI #41301330625 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41301330625 — 11255/11255 Lean SUCCESS、8/8公理依存は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立completion receipt `source_result=success`。
- マージ後push CI #41301819870 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41301819870 — 同じsquash HEADで11255/11255 Lean SUCCESS、8/8標準3公理のみ、`sorryAx`なし、変更warning/error 0/0、独立completion receipt `event=push`／`source_result=success`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`維持。
- 初回CIの作用素ノルム型推論、同一有限集合の`Fintype`インスタンス相違、`≤`と`<`の推移律誤用を、完全修飾作用素名・固定mathlibの`Fintype.card_eq_nat_card`・`lt_of_le_of_lt`で修正。主張・仮定の緩和なし。README・ROADMAPは正本とmain文書ミラーの同文追記を行い、docs-only Strict Leanは起動しない。

### 次の研究課題 — ADG（OPEN）

元の真正共分散`S(H,b0,e)`および実Cov開領域`a²*ν_H(U)`へ格子・作用・Perron/transfer・Haarの下界を接続し、`K_H<272*S`がいずれかの有限Hで成立するかを実際に評価する。粗いglobal action指数依存を改善できるかも調査するが、正値の存在だけを数値的優越性や体積一様性と誤認しない。

---

## 検証済み定理 — ADE（2026-11-01 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAP文書ミラーのみ。P4-Q2-PZ37ADE／定理PR #6124 MERGED、定理squash SHA `e21981875aae3c4c172a2e3758767e99d160fdd3`。ADCまでの既存定理を保存し、有限体積の真正interacting Wilson SU(2)、中心化Gauss-law源、元FF受信器、正Perron ground代表、更新後transfer section、元の二interacting posteriorと元境界pair-Haar測度を変更していません。

### 実共分散モーメントの厳密定量閾値

- ADCで固定済みの真正正結合`b0=log(3/2)/64`、元の共分散二乗モーメント`S(H,b0,e)>0`、元のFC上界`B(H,b0)²>0`、正規化した四成分信号`u(H,b0,e)=16*S/B²`について、`u>1/17` **iff** `B²<272*S`をLean4で証明しました。元GI二乗平均証明書の正値性に対する**条件付き十分条件**です。
- **実物理量のみによる条件付きGI結論**：`B²<272*S`なら、元の真正GI二乗平均証明書`M_GI>0`。既存ACOより、元の二interacting posteriorのsigned GI応答が非零となるOPEN・正の元pair-Haar質量集合が存在します。二乗平均証明書と実signed GI応答は区別します。
- **実Cov開領域の普遍的下界**：元outer空間の任意のOPEN集合`A`で`a>0`かつ`a<=|Cov(z)|`（全`z in A`）なら`a²*ν_H(A)<=S`。従って具体的な数値条件`B²<272*a²*ν_H(A)`を独立に示せば、同じ真のGI二乗平均証明書とsigned GI非零開領域が従います。
- **この実Cov開領域は真正模型で存在**：既存ACIの元リンクにおける非零CovとACDの連続性・元Haar正質量から、各有限H・b0・真正リンクeについて、実際に`a>0`、OPEN`A`、`ν_H(A)>0`、`a<=|Cov|`を満たす証拠が存在し、`0<a²*ν_H(A)<=S`をLean4で構成しました。ただし`272*a²*ν_H(A)>B²`はここからは**導かれません**。
- **物理的数値障害**：元GI二乗平均証明書が非正なら`272*S<=B²`。さらに任意の上記実Cov開領域`A`と閾値`a`に対し`272*a²*ν_H(A)<=B²`。これは証明書／十分条件の障害であり、signed GI応答の全消失ではありません。
- **有限体積における定数化**：真正リンク型が非空で固定Hなら、有限個の元Covモーメントに対して`s_H=min_e S(H,b0,e)>0`が存在し、eに依存しない正定数が得られます。さらに`B(H,b0)²<272*s_H`が別途成立すれば固定Hの全リンクで正のGI二乗平均証明書が従う条件付き定理を証明。正の`s_H`の存在だけではこの数値272閾値は保証しません。

### exact-source CI・公理・正本保全

- 定理PR #6124 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6124 — MERGED。新規Leanファイル1件、1定義・16定理・16`#print axioms`、359行追加・削除0行。既存Lean/model/root/toolchain/workflow/pinは無変更。
- 完全修正後exact-source HEAD `e28ddd26c57b01efbe6605b8031e540b2097446b` と定理squash `e21981875aae3c4c172a2e3758767e99d160fdd3` のGit treeは `563057298367f49c1b98a685a6d6d5835b171479` で完全一致。Lean4局所表記`hb0.le`の非展開を完全修飾正値定理へ修正、既存定理の仮定緩和なし。
- exact-source CI #41297952511 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41297952511 — 11254/11254 Lean SUCCESS。16/16公理依存`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立completion receipt SUCCESS。
- マージ後push CI #41298470345 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41298470345 — squash HEAD上のLeanステップ・workflow・独立completion receiptすべてSUCCESS。
- Lean`v4.30.0-rc2`、mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`維持。docs-onlyではStrict Leanを起動しません。

### 次の研究課題 — ADF（OPEN）

固定結合`b0`の元Perron/transferノルムを含むFC上界`B(H,b0)²`と、元Cov二乗モーメント`S(H,b0,e)`について、既存の具体的な格子・作用・転送の評価から`B²<272*S`、または実Cov開領域寄与`B²<272*a²*ν_H(A)`をさらに定量化できるかを検討する。とくに体積H依存の`s_H>0`と体積H一様な実数下界を明確に区別し、未証明の係数比較・連続体4D質量ギャップを既成事実としません。

---

## 検証済み定理 — ADC（2026-11-01 JST）

唯一の定理正本は`formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラー。P4-Q2-PZ37ADC／定理PR #6119はMERGED、定理squash SHAは`99de1c420935a2c48440a94ad0951209fda5033d`。ADBまでの既存形式証明は維持し、元の有限体積interacting Wilson SU(2)、中心化Gauss-law物理源、FF受信器、正Perron ground代表、更新後transfer section、同じ二interacting posterior、真正境界pair-Haar測度は変更なし。

### 真正結合の固定・厳密有理閾値・有限体積のリンク一様定数

- **厳密な正結合**：`b0=log(3/2)/64>0` を定義。`exp(64*b0)=3/2`、既存ACPの真正posterior指数差平方`tau(b0)=(exp(64*b0)-1)²=1/4`をLean4で証明。従ってADBのFC割合判定に現れる`tau/(tau+4)=1/17`が厳密有理定数となります。
- **元Wilson GI二乗平均証明書の正確な符号**：ADBの真正比率`u(H,b,e)=16S(H,b,e)/B(H,b)²`、`v(H,b,e)=Wbar(H,b,e)/B(H,b)²`を使うと、各有限H・元物理リンクeで`M_GI(H,b0,e)>0` **iff** `v(H,b0,e)<16*u(H,b0,e)`。これは平均二乗証明書の判定であり、signed GI応答そのものの同値ではありません。
- **数値閾値を伴う条件付き証明**：真正FC残差配分`u+v<=1`から`u(H,b0,e)>1/17`なら`M_GI(H,b0,e)>0`。既存ACOにより元の同じ二つのinteracting posteriorのsigned GI応答が非零となるOPEN・正pair-Haar質量領域が存在します。逆に`M_GI<=0`なら`u<=1/17`。厳密に`1/17`を越えること自体は元模型で未証明。
- **有限リンク集合から正の定数を得る**：固定有限Hで真正リンク型`Link(H)`が非空なら、全ての元リンクで`u(H,b0,e)>0`であり、型が有限であることから**リンクに依存しない正の実定数**`c_H=min_e u(H,b0,e)>0`が存在することを形式証明。さらに`c_H>1/17`を追加の数値条件として別に課す場合に限り、固定Hの全リンクで上記正値性が従います。正の`c_H`の存在と`c_H>1/17`は区別します。
- **体積間の権限境界**：一つの実定数`c>1/17`について全ての有限体積`H`と元リンク`e`で`c<=u(H,b0,e)`を別途証明できれば、同じ固定結合で全体積の元GI二乗平均証明書が正となる条件付き定理を形式証明しました。実際の模型にそのような`H,e`一様下界が存在することは**未証明**であり、体積一様coercivityや連続体Yang–Mills質量ギャップは主張しません。

### exact-source CI／公理依存／append-onlyガバナンス

- 定理PR #6119 https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6119 — MERGED。新規Lean1ファイル・1定義・12定理・12`#print axioms`、281行追加・削除0、元物理模型・既存Lean・root・pin・workflowの変更なし。
- 初回source検証済みHEAD`d1bb7b7d86728fa73815c9aa7a928f11037ad0a4`に続き、ADB文書同期を親コミットとしてfast-forward保持した最終exact-source HEAD`729047939706ebd725b38bed0b9312cd55b46438`で再検証。最終sourceとsquash`99de1c420935a2c48440a94ad0951209fda5033d`のGit treeは`a489fe48e133e23fe015d801cbc0471cfdd4d38d`で完全一致。改変・force-pushなし。
- 正本baseと完全一致したexact-source CI #41296069589 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41296069589 — Lean11253/11253 SUCCESS、12/12公理依存は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立completion receipt SUCCESS。
- マージ後push CI #41296471435 https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41296471435 — squash HEAD上のLean step／workflow全体／独立MCP completion receiptすべてSUCCESS。
- Lean `v4.30.0-rc2`、mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`維持。docs-only Strict Leanは起動しません。

### 次の物理的・形式的課題 — ADE（OPEN）

固定結合の数値閾値を真正共分散モーメントの定量評価に還元する：`u(H,b0,e)>1/17`は正の`B(H,b0)²`のもとで`B(H,b0)²<272*S(H,b0,e)`と同値。まずこの厳密換算をLean4で明示し、その後、元Perron／transfer normを含む`B`と元境界pair-Haar上の`S`の間に、数値272を満たす証明済みの物理評価があるか検討する。固定Hのリンク最小値と全Hに共通する数値下界は分離し、未証明の下界を仮定なしで成立したと主張しない。

---

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


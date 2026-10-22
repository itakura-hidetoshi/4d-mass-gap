# MGAP4D — 証明ロードマップ（P4-Q2-OH統合後）

**2026-10-22 JST · 唯一のLean定理正本：`formal/real-hilbert-uniform-coercive-strong-limit` · 最新検証済み定理統合点：[`b203e5361ec8148c9aaa22f4c023be2dd67268a4`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/b203e5361ec8148c9aaa22f4c023be2dd67268a4)（[#5793 OH](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5793)）**

**到達状況：** 元の相互作用Wilson二posterior・真正Gauss-law物理源・Perron半密度を変更せず、LM〜MKの空間GI、NT〜OCの完全Gaussian、ODの真正posterior差分汎関数とFF物理受信器の厳密な一致、OEの同一物理源Uの二文脈強制性、OF/GXの全有限Krylov深さ・非負fineでの零次源＝U、OGの固定スケール同一文脈all-depth真正HF GI下界を証明。**OH #5793**では元の二行から一行を先に選び、その同じ真正Wilson文脈で全深さrの零次selectorに `(Q_GI/N_H)/(20 E_b²)` 以上の二乗検出下界、正確な係数核finrank＝r、および各深さの検出される開係数近傍をLean4で証明済み。高次係数核に属する係数が非零物理源を合成するとは証明していない。全係数正fine非退化性、体積一様U0、スケール間同一endpoint、H1-C3、連続体質量ギャップはOPEN。

**[プロジェクトの数学的定義・数式・再現手順 → README.md](README.md)**

## 0. Authority / CI — status claims must be reproducible

| 項目 | 正確な検証結果 |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| 定理の唯一正本 | `formal/real-hilbert-uniform-coercive-strong-limit`（default `main`ではない） |
| 最終検証済み**定理-bearing**マージ点 | `b203e5361ec8148c9aaa22f4c023be2dd67268a4` — OH #5793 |
| OHの検証**source HEAD** | `182d1b7685765532a2d2c535c43eafdc684e6029`（squash SHAと区別） |
| [OH exact-head CI #39729769207](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39729769207) | SUCCESS、Lean **10869/10869**、変更OH warning/error **0/0** |
| OH公開定理の`#print axioms` | **6/6**、`sorryAx`なし、MCP completion receipt SUCCESS。3件は標準3公理のみ、3件は既存有限格子`native_decide`依存を継承。新規公理なし |
| Lean / mathlib pin | `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| 現在のbranch HEAD | [毎回GitHubで再観測](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) |

ここに固定したSHAは**2026-10-22時点の検証済み定理統合点**であり、README/ROADMAPのdocs-onlyマージによってbranch HEADが進んでも、定理の新規検証を意味しない。判断の優先順位は **fresh exact authoritative SHA → Lean定理と前提・import全文 → そのsource SHAのCI・公理監査 → 文書 → 以前の記録**。

### 重要な区別

- `Q_post = ∫(p_{0,b}-p_{π,b})²dν`：過去のGI/source比較に現れる真正posterior**密度差**。
- `Q_GI = Σ_{p∈P_H}d_p²`：LY以降の真正Wilson**局所GI minor二乗エネルギー**。`d_p=||T_{H,b}||²Δ_p`、`N_H=|P_H|`。
- `E_b=e^{8b}(e^{16b}-e^{-16b})`：元のone-link joint-density Harnack等からLWで得る正のコントラスト尺度（`b>0`）。
- `k_{H,b,e,e',z,z'}=(Q_GI/N_H)/(10E_b²)`。**`Q_GI>0`が体積ごとに成立しても`inf_H k_H>0`は従わない。**

`A_W`（非正規化の原Wilson Haar-reference）、`D₁₂`（正規化物理条件射影のDirichlet）、元のGI検出器、`p`ごとに変わる物理源のGram、fine-evolution/endpoint、連続体Hamiltonianは**異なる作用素・検証対象**。

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
| **F：positive fine / arbitrary r** | fine `t=0` の全有限r、または`r=0`の全非負fineで`ker S=ker Φ`、特定の正fine innovation witness | `t>0`かつ任意`r>0`で`I_phys=S(ker Φ)=0`は OPEN |
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

### 2.6 OE–OH：真正物理GI signed受信器像・同一文脈・一行rank

- **OE [#5789](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5789)**：ODの厳密な二posterior signed汎関数評価をLO〜MKの真のGauss-law物理源に接続。元の二文脈局所minorから物理的二座標源 `xU+yW_pU` の二行signed receiverの共通核が選択文脈で自明であることを証明。MF/MKの元の `Q_GI/N_H` 一次下界をそのまま受信器へ輸送し、`x=1,y=0` により**プラケットに依存しない同一物理源U**への正の下界を取得。これらは以前のLB/HY/IDの非零GI witnessを置き換えず、厳密な受信器表示・定量値の接続を強めるもの。
- **OF [#5790](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5790)**：GXにより実際のfine-right zero-selector `a⁽⁰⁾_r` のGauss-law Hilbert源が `S_{n,r}(a⁽⁰⁾_r)=U` と厳密に等しいことを使い、任意有限Krylov深さ・任意非負fine couplingでOEの元の二posterior signed受信器下界を零次選択源に輸送。frozen `b_n>0` は別途固定する。

- **OG [#5791](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5791)**：HFの真正right-Krylov係数GI modal検出器が零次選択係数についてODのsigned二posterior物理受信器（同じU）と厳密一致することをLeanで証明。任意の有限深さr,sで同一スケールn・同じ物理文脈のmodal GI実数値は等しい。さらに**先に実際のWilson文脈z,z'を選んでから、全有限rで同一正のQ_GI/N_H下界を示す** `∃z,z' ∀r` を証明。exact-head #39725595181、Lean 10868/10868、5/5公理監査、sorryAxなし、変更警告・エラー0、MCP receipt SUCCESS。3件は標準公理のみ、2件は既存native_decideを継承する。新規公理なし。

- **OH [#5793](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5793)**：OGの真正二行GI frameから、固定スケールnで同じ実Wilson文脈の**一行を深さrと独立に選択**。この真のHF modal検出器に対して全有限深さで正準零次係数の二乗応答が `(Q_GI/N_H)/(20 E_b²)>0` 以上であること、mathlibの線形rank-nullityとHF既存定理から係数核のfinrankが正確にrであること、および各深さで同じ受信器に検出される正の開係数球があることをLean4で証明。exact-head CI #39729769207、Lean 10869/10869、6/6公理監査、sorryAxなし、変更警告・エラー0、MCP receipt SUCCESS。元の二posterior・Gauss-law源・Perron半密度はそのまま。**係数核の非零ベクトルが非零物理源かは未証明**。

**量化の境界：** OGで閉じたのは**固定nにおける零次selector**の同一源・同一文脈・深さ互換であり、任意係数列や異なる格子スケールでの同一endpointではない。Q_GI/N_Hの正下界は有限体積の選択文脈に依存する。
### OI：OHの真正GI係数kernelを元の物理Hilbert源へ輸送する証明課題

1. **元のGI係数kernelの物理Hilbert源への厳密分解。** OHの選択した一行で真正零次GI係数応答は非零なので、任意の実右Krylov係数aを `a=k+(Φ(a)/Φ(a₀))a₀`、`Φ(k)=0` と具体的に分解できる。HJ本来のsource synthesisを使って `S(a)=S(k)+(Φ(a)/Φ(a₀))U` をLeanで証明し、同じ真正posteriorのOD signed FF受信器で `S(k)` の応答が消えることを証明対象にする。ただし**一行のker Φ内の係数から非零物理不可視源を結論しない**。全文脈検出器、異スケールendpointと定量誤差は別ゲート。
2. **一リンク一致から本来のtransferとendpointへのintertwining。** ODは固定 `H,b,e,z` のFF fiberとGI gapを正確に結ぶが、`Φ_{n,r}`、`S_{n,r}`、正fine `t`、Perron半密度と任意Krylov `r` を跨ぐ可換図式を与えていない。真のWilson作用素でそれを証明するかobstructionを記録する。
3. **非退化性を既存GI witnessから導出可能か判定。** LM・LOの真正physical minorとNYのsigned Gaussian厳密正値を接続する際、必要なのが同一の物理線形汎関数であること、どの局所source familyが実際に検出されるかを証明する。存在を仮定したrank・zero-invisible-sectorに置換しない。
4. **定量性は別途。** 有限点行列 `M^{-1}` の存在・有限補間は一様 `λ_min` や `Q_GI/N_H` の下界ではない。cross-volume comparison、尺度・sourceの一致、空間tailと可和性を維持する。

## 3. 次の核心：本当に不足する数学的入力

### Gate U0 — 真正Wilson GI密度または同等のframe coercivityを一様化

**求める条件の一例：** 自然な有限格子・coupling schedule・相容れる物理文脈族に対して、`Q_{\rm GI}(H,b_H,\ldots)/N_H`の十分な正下界と`E_{b_H}`の同時制御を**真のWilson積分から導く**。より直接的には`k_H=(Q_{\rm GI}/N_H)/(10E_{b_H}²)`そのものの有効な正下界、または必要な物理source作用素の相当する非退化性を証明してもよい。

**既存証明からは出ないこと：** `∀H\,∃(z_H,z'_H),Q_H>0`は`∃c>0\,∀H,Q_H/N_H≥c`を含意しない。さらに文脈や選択plaquette`p_H`が各Hで独立に選べるだけでは、projective/物理時間の**同一source family**は得られない。`E_b`の一様上界だけでも`Q_{\rm GI}/N_H`の下界は得られない。

**優先して調べる真の対象：** signed posterior receiverの空間Wilson局所minorの二点相関、局所感度の位置依存、真正Wilson fiber-Haar posterior energy、volume依存の重なりや相関の減衰。Dobrushinをデフォルトの代替模型として再構成しない。**証明可能な新しい定理と、未証明の推測を必ず分ける**。

### Gate E — 空間`p`依存Gramを同一のendpoint物理源へ接続

MF–MKの量化は`\sum_p R_p(x,y)`や`∃p\,R_p(x,y)`で、`R_p`の物理源は`xU+yW_{H,p}U`。高次Krylov/endpointで必要な`S_{n,r}a`、真のfine transfer/receiver、実際のoriginal二posterior GI detector`Φ_{n,r}`と**自動的には等しいものではない**。

必要な証明は、実際のendpoint source写像で選択源・平均frameをtransportした際に、同じsigned GI応答・ノルム・誤差がどう変化するかという**具体的なintertwining / interpolation / controlled remainder**。架空の等長同型やrow rankで代用しない。LM/LNにglobal original source planeの非零性があることと、任意Krylov源へのinjectivityを混同しない。

### Gate F — positive fine coupling・高次Krylovの全源分離

真の`S_{n,r}`と`Φ_{n,r}`の組に対し、物理的不可視部分`I_{\rm phys}=S_{n,r}(\ker\Phi_{n,r})`を考える。

- **CLOSED boundary:** `t_{n+1}=0`で全有限`r`、または`r=0`で全`t_{n+1}≥0`の`ker S=ker Φ`。
- **OPEN interior:** `t_{n+1}>0`かつ`r>0`の任意深さで`I_{\rm phys}=0`、あるいは真正な不可視セクターの扱い。初期のrank-one・zero-selector・個別innovation成功を全源陽性へ読み替えない。
- Gate Eのtransportが成立しても、**同じ全source spanへの分離・Coercivity**を別途示す必要がある。

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
4. 上の材料を使い、**positive fine × arbitrary Krylov r**で真の`I_{\rm phys}`消去または定量的代替を進める。Dobrushin依存経路へ自動的に戻さない。
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
| **真正物理GI signed〜right-Krylov一行frame：OE–OH** | `OriginalPhysicalSignedReceiverNonannihilationV5_OE` / `OriginalKrylovZeroSelectorSignedDensityFloorV5_OF` / `OriginalZeroSelectorAllDepthSameContextGIFrameV5_OG` / `OriginalOneRowAllDepthModalRankOpenV5_OH` | 元の二posterior signed物理受信器、真正零次係数源、選択文脈の全r等式に加え、一つの真正受信器行の半分下界・核finrank r・開係数球 |

## 7. CIを効率的に保ちながら厳密性を保つ

定理を新しく書いた場合は次を省略しない。

- 定理正本branchのfresh SHA、**変更Lean全文**、import先と真正物理定義、実際に必要な前提条件を再観測する。
- pinned Lean/mathlibの既存補題を優先し、数学的に別物のindependent-Haar検出器・架空のrank/source・未検証uniform条件で不足を埋めない。
- **変更した依存の最大leaf**に対する`lake build`、CI exact source SHA、変更ファイルのwarning/error 0件、全公開`#print axioms`で`sorryAx`なし、独立MCP completion receipt SUCCESSを確認する。既存有限格子の`native_decide`由来の依存は「新規公理」と混同しない。
- 変更が`README.md`/`ROADMAP.md`だけの場合、現在の`PR Lean Fast Check`はパスフィルタで**Lean CIを起動しない**。Markdown表示・相互リンク・正本SHAを直接点検し、1万以上のLeanモジュールを再ビルドしない。Lean変更時のキャッシュキーはpinned toolchain/manifest、authoritative baseと安全なPRリトライscopeで扱い、不要なフルビルドを繰り返さない。
- PRソースCI成功後に定理正本へ統合し、**squash SHAとsource SHAを別々に記録**。docs-onlyマージを新しい数学的達成と数えない。

再現例（**検証済みOH source**を含むtheorem-bearing mergeを利用）：

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch --detach b203e5361ec8148c9aaa22f4c023be2dd67268a4
cat lean-toolchain
# optional when available: lake exe cache get
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOneRowAllDepthModalRankOpenV5_OH
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

これらは**有限モデルでどこまで実際に証明したか**を表すリンクであり、Yang–Mills Millennium Prize問題の解決宣言ではない。より古いステップごとのPRと定理の履歴はGit historyに残してある。

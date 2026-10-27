# MGAP4D — 証明ロードマップ（P4-Q2-PZ37ZA #5935統合済み／次は全リンク・全文脈の真正GL質量一様制御とendpoint source transport）

**2026-10-27 JST · 唯一のLean定理正本：`formal/real-hilbert-uniform-coercive-strong-limit` · 最新検証済みtheorem-bearing squash HEAD：[`56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300)（[#5935 PZ37ZA](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5935)）。default `main`は定理正本ではない。**

**最新到達（PZ37ZA）：** 元の真正SU(2) Wilson・二相互作用posterior・Gauss-law物理Hilbert・参照積Haar・frozen/fine結合を保持。PZ37Q–Yで全有限Hの小正fine三モード物理rank3・元の3モードGL積分Gram coercivityと `det G_H^GL≥c_H³D3(H,t)>0` を証明済み。PZ37Z #5933は異なる量 `Q_{H,b}(e,e',z,z')=Σ_{p∈P_H}d_{H,b,p}²` の `Q_H/N_H` に関し、文脈選択型の一様正下界と固定絶対閾値・正のGI活動割合の同値を証明した。しかし**PZ37ZA #5935でこの二文脈補償済みGI densityの実在側を否定した**。元の四リンク支持と有限重なり（24）、中心化Wilsonプラケットの積Haar独立性、補償済みGI二文脈汎関数ノルム `≤2E_b²` から、**全H・全リンク・全境界文脈で `Q_H≤96E_b⁴`**。実際のプラケット数 `N_H≥2(H+1)` により**固定 `b≥0` の `Q_H/N_H` はどのH依存文脈を選んでも一様正下界を持てない**。変動 `b_H` で元のHarnack共通上界 `(4E_{b_H}²)²≤K` を置けば `Q_H≤6K` で同じ結論。PZ37Zの同値は論理的に正しく、双方が偽となる。**限定：** 二文脈補償済み密度のno-goであり、元の全リンク・全文脈GL積分質量の一様coercivity、元の3モードの有限H正値性、endpoint E、任意深さF、強極限H1–H4・4D Yang–Mills質量ギャップの否定ではない。次に必要なのは十分条件の言い換えでなく、同一source/endpointに沿う真正full-link GL積分・相関の解析的一様評価。

**[プロジェクトの数学的定義・数式・再現手順 → README.md](README.md)**

## 0. Authority / CI — status claims must be reproducible

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

# P4-Q2-PZ37AIM — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、両端halfweight、ZW符号付き物理L²源と既存連続代表、真正空間積Haar、元のAIG全余裕と負領域、既存定理・仮定、固定Lean/mathlib、workflowを保持した。

## 1．検証済みソースと実際の統合

| 項目 | 確認した値 |
| --- | --- |
| 定理PR | [#6533](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6533)、MERGED |
| 基礎canonical formal HEAD | `f19c83c3d1a93995f37114062d478fa3deb8ab4f` |
| Exact-source HEAD | `0cdc195e04ca834089cf2fc4ef9070758965a586` |
| CIが実際に検査したtest-merge HEAD | `e825b10ae847d74125f966d1ba6f91f090560e33` |
| 定理squash | `52c14df9084213b1b36442c9bb618a019fdb7414` |
| source／test-merge／squash共通Git tree | `df29dee41a4f73050a788dcf5a1a269ff0883ffb` |
| source／squash共通Lean blob | `9d77dcb5dfa7dbb362066d1ac7f2fa55b6b53bc6` |
| Lean source SHA256 | `75d74a42e35e265f4dd58a452099bc1f81de2d62d4709a64ec057d3f47407ef6` |
| 変更範囲 | 新規Lean 1件・398行・20719 bytes、23定理＋2定義、既存ファイル変更0、削除0 |
| [Exact-source CI #42489780978 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42489780978/attempts/1) | workflow completed／SUCCESS |
| 必須Lean job | `128759419458`、completed／SUCCESS |
| 必須Lean step 17 | Run changed Lean fast check、completed／SUCCESS |
| Lake依存閉包 | **11,401／11,401 SUCCESS** |
| 新規AIM leaf実ビルド | **37秒** |
| 公開宣言／print命令／実際のaxiom出力 | **25／25／25**、一対一一致 |
| 公理出力の欠落／余剰／重複 | **0／0／0** |
| 公理依存 | 全25件が `propext`・`Classical.choice`・`Quot.sound` のみ |
| 完成した診断ログのsorryAx | **0件** |
| 完成した診断ログのLean error行 | **0件** |
| 変更AIM Lean warning／error | **0／0** |
| 独立completion receipt job／step 2 | `128760727323`、両方completed／SUCCESS |
| receipt実出力 | `exact_sha=0cdc195e04ca834089cf2fc4ef9070758965a586 source_result=success run=42489780978 attempt=1` |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| diagnostic artifact | `13621191704`、`lean-fast-check-log`、128283 bytes |
| archive SHA256（実取得bytesとGitHub metadata一致） | `ccc7f996186b5e1c17963c66b339f1132b0392ec5de7b0b831b73f06acc5277a` |
| 展開したlean-fast.log | 1901001 bytes |
| 展開ログSHA256 | `d1f5defe4eb6755f12488f07a9fad860819914fbcc5b38e7da4ac5190e340cef` |

[検証済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/52c14df9084213b1b36442c9bb618a019fdb7414/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCauchyCubicSmallCouplingV5_PZ37AIM.lean)。直接importはPZ37AIL、PZ37AHY、PZ37AIB、Mathlib.Tactic。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000` を保持した。baseからexact-sourceまでのcompareはahead 2／behind 0で、新規leaf以外の変更はない。

### 初回失敗と修正の来歴

初回source `b89233e605311d8417d118b1500f7814174eed05` の [CI #42489221057 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42489221057/attempts/1) はcompleted／FAILUREだった。実artifact `13620298568`（128842 bytes、SHA256 `817e84f51620ada88ba42e5221ee6cd8b066a9714afe179afd3d87ce65220436`）を取得して、元のCauchy証明内の2件のelaboration errorを確認した。

初回86行の連続写像省略記法 `fCont.continuous` を、元の連続写像名の明示的なprojectionに変更した。初回103行の積分分解では、線形項と差の可積分性を具体的な関数・係数で明示し、`integral_add`／`integral_sub` の引数推論を解消した。定理の型、定数、物理源・測度、既存仮定、環境、CI認証条件は変更していない。

失敗ログにはコンパイラのエラー回復による `sorryAx` 出力があり、失敗sourceを認証済みとは扱わない。上表は修正後sourceの新しいCIで確認した結果である。PRには初回失敗と修正内容を追記して保持した。

### 独立確認と証拠の範囲

別担当は、workflow・jobが完了した後の **3,310,604文字の実ジョブログ**を独立に取得し、11,401件のビルド、25件の標準公理のみの実出力、sorryAxなし、Lean errorなし、変更warning/errorなし、正確なcheckout SHAを確認した。receipt実ログと対象commit statusも独立に照合した。初回の部分ログを成功根拠に用いていない。

主担当は診断artifactの実bytesとGitHub metadataのSHA256を照合し、source／test-merge／実squashのGit treeとLean blobの一致を確認した。receiptは別CIジョブによるexact-source結果記録であり、別の証明カーネルを意味しない。変更ファイルのwarning 0は、再生された歴史的な依存ファイルの全warningが0という意味ではない。

数学的内容と既存の型付きAPIについて、個数・区間包含・固定結合の担当、真正Haar Cauchyの担当、実transfer三次誤差の担当が独立にレビューした。修正後の積分elaboration部分および本記録の数学部分も再レビューした。ソースレビューと機械的証明認証は区別する。

## 2．対象と既存の量

各 `H : ℕ` に対する元の有限空間格子を対象とする。`p_H` はAFZの元plaquette list長の実数値、`n_H` は元空間リンク型の `Nat.card`。[AIB] の正確な式は

\[
p_H=24(H+1)^3\ge24.
\]

元の符号付きZW物理L²源を `f_{0,H}`、[AHN] の真正源二次モーメントを `V_H`、AEVの真正Haar L1質量を `M_H` とする。AFZの既存連続代表を `f_H` と書くと、[AHN] の既証明代表橋を通じて

\[
M_H=\int |f_H(A)|\,d\mu_H(A),\qquad
V_H=\int f_H(A)^2\,d\mu_H(A)>0.
\]

ここで `mu_H` は元の正規化空間積Haar測度である。L²同値類の任意の点ごとの値を仮定しない。

## 3．元のHaar上のCauchy評価

新定理 `p4Q2PZ37AIM_originalSource_L1_sq_le_secondMoment` は

\[
\boxed{M_H^2\le V_H}
\]

を証明する。証明は元の連続代表の可積分性と、真正確率測度上の

\[
0\le\int (|f_H|-M_H)^2\,d\mu_H
=V_H-M_H^2
\]

の展開による。新たなHaar分解やplaquette独立性を仮定しない。

新定義 `p4Q2PZ37AIM_identityHaarRoot` を

\[
u_H=(1/384)^{n_H},\qquad 0<u_H\le1
\]

とする。[AIK] の既存床は厳密に

\[
v_H=\left(\frac{3p_H}{8}\right)^2u_H^4\le V_H
\]

と等しい。`q_H=(3p_H/8)u_H^2` と略記すれば `q_H^2=v_H` であり、`M_H^2<=V_H` と `(q_H-M_H)^2>=0` から

\[
\boxed{q_HM_H=\frac{3p_H}{8}u_H^2M_H\le V_H}
\]

を導く。`q_H` は説明上の略記であり、元の二次モーメントを置き換える定義ではない。

## 4．明示的な区間の厳密な拡張

新定義 `p4Q2PZ37AIM_elementaryCubicSmallCoupling` は

\[
\boxed{\theta_H=\frac{u_H}{16p_H+1}
=\frac{(1/384)^{n_H}}{16p_H+1}>0}.
\]

[AIL] の既存端点

\[
\tau_H=\frac{v_H}{16p_H^3+1}
\]

を変更せず、全Hで

\[
\boxed{0<\tau_H<\theta_H}
\]

を証明した。証明では `u_H^4<=u_H` と `p_H^2<=p_H^3` を使い、

\[
(3p_H/8)^2(16p_H+1)<16p_H^3+1
\]

を示して正の分母を比較する。新端点には未評価の源・L1・分配積分やHaar球定数は残らない。旧式のHaar因子の指数 `4*n_H` に対し、新式は `n_H` である。ただし有限体積依存は保つ。

## 5．元のtransferの三次誤差を制御

以後、**`0<beta<=theta_H`** を仮定する。分母の `+1` と `beta>0` により、上端を含め

\[
16\beta p_H<u_H\le1.
\]

[AHX] の既証明二次近似は、元の完全Wilson作用と両端halfweightを保持した

\[
Q_{H,\beta}(B)=-\beta V_H+
\frac{\beta^2}{2}(3p_H+W_H(B))V_H.
\]

元の空間Wilson作用の上界 `W_H(B)<=2p_H` から、AIMは全境界で

\[
\frac{\beta^2}{2}(3p_H+W_H(B))V_H
<\frac{5}{32}\beta V_H
\]

を証明する。

[AHY] の元の境界依存half cubic budgetを `E^{(3)}_{H,\beta}(B)` と書く。AHYと既存の正確な作用budget `C_H=4p_H` より

\[
E^{(3)}_{H,\beta}(B)
\le\frac{(\beta C_H)^3}{12}M_H
=\frac{16}{3}\beta^3p_H^3M_H.
\]

`(16 beta p_H)^2<=u_H^2` と上記 `q_H M_H<=V_H` を使い、

\[
\boxed{E^{(3)}_{H,\beta}(B)\le\frac1{18}\beta V_H}
\]

を得る。`5/32+1/18=61/288<1/4` であるため、[AHY] の実transfer包含 `T_beta f0(B)<=Q_beta(B)+E^{(3)}_beta(B)` から

\[
\boxed{\forall B,\quad
T_{H,\beta}f_{0,H}(B)<-\frac34\beta V_H
\le-\frac34\beta v_H<0}
\]

が従う。評価しているのは元のtransferであり、Taylor多項式の符号だけを結論にしていない。

## 6．同じ全余裕負領域のHaar質量1

[AIL] の既証明上界は、元のAIG余裕について

\[
\varepsilon_H(\beta)
=\frac{\beta}{2}Z_{\mathrm{cross},H}(\beta)
e^{-2\beta p_H}V_H
\le\frac12\beta V_H.
\]

AIMはその余裕と領域の定義を変更せず、

\[
\forall B,\quad T_{H,\beta}f_{0,H}(B)
<-\frac32\varepsilon_H(\beta)
<-\varepsilon_H(\beta)
\]

を導く。従って同じ元の全余裕負領域

\[
\mathcal N_{H,\beta}
=\{B\mid T_{H,\beta}f_{0,H}(B)<-\varepsilon_H(\beta)\}
\]

について

\[
\boxed{\mathcal N_{H,\beta}=\mathrm{univ},\qquad
\mu_H(\mathcal N_{H,\beta})=
\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})=1}
\]

を証明した。AHNに既に定義された元の恒等配置も、この拡張区間全体で三半余裕を満たす指定負境界である。同じ区間では

\[
\{B\mid 0\le T_{H,\beta}f_{0,H}(B)\}=\varnothing.
\]

端点証明は `beta=theta_H` 自体での全境界負性と元のHaar質量1を明示する。

## 7．元の固定結合との関係と残る障害

元の固定結合は[ADC] の

\[
\beta_0=\frac{\log(3/2)}{64}.
\]

[AIB] の既証明有理下界 `1/192<=beta0` と、実個数 `p_H>=24` を使って

\[
\boxed{\tau_H<\theta_H\le\frac1{385}
<\frac1{192}\le\beta_0}
\]

を全Hで形式証明した。これにより、旧AIL区間および新AIM区間のどちらも固定 `beta0` を含まないことが確定した。**これは証明済み区間からの除外であり、`beta0` で負境界が存在しない、あるいはtransferが非負になるという意味ではない。**

[AIK] の任意正結合に対する正のHaar質量下界は保持される。この既存結果は正の固定結合 `beta0` にも適用でき、その負領域の存在は既に保証される。今回拡張した全空間負性と具体的恒等負境界は `0<beta<=theta_H` の範囲である。元の固定結合での評価済み負中心、指定境界での符号判定、全境界負性、任意正結合での評価済み負中心、区間外の正境界・正負両符号領域、Hに一様な正結合区間、一様coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは導かない。

高次剰余だけから固定結合の主張を昇格させない。特に既存[AIB] の粗いquartic budgetの障害は、実transferの符号についての不可能性とは異なる。今回も元の全作用、両端halfweight、符号付き物理源、真正Haar、既存仮定・定理を保持する。

## 8．公開宣言の監査

すべて `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` に属する。共通prefixは `p4Q2PZ37AIM_`。23定理と2定義の全25件に、公理出力命令と実ログの出力が一対一で対応する。

| 宣言末尾 | 種別 |
| --- | --- |
| `originalSource_L1_sq_le_secondMoment` | 定理 |
| `identityHaarRoot` | 定義 |
| `identityHaarRoot_pos` | 定理 |
| `identityHaarRoot_le_one` | 定理 |
| `elementaryVariance_eq_root` | 定理 |
| `originalSource_rootScaledMass_le_variance` | 定理 |
| `elementaryCubicSmallCoupling` | 定義 |
| `elementaryCubicSmallCoupling_pos` | 定理 |
| `plaquetteCount_ge_twentyFour` | 定理 |
| `oldSmallCoupling_lt_cubic` | 定理 |
| `elementaryCubicSmallCoupling_le_oneDiv385` | 定理 |
| `elementaryCubicSmallCoupling_lt_fixedCoupling` | 定理 |
| `scaledCoupling_lt_root` | 定理 |
| `originalQuadraticCorrection_lt_fiveThirtySeconds` | 定理 |
| `originalHalfCubicBudget_le_eighteenthVariance` | 定理 |
| `originalTransfer_lt_negThreeQuarterVariance` | 定理 |
| `originalTransfer_lt_negThreeQuarterElementary` | 定理 |
| `originalTransfer_below_threeHalfMargin` | 定理 |
| `originalFullNegativeRegion_eq_univ` | 定理 |
| `originalFullNegativeRegion_measure_one` | 定理 |
| `originalFullNegativeRegion_realMeasure_one` | 定理 |
| `originalIdentityTransfer_below_threeHalfMargin` | 定理 |
| `originalTransfer_negative` | 定理 |
| `originalNonnegativeRegion_eq_empty` | 定理 |
| `explicitEndpoint_certificate` | 定理 |

## 9．公開記録の扱い

本記録は定理のexact-source成功と実squashのtree・blob一致を確認した後、新規docs-only PRで追加する。mainへの文書ミラーには同じ記録Git blobを使う。既存README・ROADMAP・証明記録を上書きせず、文書専用PRではStrict Leanを手動dispatchしない。既存の自動workflowの設定は変更しない。

[AIL]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f19c83c3d1a93995f37114062d478fa3deb8ab4f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExplicitSmallCouplingFullNegativeRegionV5_PZ37AIL.lean
[AIK]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f19c83c3d1a93995f37114062d478fa3deb8ab4f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalElementaryNegativeHaarFloorV5_PZ37AIK.lean
[AHN]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f19c83c3d1a93995f37114062d478fa3deb8ab4f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentitySourceHaarMomentV5_PZ37AHN.lean
[AHX]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f19c83c3d1a93995f37114062d478fa3deb8ab4f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSecondOrderTaylorTransferV5_PZ37AHX.lean
[AHY]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f19c83c3d1a93995f37114062d478fa3deb8ab4f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWeightedCubicRemainderV5_PZ37AHY.lean
[AIB]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f19c83c3d1a93995f37114062d478fa3deb8ab4f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuarticBudgetObstructionV5_PZ37AIB.lean
[ADC]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f19c83c3d1a93995f37114062d478fa3deb8ab4f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingCertificateV5_PZ37ADC.lean

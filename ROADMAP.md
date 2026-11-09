## AHE（2026-11-07 JST）— 真正Haar signed min/max表の中心・誤差分解と有理Bool符号認証

**CLOSED:** [AHE定理PR #6430](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6430) MERGED。真正AGP/AGIの質量端点 `l_i≤u_i` を固定したまま、各signed係数 `a_i` に対して `min(a_i*l_i,a_i*u_i)=a_i*(l_i+u_i)/2-|a_i|*(u_i-l_i)/2`、`max(...)=a_i*(l_i+u_i)/2+|a_i|*(u_i-l_i)/2` をℚで厳密証明し、元表の上下端を真正有限有理 `signedMoment±massError` に展開。質量error非負、各Boolean判定と元AGP下端正・上端負の同値、真正Haar体積の同じ元物理transferへの符号健全性、元24中心格子への特殊化、任意精度AGU格子のAHD非零符号条件付き完全性をLean4で証明。**特定H／Bでchecker=trueを与える厳密数値証人は未構成。** 古典選択格子を数値計算完了と主張しない。

**VERIFIED:** [exact-source CI #42321226504](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42321226504)、**11,366/11,366 SUCCESS**、新規16定理は標準3公理のみ、sorryAxなし、変更Lean warning/error 0/0、workflow/job/Lean step/独立completion receipt completed/SUCCESS、source/test-merge/squash共通Git tree `0c978fd763c57fe7c91d9a995732a3d1ee43732b`。新規Lean1件・386行、既存Lean・元物理・root・Lean/mathlib pin・workflow変更なし。

**NEXT — AHF:** 実際の元Wilson作用、centered source、固定H・真正Haarセル質量・有理右境界の明示的有限数値表を構成し、`AGP originalTable.lower>0` または `upper<0` の実証人を探索する。正／負の存在はまだ証明されておらず、two-sign shell、H一様coercivity、Hamiltonian gap、連続体mass gap、非有理境界拡張はOPEN。

[AHE正式証明記録](docs/proofs/P4-Q2-PZ37AHE_verified_20261107.md)。唯一の定理正本 `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラー。以下AHD以前の履歴を全文保持。

---

## AHD（2026-11-07 JST）— 元signed-transfer非零符号の必要十分な真正Haar表証明書

**CLOSED:** [AHD定理PR #6427](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6427) MERGED。AHC元signed-transfer任意精度区間とAFV実値包含から、`t_H(B)>0 iff ∃元AGU区間lower>0`、`t_H(B)<0 iff ∃元AGU区間upper<0` をLean4で形式証明（固定H・元AGL有理座標右境界）。元AGN global対称 `[-M,M]` が非零符号を独力で与えないことを用い、各真正AGU区間の正下端／負上端条件が**同じ元AGP signed-Haar有理表**の正下端／負上端条件と同値と示した。`t_H(B)≠0 iff ∃元AGP有理符号表`、`t_H(B)=0 iff 全真正区間が0をまたぐ iff 正・負表証明書が存在しない` を検証した。`width→0` だけでは `t_H(B)≠0` を導けないことを幅0の例でも証明。元物理transfer、centered source、kernel、global floor、Haar mass、AGU古典選択grid、signed min/max不変更。**具体的な非零符号証人は未証明。**

**VERIFIED:** [exact-source CI #42318237854](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42318237854)、**11,365/11,365 SUCCESS**、新規14定理の標準3公理依存のみ、sorryAxなし、変更Lean warning/error 0/0、workflow/job/Lean step/独立receipt completed/SUCCESS、source/test-merge/squash Git tree一致 `c7a7f3c76072b0549fd3571948338ec07eaeee5d`。新規Lean1件388行・削除0、元root/pins/workflow不変更。

**NEXT — AHE:** ひとつの固定H・真正有理右境界に対して、実際の元AGPの `originalTable.lower>0` または `originalTable.upper<0` を成立させる具体的な有理数・元Haar質量・中心化source証明書を探索し、古典選択格子の実用的評価へ降ろす。非有理境界拡張、two-threshold shell、H一様coercivity、Hamiltonian gap、連続体4D質量ギャップはOPEN。結果の論理的同値は非零値の証拠を作ったことではない。

[正式証明記録](docs/proofs/P4-Q2-PZ37AHD_verified_20261107.md)。定理正本 `formal/real-hilbert-uniform-coercive-strong-limit`／main文書ミラー。以下AHC以前の全履歴保持。

---

## AHC（2026-11-07 JST）— 元signed-transfer区間幅の固定H任意精度

**CLOSED:** [AHC定理PR #6424](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6424) MERGED。AGYの真正signed-transfer幅誤差 `width(I_H)≤(p_H/2)*(DeltaKmax+DeltaF/2)+2L_H(m)R+2M_H(m,n)eps` を一切弱めず、元AGV `L_H(m)≤Lcap_H=6+13p_H/2` と元AGN `M_H(m,n)≤Mcap_H=p_H/4` を次数非依存にLean4で証明した。`C_H=p_H+2Lcap_H+2Mcap_H+1>0`、`q=eta/(4C_H)>0` を構成し、元AGU Borel grid・Haar質量誤差を `R=eps=q` として選択。AHBの固定体積全中心一様kernel/floor幅の任意精度から共通 `m,n` を選択、真正元signed-transfer verified intervalに `width(I_H)≤(C_H−1)q≤eta/4<eta` を形式証明。元kernel/floor/source/measure/signed min/max/root/pinsを維持。固定HかつAGL有理座標の右境界に対する狭区間であり、実transfer非零符号は依然未証明。

**VERIFIED:** [Exact-source CI #42316089429](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42316089429)、**11,364/11,364 SUCCESS**、新規11宣言の公理依存は標準3公理のみ、sorryAxなし、変更Lean warning/error0/0、workflow/job/Lean step/独立completion receipt completed/SUCCESS。source/test-merge/squash共通Git tree `9da2c909a00d06d6876dc11229b30c376fcff777`。新規Lean1件・既存Lean不変更・削除0。Lean/mathlib pinと物理定義、公開root、workflow不変更。

**NEXT — AHD:** 真正元signed-transferを任意に狭い区間へ囲めることと、その値が0ではないことを区別する。真正区間の正下端／負上端を示す有限有理認証、原Haar質量と作用量、元符号付き中心化sourceに基づく構成的な符号証人を検討する。非有理境界への一般化、two-threshold shell、H一様coercivity、Hamiltonian gap、連続体4D質量ギャップ、大体積Haar表は引き続きOPEN。

[AHC正式証明記録](docs/proofs/P4-Q2-PZ37AHC_verified_20261107.md)。唯一のLean定理正本 `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。以下AHB以前の履歴全文保持。

---

## AHB（2026-11-07 JST）— 元kernel/floorの固定体積一様任意精度

**CLOSED:** [AHB定理PR #6421](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6421) MERGED。既証明元Wilson one-slab作用上界 `0≤S≤V_H` とAGK結合端点 `0≤betaLower≤betaUpper≤1` を継承し、元AGM `autoScale≤K_H=ceil(V_H)+1` を全中心・全次数に証明。元AGJ clipped指数下端 `0≤b≤1`、階乗 `E_n=(n+1)/(n!*n)≤2/n`、幾何尾 `t_m=(5/768)*(1/25)^m` を合成し、`B(S,m,n)≤K_H*2^K_H*(V_H*t_m+4E_n)`（同誤差≤1）を形式証明。全有理元作用量 `0≤S≤V_H` の出力幅に任意精度を与える同じ `m,n` を構成。元AGZ/AHAの真正物理区間への降下により、任意固定H・任意正有理etaに対し、元AGU真正grid・元有理右境界の**全体に共通**の `m,n>0` で `DeltaKmax<eta, DeltaF<eta` をLean4で証明。元Haar・kernel・floor・source・transfer不変更。

**VERIFIED:** [exact-source CI #42313988679](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42313988679)、**11,363/11,363 SUCCESS**、新規14宣言標準3公理のみ・sorryAxなし・変更Lean warning/error 0/0、workflow/job/Lean step/独立receipt completed/SUCCESS、source/test-merge/squash Git tree一致 `89d9e7c8dd21726a7c44d1dd0e30bcfd4b2d1d71`。新規Lean1件502行、削除0。既存physics・root・pinned Lean/mathlib・workflow不変更。

**NEXT — AHC:** AGYの元signed-transfer幅誤差の残項 `2L_H(m)R+2M_H(m,n)eps` を固定Hで一様に上から制御し、`R,eps,m,n` を同時選択する。AHBは kernel/floor幅の任意精度を確立したが、元signed-transferの非零符号、two-threshold shell、H一様coercivity、Hamiltonian gap、連続体4D gapは引き続きOPEN。大体積Haar数値表も未評価。

[AHB正式証明記録](docs/proofs/P4-Q2-PZ37AHB_verified_20261107.md)。唯一の定理正本 `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラー。以下AHA以前の履歴全文保持。

---

## AHA（2026-11-07 JST）— AGK結合・AGJ階乗剰余の真正指数出力幅上界

**CLOSED:** [AHA定理PR #6418](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6418) MERGED。元AGJ `TaylorError(q,n)≤E_n=(n+1)/(n!*n)`（`n>0, |q|≤1`）、元非負Wilson作用からの非正指数の1-Lipschitz、ゼロclip付きTaylor底と整数乗の幅をLean4で証明。AGK `t_m=(5/768)*(1/25)^m`、AGMの実際のautoScale `k`、真正Taylor下端 `b` を用い `AGJ_expUpper-AGJ_expLower ≤ (b+S*t_m/k+4E_n)^k-b^k=:B(S,m,n)` とした。元AGM真正kernel・AGN global floorのraw幅≤`B` を証明し、AGU同じ真正格子の全中心最大 `Bmax` とAGZ signed-transfer評価から `width(I_H)≤(p_H/2)*(Bmax+Bfloor/2)+2L_H(m)R+2M_H(m,n)eps` を形式化。元source・Haar・kernel・floor・transfer・root/pins不変更。

**VERIFIED:** [Exact-source CI #42310738307](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42310738307)、**11,362/11,362 SUCCESS**、新規12定理は標準3公理のみ、sorryAxなし、変更Lean warning/error0/0、workflow/job/Lean step/独立receipt completed/SUCCESS、source/test-merge/squash共通Git tree `61663613839f72b5251105bdbf6355e82544ca91`。新規Lean1件・削除0、既存の物理モデル・root・pins・workflow不変更。

**NEXT — AHB:** `t_m→0` に加え、階乗tail `E_n→0`、実際の元作用量 `S` の上界、AGM自動scale `k` の一様上界、`b≤1` をLean4で結合して、固定Hにおける真正出力幅の任意精度制御へ進む。AHA自体は `B(S,m,n)→0`・kernel/floor一様精度を証明しない。真の非零transfer符号、two-threshold shell、H一様coercivity、Hamiltonian gap、連続体gap、大体積Haar表はOPEN。

[正式証明記録](docs/proofs/P4-Q2-PZ37AHA_verified_20261107.md)。唯一のLean正本 `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。以下AGZ以前の履歴全文保持。

---

## AGZ（2026-11-07 JST）— 元AGK結合・AGJ指数Taylor幅の真正kernel/floorへの降下

**CLOSED:** [定理PR #6415](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6415) MERGED。元AGL真正有理作用・元AGN global floor combinatorial actionについて、AGK固定結合区間から指数入力幅 `0≤qHi-qLo=S*(betaUpper-betaLower)≤S*(5/768)*(1/25)^m` を証明。元AGM真正kernel [0,1] clip／元AGN floor [0,1] clipにより各実幅≤AGK/AGJ raw Taylor有理幅、同一AGU格子の有限最大値についても同様。元signed transfer幅 `width(I_H)≤(p_H/2)*(DeltaK_rawTaylorMax+DeltaF_rawTaylor/2)+2L_H(m)R+2M_H(m,n)eps` を証明。etaK,etaF の有限有理チェック証明を受け取る条件付き最終上界も形式化。物理model・source・Haar・signed min/maxを一切変更しない。

**VERIFIED:** [Exact-source CI #42304072471](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42304072471)、**11,361/11,361 SUCCESS**、新規11宣言は標準3公理のみ、sorryAxなし、変更warning/error0/0、workflow/job/Lean step/独立receipt completed/SUCCESS。source/test-merge/squash Git tree一致 `a8a5c7c2c75e1bd147840ab2ec2e3f31e4ee5df8`。新規Lean1件304行・削除0、root・pin・workflow不変更。

**NEXT — AHA:** AGJ出力Taylor区間幅の定量・一様収束を実際の自動scaleに対して証明し、既証明AGK入力幅収束と統合する。現在は `DeltaK_rawTaylorMax→0`・`DeltaF_rawTaylor→0` 未証明。元transfer非零符号、two-threshold shell、H一様coercivity、Hamiltonian gap、連続体gap、大体積数値Haar表もOPEN。

[正式証明記録](docs/proofs/P4-Q2-PZ37AGZ_verified_20261107.md)。唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。以下のAGY以前の履歴全文保持。

---

## AGY（2026-11-07 JST）— 元center幅を真正kernel最大幅とglobal floor幅へ分解

**CLOSED:** [定理PR #6412](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6412) MERGED。元AGUと同じBorel格子の真正AGM clipped Wilson kernel幅の有限最大 `DeltaKmax`、元AGN global floor幅 `DeltaF` を定義。元AGN中心化sourceの厳密有理値に `|s_H(C)|≤p_H/2` を適用し、AGXの `etaMax≤(p_H/2)*(DeltaKmax+DeltaF/2)`、更に元AGU最終signed-transfer区間の `width(I_H)≤(p_H/2)*(DeltaKmax+DeltaF/2)+2L_H(m)R+2M_H(m,n)eps` を証明。物理model・Haar・signed min/maxを不変更。

**VERIFIED:** [exact-source CI #42300462050](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42300462050)、11,360/11,360 SUCCESS、9公理出力は標準3公理のみ、sorryAxなし、変更warning/error0/0、workflow/job/step/receipt completed/SUCCESS、source/test-merge/squash Git tree一致。新規Lean219行・削除0、root・pins・workflow不変更。

**NEXT — AGZ:** AGK真正結合幅、AGJ Taylor残差を元AGM kernel幅・AGN floor幅へ直接証明付きで接続し、有限中心すべてに対する誤差収束を検討する。DeltaKmax→0／DeltaF→0、真のtransfer非零符号、二閾値殻、H一様coercivity、Hamiltonian gap、連続体gap、具体的大体積数値計算はいずれもOPEN。

[正式証明記録](docs/proofs/P4-Q2-PZ37AGY_verified_20261107.md)。唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラー、旧履歴全文保持。

---

## AGX（2026-11-07 JST）— 真正有限中心幅最大値による外部eta条件の解消

**CLOSED:** [定理PR #6409](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6409) MERGED。元AGUの空でない真正Borel partitionから `Finset.sup'` による実中心幅の有限最大値 `etaMax` を構成。元AGN各中心幅≤etaMaxとetaMax≥0を証明し、元AGVのsigned min/max／Haar質量／AGP評価／tighten-only交差に**外部eta仮定なし**で接続した：`width(I_H)≤etaMax+2L_H(m)R+2M_H(m,n)eps`。同じ選択格子と右境界・source・kernel・floorを保持。

**VERIFIED:** [exact-source CI #42297186825](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42297186825)、11,359/11,359 SUCCESS、新規6宣言は標準3公理のみ、sorryAxなし、変更warning/error0/0、workflow/job/Lean step/receipt completed/SUCCESS、source/test-merge/squash Git tree一致。新規Lean146追加行・削除0。

**NEXT — AGY:** AGWの厳密因子分解を使い、全中心で元kernel幅と元floor幅の有限最大上界を構築し、さらにAGK結合精度・AGJ Taylor誤差と接続する。古典選択格子の具体的数値表、etaMax→0、実signed-transfer非零符号、二閾値殻、H一様coercivity、Hamiltonian gap、連続体gapはOPEN。

[正式証明記録](docs/proofs/P4-Q2-PZ37AGX_verified_20261107.md)。正本 `formal/real-hilbert-uniform-coercive-strong-limit`、main文書ミラー、既存本文全文保持。

---

## AGW（2026-11-07 JST）— 元中心値区間のkernel／floor幅への厳密分解

**CLOSED:** [PR #6406](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6406) MERGED。真正AGNの元source有理値sと元AGM clipped kernel[klo,khi]・元AGN floor[flo,fhi]から、`centerWidth=|s|*((khi-klo)+(fhi-flo)/2)` をmin/max符号処理付きでLean4形式証明。元center intervalの非負幅も証明。物理式・Haar法則・元kernel等を変更しない。

**VERIFIED:** [CI #42274305910](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42274305910)、11,358/11,358 SUCCESS、4宣言標準公理のみ、sorryAxなし、変更warning/error0/0、workflow/job/step/receipt SUCCESS、source/test-merge/squash Git tree一致。新規Lean150追加行のみ。

**NEXT/OPEN:** AGM／AGJ／AGKの元kernel誤差とAGN floor幅の上界・一様精度を証明し、AGVの全中心eta条件を解消する。中心幅恒等式単体は任意精度収束を意味しない。非零transfer符号、二閾値殻、H一様coercivity、Hamiltonian gap、連続体mass gap、具体的大体積計算は引き続き未証明。

[AGW正式記録](docs/proofs/P4-Q2-PZ37AGW_verified_20261107.md)。定理正本 formal/real-hilbert-uniform-coercive-strong-limit、mainは文書ミラー、従来履歴保持。

---

## AGV（2026-11-07 JST）— 真正Haarによる元signed-transfer区間幅

**CLOSED:** [PR #6403](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6403) MERGED。各セルのAGN中心値区間幅≤etaの条件の下、AGP/AGIの符号付きmin/max、実際のHaar質量の非負性と正規化、AGUの同一選択格子の半径≤R・質量総幅≤epsにより、`width(I_H)≤eta+2L_H(m)R+2M_H(m,n)eps` をLean4で証明。負の有理Haar下端を許容し、有理端点の和を1と仮定しない。元のtransfer・Borel格子・source/kernelは不変更。

**VERIFIED:** [exact-source CI #42271966524](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42271966524)、11,357/11,357 SUCCESS、10公理監査は標準公理のみ、sorryAxなし、変更warning/error0/0、workflow/job/Lean step/receipt SUCCESS、source/test-merge/squash Git tree一致。新規Lean1件450行のみ、削除0。

**NEXT — AGW:** etaは条件として残る。AGKの固定結合区間幅の収束と、AGJ Taylor・AGM kernel・AGN floorの誤差を元定義で統合して中心値幅の任意精度保証へ進む。最終幅の無条件任意精度化、具体的大体積表、真正非零符号、二閾値殻、H一様coercivity、Hamiltonian gap、連続体mass gapは未解決。

[AGV正式証明記録](docs/proofs/P4-Q2-PZ37AGV_verified_20261107.md)。唯一の定理正本 formal/real-hilbert-uniform-coercive-strong-limit、main文書ミラー、既存本文を全文保持。

---

## AGU（2026-11-06 JST）— 要求精度を保持した元Haar格子とsigned-transfer接続

**CLOSED:** [定理PR #6400](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6400) MERGED。旧AGTの裸の `Nonempty (AGP_gridData H)` に由来する予算非依存性を形式証明し、元AGPデータと半径・セル認証半径・真のHaar質量総幅を持つ添字付きTypeを追加した。任意正有理R,epsで存在し、そのTypeから選んだ実データに `grid.radius≤R`、`cellCertificateRadius_i=R`、`Σ(upper_i-lower_i)≤eps` が成立する。

**同じ元データへの接続:** AGUのtransfer区間は上記の選択データを元AGP評価器へそのまま渡す。既存区間・元大域区間との交差のtighten-only性を証明。明示的構成子は供給格子とAGQ質量オブジェクトを厳密保存するが、古典選択したpackageがその構成履歴そのものを返すとは主張しない。

**VERIFIED:** [CI #42210989555](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42210989555)、11356/11356 SUCCESS、14宣言は標準公理のみ、sorryAxなし、変更warning/error0/0、workflow・Lean job/step・receipt completed/SUCCESS、source/test-merge/squash Git tree一致。新規1ファイル225追加行、既存Lean・物理定義・root・pin・workflow不変更。

**NEXT/OPEN:** 同じ選択格子について、セル幾何変動、中心の有理核区間幅、有限セル数を含めた質量誤差を統合する最終signed区間幅評価を進める。最終幅の任意精度化には各項の制御が必要であり、R・epsの存在だけから結論しない。具体的大体積計算、非零transfer符号、二閾値殻、H一様coercivity、Hamiltonian gap、連続体4D質量ギャップは未証明。

[正式証明記録](docs/proofs/P4-Q2-PZ37AGU_verified_20261106.md)。唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。以下の履歴を全て保持し、AGS・AGT追補で次段としていた「要求精度の型付き保存」は今回完了した。

---

## AGS・AGT（2026-11-06 JST）— 有理稠密性・有限被覆・真正空間格子と次の精度保持

**CLOSED:** [AGS #6396](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6396)・[AGT #6397](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6397) MERGED。AGRで外部入力だった真正有理中心の有限被覆は、実チャート逆写像、有理Pi稠密性、対蹠チャート、元SU(2)等距離、コンパクト性から任意正半径について存在証明された。AGTの `exists_fineOriginalRationalSpatialGrid` は任意の正の有理Rに対し、全元リンクの有理座標証拠と `grid.radius≤R` を持つ真正AGH Borel格子を存在量化する。

**型の境界:** AGQの格子後置質量予算はセル数Nを保持して総幅 `≤eps` を証明する。一方、AGTの後段存在定理は `Nonempty (AGP_gridData H)` にR・epsの制約を残しておらず、そこから選択したデータには指定予算の射影定理がない。元signed-transferの `verifiedInterval` 包含保証は有効だが、選択データが指定R・epsを満たす、または最終区間幅がR・epsとともに消えるとは主張しない。

**NEXT — AGU:** 同じ元AGPデータを保持する `precisionGridData H R eps` のような添字付きTypeに、格子半径 `≤R`、各セル認証半径、真のHaar質量区間総幅 `≤eps` の証拠を格納する。AGTの正しい格子存在定理からこの強いTypeの存在を証明し、そのTypeで選択する。元の有理座標・Borelセル・真の測度・signed-transferとの関係を保持したまま、選択後も要求予算を射影できるようにする。既存AGTは変更しない。

**VERIFIED:** AGS [CI #42196369171](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42196369171) は11,354/11,354・新規10宣言、AGT [CI #42208149754](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42208149754) は11,355/11,355・新規5宣言。両者ともworkflow・Changed Lean job・Lean step・receipt completed/SUCCESS、標準公理のみ、sorryAxなし、変更Lean warning/error 0/0、source/test-merge/squash Git tree一致。別workflowのStrict LeanやGovernanceの結果には読み替えない。

**OPEN:** 最終signed区間幅の収束評価、具体的な大体積数値表、元transfer非零符号、二閾値殻、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップ。固定24中心のAGO障害はその手法の定理として保持され、新たな細分可能性と混同しない。

唯一の定理正本 `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラー。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、元物理定義・root・workflow不変更。[AGS正式記録](docs/proofs/P4-Q2-PZ37AGS_verified_20261106.md) · [AGT正式記録](docs/proofs/P4-Q2-PZ37AGT_verified_20261106.md)。AGR以前の全文を保持する。

---

## AGR（2026-11-06）— 真正有理ステレオ中心と細分gridの条件付きdescent

[定理PR #6393](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6393) MERGED、[CI #42190751075](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42190751075) **11,353/11,353 SUCCESS**。新規7宣言は標準公理のみ、sorryAxなし、changed warning/error 0/0、source/test-merge/squash Git tree同一。

**CLOSED**：有理3変数の逆ステレオ投影による真正`S³`・元SU(2)中心の厳密構成とAGL有理座標証明、元Wilson作用幅0包囲。真正元SU(2)の有限被覆証拠を入力すると、AGH全リンク格子→AGQの真Haar総質量幅`≤eps`→AGPの元signed-transfer区間を既存のまま連結するLean4定理を構成した。

**NEXT/OPEN**：単一ステレオチャートの除外極を別扱いし、`Rat.denseRange_cast`＋有限Pi稠密性＋連続逆投影＋ADS/ADT等距離の正確な形式化から**任意点・任意半径の有理近似**を証明。次にSU(2)コンパクト性から有限有理被覆を抽出し`hCover`前提を解消する。数値的な具体Haarセル質量表、非零signed transfer符号、H一様coercivity、Hamiltonian gap、連続体質量ギャップは独立の未解決条件。

唯一の定理正本 `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。Lean/mathlib pin、既存定義・root・workflow変更なし。正式記録 `docs/proofs/P4-Q2-PZ37AGR_verified_20261106.md`。AGQ以前の内容を全バイト保持。

---

## AGQ（2026-11-06）— 真正Haarセルの総質量誤差幅

[定理PR #6390](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6390) MERGED、[CI #42178646756](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42178646756)：11,352/11,352 SUCCESS、9宣言は標準公理のみ、sorryAxなし、warning/error 0/0、独立receipt SUCCESS、Git tree一致。

**CLOSED**：任意の元AGH真正Borel格子Nセルと正の有理許容epsについて、真のセルHaar質量を含む有理区間の総幅 `<=eps` をLeanで構成。精度選択は格子生成後の `eps/[2(N+1)]`。中心有理座標と半径の証拠がある格子なら、質量intervalを新規oracleなしでAGPの元signed-transferへ接続。

**OPEN**：有理SU(2)細分中心の密度・被覆の形式化、非計算的選択の計算実装、具体的符号認証。既存Wilson・Haar・transfer・root・Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 不変更。正式記録 `docs/proofs/P4-Q2-PZ37AGQ_verified_20261106.md`。mainは文書ミラー。旧本文保持。

---

## AGP（2026-11-06）— セル別真正Haar評価と次段AGQ

**MERGED:** [定理PR #6387](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6387)。exact-source CI #42175738816：11,351/11,351 SUCCESS、17標準公理監査・sorryAxなし、変更Lean warning/error 0/0、独立receipt SUCCESS、source/test-merge/squash Git tree一致。

**CLOSED:** 元連続signed integrandの中心依存係数 `6(1-k_H)+13 beta0 |f_H(C)|`、AGNによる源振幅 `p_H/2` の一様包囲、セル別真正有理半径・中心値・真のHaar質量を使うAGI min/max積分評価、元transferの既存区間とのtighten-only交差。旧AGI/AGOの定理を変更していない。

**OPEN:** AGQでは、細かい有理SU(2)中心を持つ真正Borel有限被覆、セル別半径、有理質量包囲をAGPへ接続する。非計算的有限ネットの存在と機械的に実行済みの大体積表は区別する。物理的符号・二閾値殻・H一様coercivity・Hamiltonian gap・連続体質量ギャップは未証明。唯一のLean正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持する。

---

## P4-Q2-PZ37AGO（2026-11-06 JST）— 真正24中心signed-transfer証明書の飽和障害

[定理PR #6384](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6384) MERGED。唯一のLean正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

**CLOSED（Lean形式証明）**：元空間リンク数＝元plaquette数 `p_H`、元24中心幾何誤差 `gamma_H >= (24/5)*p_H >= 2*R_H`（任意H,m,n>0）、真正Haar質量の上端総和≥1、AGI signed `min/max` raw包囲が `[-R_H,R_H]` を包含。従って、元のfixed-24証明書とAGNの改善された大域区間の交差は**ちょうど `[-R_H,R_H]`**。任意の元有理境界・許容m,nについて、この手法での正負符号判定は不可能。物理transferがゼロとは言っていない。

**VERIFIED**：[CI #42169865632](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42169865632) 11,350/11,350 SUCCESS、12公理依存は標準公理のみ、sorryAxなし、変更Lean warning/error 0/0、receipt SUCCESS、source/test-merge/squash Git tree一致。前CIの有限型cardinalityのsimp循環を列挙補題の`simp only`へ修正。変更は新規Lean葉1件・377追加行のみ、既存Lean・物理定義・workflow・root不変更。

**NEXT（OPEN）**：真正Haar細分による幾何半径の改善、個々の真正セル質量の有理認証、center値と全積分の誤差制御を同時に進める。m,nだけの精密化では幾何障害が残る。非零符号、二閾値殻、H一様coercivity、Hamiltonian gap、連続体4D質量ギャップは未証明。

正式記録：`docs/proofs/P4-Q2-PZ37AGO_verified_20261106.md`。以下のAGN以前の履歴本文は全バイト保持する。

---

## 検証済み定理 — AGN／元Wilson Haar平均の厳密計算とsigned transfer自動証明書（2026-11-06 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。[AGN定理PR #6381](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6381) はMERGED。AGN定理squashは `c648bd88566d1e5bf06324ada997ab37918cb12c`。 元SU(2)・Wilson作用・核・固定結合・source・Haar/Perron/transfer/FF・Lean公開集約root・Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。

### CLOSED — 中心化で差し引く元Wilson作用の平均を厳密化

元の空間plaquetteの4本のリンクが全H（H=0を含む）で異なることを証明し、元product Haarの4リンク制限、既証明cyclic Haar word、元Wilsonエネルギーの共役不変性から各plaquetteの平均を1と導いた。積分の線形性で **`m_H=integral W_H dmu_H=p_H`** が成立する。p_Hは元plaquette listの長さである。異なるplaquette間の独立性を仮定していない。元中心化源 `f_c=(W_H-p_H)/2` の平均は0であり、その連続代表の点wise上界をp_Hから **p_H/2** へ改善した。

AGLの厳密有理作用値から、任意の元有理座標配置で中心化源の幅0の有理区間を構成。未知の中心化定数の近似入力を除いた。

### CLOSED — 真正Haar質量・元指数核からAGI全証明欄を構成

既存AFQ/AGDの24中心product cellsを、実際の中心と半径 `(4/5)*L` を持つAGH格子に接続。真正Haar質量の区間 `[(1/160000)^L,(625/1781)^L]`、真正質量総和1、符号付きセル積分の一般包含を構成した。独立した元Wilson平均の有限区間も保持する。

AGK・AGJ・AGMから元global floorの自動有理区間を構成。厳密な元中心化源、AGMの核区間、floor midpoint、元AGG幾何誤差、真正質量端点を接続して、任意の元有理座標境界のAGI signed tableを証明した。特に真正24中心境界では、追加の数値入力は結合次数m、Taylor次数n、n>0のみ。

厳密平均と元kernel midpoint boundにより **`|t_H(B)| <= p_H*(1-ell)/4 <= p_H/4`** を証明した。ellは元floorの認証有理下端である。従来のp_H/2を少なくとも半分に改善し、AGI有限和の区間と交差して同じ元transferの情報を保持する。

### exact-source検証

[CI #42164476429](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42164476429) はworkflow・Lean job `127717599152`・Lean step17・独立receipt `127719202262` がすべてcompleted / SUCCESS。**11,349 jobs・43宣言（14+12+17）・標準公理のみ・sorryAxなし・変更warning/error 0/0**。新規Lean3ファイル・1,013行追加のみ。

検証済みsource `7ab237c1bfb08c85d6ff9031b208b575b23b30b5`、実checkout test-merge `5f902a43cb2e046d3164779fe87fc2c8b51f1bbd`、定理squash `c648bd88566d1e5bf06324ada997ab37918cb12c` のGit treeはすべて `c6d6dc1d045edb21a42a52a0b8682836dfb6176e`。

[AGN正式記録](docs/proofs/P4-Q2-PZ37AGN_verified_20261106.md) · [厳密平均](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c648bd88566d1e5bf06324ada997ab37918cb12c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExactWilsonHaarMeanV5_PZ37AGN.lean) · [真正質量・平均包囲](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c648bd88566d1e5bf06324ada997ab37918cb12c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHaarMeanEnclosureV5_PZ37AGN.lean) · [自動signed証明書](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c648bd88566d1e5bf06324ada997ab37918cb12c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAutomaticSignedSpatialCertificateV5_PZ37AGN.lean)

### AGK・AGL・AGMの記録追補

[AGK #6376](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6376)・[AGL #6377](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6377)・[AGM #6380](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6380) はMERGED。元結合の任意精度包囲、元行列規約に従う厳密有理作用、整数尺度自動選択を経て、真正24中心核の有理区間を構成した。AGM [CI #42158675778](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42158675778) は11,346 jobs・9宣言・標準公理のみ・sorryAxなし・変更warning/error 0/0・receipt SUCCESS。source/test-merge/squashは共通tree `ff9b5391d4bea5ae8e3b0e38942823ba939fcc1e`。

[AGK・AGL正式記録](docs/proofs/P4-Q2-PZ37AGK-AGL_verified_20261106.md) · [AGM正式記録](docs/proofs/P4-Q2-PZ37AGM_verified_20261106.md)

### OPEN — 実際の符号分離と幾何・質量誤差の精密化

元の有限列挙は非計算的定義を含み、24^L個の大体積数値表を実行した段階ではない。固定24中心の半径4/5と保守的な真正質量区間は粗く、m,nの増大だけで幾何・質量誤差が消えるとは結論しない。定義と不等式の数式確認では、現行の幾何予算は対称大域半径の2倍以上であり、raw signed intervalが大域区間全体を含むため、現在の最終交差は大域区間と同じになる（この精度評価は独立の新規Lean宣言としては数えていない）。次は厳密平均を利用した幾何誤差の改善、元Haar質量の精密化または積分の構造的簡約、具体的境界での認証区間の0からの分離である。

実際の非零signed transfer符号、二閾値殻非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明。

以下の既存本文は全て保存した履歴であり、旧「最新・次段階」よりこの追補を優先する。

---

## 検証済み定理 — AGJ（2026-11-06 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。[AGJ定理PR #6372](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6372) はMERGED。定理squash `f24be7665c82a40051873c7fcc3df65c1fc27b06`、検証済みsource `726c93be12e6f3eeb6cb4ae7b80a3b39330eb83d`。元Wilson作用・核・固定結合・中心化source・真正Haar/Perron/transfer/FF・公開root・Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変更。

### CLOSED — 元Wilson指数核の有限有理Taylor包囲

`P_n(q)=sum_{j<n} q^j/j!`、`R_n(q)=|q|^n(n+1)/(n!*n)` を計算可能な有理式として実装。`|q|<=1`、`n>0` で固定mathlibの `Real.exp_bound` から `|exp(q)-P_n(q)|<=R_n(q)` を証明した。正整数kによる `exp(q/k)^k=exp(q)` で指数の大きさを処理し、下端 `max(0,P_n-R_n)` を非負にしてから累乗する。負の下端を偶数乗して誤った正下界を作らない。

元の実数xが有理区間[lo,hi]に入り、`|lo/k|<=1`、`|hi/k|<=1` が成り立てば、計算可能な `expLower(lo,k,n)` と `expUpper(hi,k,n)` で実際のexp(x)を包囲するAFV証明付き区間を構成した。未知の指数値に対する区間oracleや非計算的な有理選択は必要としない。

### CLOSED — 元固定結合の無条件有理包囲と真正核への接続

五項Taylorの正確な有理計算により `exp(2/5)<3/2<exp(13/32)` を証明。既証明の元結合恒等式 `exp(64 beta0)=3/2` と単調性から **`1/160<beta0<13/2048`** を無条件に導いた。beta0自体は元の `log(3/2)/64` のままであり、小数値を物理的仮定として代入していない。

非負の元one-slab作用 `S_H(A,B)` に対する証拠付き区間[s_lower,s_upper]から、`-beta0*S_H(A,B)` の区間 `[-(13/2048)*s_upper,-(1/160)*s_lower]` を構成し、元Boltzmann恒等式で **真正 `K_H(A,B)=exp(-beta0*S_H(A,B))` の有理区間・AGA有理球**を得る。作用0なら核1、作用64なら核2/3の校正定理は、それぞれ元作用の等式を明示的入力とする。作用64の具体的配置の存在を主張していない。

### exact-source検証とLean4修正

新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalKernelTaylorIntervalV5_PZ37AGJ.lean` 1ファイル279行。既存Lean変更なし。[最終CI #42106035057](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42106035057) はworkflow・Changed Lean job `127520984143`・Lean step・独立receipt `127523984881` がcompleted/SUCCESS。artifact `13452332224` を取得・実検査し、**11,343 jobs成功**、14宣言の公理依存は標準公理のみ、sorryAxなし、変更AGJ warning/error 0/0。SHA-256 `e265fd9a6a4545f0aa9ec95a0081cf7379a42c78375678ebab81bdb23f642273` も一致。

source・test-merge `2aa1e0528d7e33e5d3d9bdce56ea1827c7d549c0`・squashは共通tree `bfdad9a8531b2520962de5e03fd39254b00c5ab5`。初回CI #42104807540 は固定結合証明の区間構造体をhaveで束縛したため展開できず、有理数から実数へのcastも不一致となった。構造体をletで保持し、Rat.cast_ltと明示的cast簡約へ修正。定理文・仮定は不変更。結合の有理不等式・負端点clip・零指数の3回帰例も最終ビルドで検証した。

### OPEN — 具体的原作用・質量・中心化平均

固定結合区間には正の幅があるため、Taylor次数を上げるだけで全核区間の幅がゼロに収束するとは結論しない。元作用の具体的区間、真正Haarセル質量、中心化平均は別途評価が必要。次段は真正中心配置の元Wilson作用を成分別に有理評価し、AGJの核区間とAGIの証明書へ接続する。実際の非零signed transfer符号、二閾値殻非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明。

以下のAGI以前の本文は全バイト保存した履歴であり、旧「最新・次段階」よりこの追補を優先する。

---

## 検証済み定理 — AGI（2026-11-06 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。[AGI定理PR #6370](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6370) はMERGED。squash `0601f8fd80737c6ad4e66e28bd8b1bf9be15e099`、exact-source `16e34e7f25d12bd234d8b71b69f452b565eb895d`。真正Wilson/Haar/Perron/transfer/FF・元中心化source・公開root・Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変更。

### CLOSED — 符号を保持する有限有理区間評価

計算可能な `rationalTable` と、元の中心値・真正Haar質量・元AGG変動係数との整合を要求する `certifiedTable : Prop` を分離した。中心区間[a_i,b_i]、真正質量区間[m_i,M_i]、有理幾何誤差gammaについて、l_i=a_i-gamma、u_i=b_i+gamma とし、`L=sum_i min(l_i*m_i,l_i*M_i)`、`U=sum_i max(u_i*m_i,u_i*M_i)` を正確な有理数演算で計算する。真正下側・上側Haar階段関数を元測度で積分し、AGEの同一性を使って **`L<=t_H(B)<=U`** をLean4証明した。負のセル係数では反対側の質量端点を使うため、符号を失わない。

元量との整合証拠がある表に限り、Boolean有理判定 `0<L` から真正 `0<t_H(B)`、`U<0` から真正 `t_H(B)<0` を導く。同一H・同一Bの異なる分割の証明済み区間を[max L,min U]で交差でき、正しい二証明書が相反する符号を認証しないことも証明した。AFV `verifiedInterval`・AGA `rationalBall` への接続を保持する。

### 検証・修正理由

新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSignedSpatialIntervalCertificateV5_PZ37AGI.lean` 1ファイル384行、既存Lean変更なし。[exact-source CI #42063129806](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42063129806) はworkflow・Lean job `127369907250`・Lean step・独立receipt `127373820378` がcompleted/SUCCESS。artifact `13433910241` の診断で **11,342 jobs成功**、13公理依存出力は標準公理のみ、sorryAxなし、変更AGI warning/error 0/0。artifact SHA-256 `5272b4267d34dba8ec5851b51e3266e548b0b3922fae0c47e4c6e2a3a7ad72d2` も一致した。

source・test-merge `3b2c63dc00156449ca17fb268444ed68c0a6ae94`・squashの共通Git treeは `1331e3d69c448a4a957a20a859c1c2ad91ccd36e`。初回CIでは有理演算のdecide簡約と共有境界変数の解決が失敗したため、同じ命題をnorm_numで証明し各定義に `{boundary : Cfg}` を明示した。仮定・結論を弱めていない。正・負・幾何誤差による判定不能の3回帰例は合成算術テストであり、実際のWilson/Haarデータとは主張しない。

### OPEN — 元作用からの区間生成

AGIは与えられた証拠付き区間表の健全性であり、実際の非零transfer符号を認証した結果ではない。次段AGJでは固定結合と元Wilson指数核の有理包囲を、有限Taylor演算と剰余評価から構成する。元作用・Haar質量・中心化平均の入力評価を混同しない。二閾値殻非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明。

以下のAGH以前の本文は全バイトを保存した履歴であり、旧「最新・次段階」よりこの追補を優先する。

---

# ROADMAP追補 — AGH検証済み・AGI区間証明書へ

## 検証済み定理 — AGH（2026-11-06 JST記録）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。[AGH定理PR #6367](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6367) は2026-11-05 JSTに **MERGED**。定理squash `71627744b2e7a57b2ff93e60f2fe16ae9e55bea4`、最終exact-source `31ca7e9947a27e50fc2b1656e68218810325ed15`。AGGまでの真正Wilson/Haar/Perron/transfer/FF、元Gauss-law中心化source、公開root、Lean `v4.30.0-rc2` とmathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変更。

### CLOSED — 全右境界に共通の任意精度・真正空間Haar求積

各固定有限体積Hと任意epsilon>0について、元空間配置の真正Borel有限分割・真正中心・有理Haar重みを一度選べば、すべての元右境界Bで `|t_H(B)-sum_i q_i(B) w_i|<epsilon` となる証明書の存在をLean4で証明した。分割・中心・重みはBに依存せず、中心値の有理標本だけがBに依存する。AGCの真正積分評価とAGEのHaar-a.e.等価性から、元のsigned transferそのものへ接続している。

AGGの元空間弦距離斜率 `L_H=6(1-k_H)+13 beta0 p_H`、AGFの真正被積分関数上界 `M_H=(1-k_H)p_H/2`、元リンク数ell_Hを使用する。`tau=epsilon/4`、`r=tau/(L_H ell_H+1)` を選び、ADPの真正SU(2)有限ネットからAFNのfirst-center Borelセルと元リンク積を構成。積距離半径は正しく `ell_H r` であり、次元因子を省略しない。

**セル数が確定してから質量精度を選ぶ。** 実際の積セル数Nを得た後に `delta=tau/(N(M_H+tau)+1)` と定める。すべてのBで `|q_i(B)|<=M_H+tau` なので、幾何誤差 `L_H ell_H r`、中心値有理近似誤差tau、Haar質量誤差の総和 `sum_i |q_i(B)| delta` を各tau以下に抑え、総誤差 `<=3epsilon/4<epsilon` を証明した。細分化だけで質量誤差総和が縮むという推論は使わない。分母の+1は零リンク・零振幅を含む退化場合も扱う。

`p4Q2PZ37AGH_exists_uniformQuadrature`、`p4Q2PZ37AGH_uniformQuadrature_accuracy` と任意の正の有理半径への `p4Q2PZ37AGH_originalTransferRationalBall` を追加。「全右境界Bで共通」は固定Hの一様性であり、Hについての一様性ではない。

### exact-source検証と記録訂正

新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformSpatialHaarQuadratureV5_PZ37AGH.lean` 1ファイル・423追加行、既存Lean変更なし。[最終CI #42033094163](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42033094163) はworkflow・Changed Lean job・Lean step・独立completion receiptがcompleted/SUCCESS。診断artifact `13416763826` の `lean-fast.log` を再検査し、**11,341/11,341 SUCCESS**、新規16宣言は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更AGH warning/error **0/0** を確認。

source、test-merge `21ff2dbf30ac7a24b7618bb052a4be755b7459bc`、定理squashの正しい共通Git treeは **`c7cc67bf68af2c64ff60ef7f92fc9920ecb250ce`**。前PRコメントの `dbcb336f...` は転記誤りで、Git-commit APIの三者再取得により訂正した。独立completion receiptの正しいjob IDは `127267191687`。訂正はPRにも追記し、元記録は削除していない。証明修正は積セル所属のリンク型の明示と、加法不等式の両項を `add_le_add`・`le_refl` で対応させたもの。定理文・物理的仮定の弱化なし。

### OPEN — 数値表の評価とAGIへの接続

有限ネット・有理包囲は依然として古典的な非計算的選択を用いる。今回確定したのは任意精度の求積証明書の存在であり、具体的な中心値・Haar質量の有理数表を算出したという意味ではない。次段AGIでは、供給された有理区間と元の真正量との整合証拠を入力とし、有限の区間演算から元transferの上下界・符号へ接続する形式化を進める。実際の正負分離、二閾値殻非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明。

以下のAGG以前の本文は全バイトを保存した履歴。旧「最新・次段階・OPEN」よりこの追補を優先する。

---

## 検証済み定理 — AGG（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAPの文書ミラー。AGF定理 #6361・正本文書 #6362・mainミラー #6363 のすべてのMERGEDを継承し、[AGG定理PR #6364](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6364) は **MERGED**。検証済みexact-source HEAD `5e87f9091f9b2bfbdfb9b3ae83d520ac0ffd1946`、AGG定理squash SHA `e987e7cd3481d14e30a74357a7bccccf3497721a`。真正SU(2) Wilson作用・正規化空間Haar・ZW中心化Gauss-law source・元one-slab Perron/transfer/FF、Lean/mathlib pins、公開rootは一切変更しない。

### 真正空間リンク弦距離による無条件Wilson振動係数

- **元の物理幾何に対する有限座標telescoping**：ADKの真正SU(2)弦距離 `d_J` と元空間リンクの有限集合に対し `D_sp,H(A,C)=Σ_e d_J(A_e,C_e)` を定義。AEMで無条件証明済みの空間Wilson作用1リンク斜率24とAEP/AETの有限座標Lipschitz移送から、元AFZの真正連続中心化source `f_c(A)=½(W_c(A)−m_H)` について **`|f_c(A)−f_c(C)|≤12 D_sp,H(A,C)`** をLean4証明。元のHaar平均は差分で厳密に消去し、任意のL²代表元との不正な点wise同一視をしない。
- **真正one-slab核の第一境界変動を証明**：AEMの右側1リンク核係数 `13β₀` と既証明の元対称Wilson核 `K_H(A,B)=K_H(B,A)` を合わせ、全空間リンクへのtelescopingで **`|K_H(A,B)−K_H(C,B)|≤13β₀ D_sp,H(A,C)`** を証明。代理核・独立Haar・新しい正則性仮定は導入しない。
- **真のAGE連続被積分関数の積差分評価**：AGBの真正核中点半径 `(1−k_H)/2`、AGFの`|f_c|≤p_H`、上記の真正source/核差分を積の差の恒等式で接続して、**`|g_B(A)−g_B(C)|≤L_H D_sp,H(A,C)`** を無条件形式証明。係数は **`L_H=6(1−k_H)+13β₀p_H≥0`**。ここで`g_B(A)=f_c(A)(K_H(A,B)−(1+k_H)/2)` は元AGEの真正連続代表元そのもの。各有限Hで成立するが`p_H`・`k_H`を含むため体積一様係数とは主張しない。
- **真正24中心Haar積セルを直接評価**：AGE・AGDの実際のAFQ指定中心 `a_i` と真正空間積セルの既証明半径`d_J(A_e,a_{i,e})≤4/5` から、**`D_sp,H(A,a_i)≤(4/5)|Link_H|`** を証明。これによりAGEの外部仮定不要な幾何学的`originalSpatialOscillation`を`ε_geom=L_H(4/5)|Link_H|`で構成。
- **tighten-only hybrid証明書を構成**：AGFの元全球上界`ε_global=(1−k_H)p_H`と新幾何上界から **`ε_H=min{ε_global,ε_geom}`** を真正AGE積セルに対して無条件に導出。元AGEの真正signed transfer有理求積に直結し、**`|t_H(B)−Σ_i q_iw_i|≤ε_H+1/64+Σ_i|q_i|δ_i`** を保持する。AGDの固定24中心セルでは`ε_geom`が`ε_global`より小さいとは限らないため、「数値誤差が厳密に減少した」とは主張しない。`q_i`はAGEの非計算的な有理稠密選択で、具体的な評価済み有理表ではない。

### exact-source Lean4・公理監査・source/test-merge一致

- AGGで追加したのは新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSpatialChordalCellOscillationV5_PZ37AGG.lean` **1ファイル・382追加行**のみ。既存Lean、元物理量、workflow、公開root、Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変更。
- 初回sourceの絶対値積差の証明で`abs_mul`と三角不等式の順序を確認し、証明本体を明示的`calc`に修正した。元の定理文・既存物理的仮定は変更なし。修正後の最終[exact-source CI #42025445563](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42025445563)は **11,340 / 11,340 SUCCESS**。`#print axioms`新規13件すべて`propext`・`Classical.choice`・`Quot.sound`のみで`sorryAx`なし、変更AGG warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- CI検証済みsource `5e87f9091f9b2bfbdfb9b3ae83d520ac0ffd1946` とGitHub test-merge `c9f00398fc0511a9ce1ccd1c7f4ac2503cb39fce` はGit tree `8194ed45d609844a52963e76766a173994e5d698` で完全一致。検証済みHEAD指定で定理をsquashマージした。

### 未解決obstructionと次の研究

幾何学的なゼロ距離連続性と真正積セルの証明書は得られたが、固定24中心の粗いセル半径と高次元のAGD Haar質量区間は保守的。非計算的有理`q_i`の実効的な区間評価、真正transferの非零符号分離、二閾値殻非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。次段はより小さな真正AFQ/ADPネットセルと、具体的なHaar質量およびWilson被積分関数の区間演算による誤差縮小・符号判定証明書を検討する。

---

## 検証済み定理 — AGF（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAP文書ミラー。AGE定理PR #6358、正本文書 #6359、main文書ミラー #6360 のMERGEDを継承し、[AGF定理PR #6361](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6361) も **MERGED**。検証済みexact-source HEAD `933d72ac12cfa5f8182067f22689c078d2cfa1a0`、AGF定理squash SHA `d78801d20f0c38466176c8442d0ea434cf50d1e1`。元の真正SU(2) Wilson/Haar、ZW Gauss-law中心化物理source、元のone-slab Perron/transfer/FF、AFQ指定24中心とAGD積セル、固定Lean/mathlibを変更しない。

### 元の中心化Wilson sourceと真正核からセル内振動上界を無条件導出

- **点wiseに正しい連続代表元だけを評価**：AFZの元空間Wilson連続作用 `W_c(A)`、元の真正Haar平均 `m_H`、実際の空間plaquette列長 `p_H` を使用。証明済み `0≤W_c(A)≤2p_H`、`0≤m_H≤2p_H` から、元の連続中心化source `f_c(A)=(W_c(A)−m_H)/2` に対して、全真正空間配置 `A` で **`|f_c(A)|≤p_H`** をLean4で証明。任意のL²代表元の値を点ごとに同一視せず、AGEのHaar-a.e.等価性と真正積分値を継承する。
- **真正one-slab核の定数相殺を保持**：AGBで証明済みの元Wilson核範囲 `k_H≤K_H(A,B)≤1` と真正中点 `(1+k_H)/2` を使用。`g_B(A)=f_c(A)(K_H(A,B)−(1+k_H)/2)` について、全ての元境界 `B` と空間配置 `A` で **`|g_B(A)|≤(1-k_H)p_H/2`** を形式証明した。独立の核やsourceを導入しない。
- **無条件の全域振動証明書**：上記の絶対値上界から、全真正空間配置 `A,C` について `|g_B(A)−g_B(C)|≤(1-k_H)p_H≤p_H` を証明。`k_H>0`、`k_H≤1` は既存のWilson核定理に由来する。これをAGDの真正24中心リンク積セルすべてへ適用し、AGEの `originalSpatialOscillation` を **`epsilon=(1-k_H)p_H`** と、計算しやすい保守的な **`epsilon=p_H`** の2系統で、外部の振動仮定なしに構成した。
- **AGEの真正signed transfer有理求積へ直接接続**：AGEで構成した真正物理中心値からの非計算的有理標本 `q_i` と、AGDで証明した元Haar積セル質量の有理重み `w_i`・誤差 `δ_i` をそのまま利用し、外部の物理振動入力なしで **`|t_H(B)−∑_i q_iw_i|≤p_H+1/64+∑_i|q_i|δ_i`** をLean4で証明。定理は実際の元signed transfer積分に適用され、代理測度・代理物理量に降格していない。
- **限界を明示**：振動上界は全球的な値域から導いたため、AGDセルの真正弦距離半径 `4/5` はまだ誤差縮小に使用していない。AGEの `q_i` は非計算的な有理密度選択であり、実際に算出した数値標本ではない。したがって非零transfer符号を確認したとの主張はしない。

### Exact-source Lean4 CI・公理監査・ソース一致

- AGFで変更したのは新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAutomaticSpatialHaarOscillationV5_PZ37AGF.lean` **1ファイル・207行**だけ（`#print axioms` 8件）。既存Lean、Wilson/Haar/transfer/Perron/FF、固定Lean `v4.30.0-rc2` とmathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、workflow、公開rootは不変更。
- 初回CI #42019752887は固定mathlibの三点不等式 `abs_sub_le a b c` を二引数で使用したため不成功。このため後続定理に一時的な`sorryAx`が伝播した。変更AGF全文と依存署名を照合し、中間点 `0` を明示して修正。定理文や既存物理的仮定の弱化はない。
- 最終[exact-source CI #42020515257](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42020515257) は **11,339/11,339 SUCCESS**。新規8件の公理依存は標準 `propext`・`Classical.choice`・`Quot.sound` のみで`sorryAx`なし、変更AGF warning/error 0/0、独立MCP completion receipt SUCCESS。source/test-merge Git treeは `9217f02c34bb8b6a11154988038653d006af2cf7` で完全一致した。

### 未解決の物理的障害・次段AGG（研究候補）

AGFはAGEのセル内振動入力を元の物理定理だけで解消したが、全球上界 `epsilon=p_H` は保守的で、高次元のAGD Haar質量区間誤差 `δ_i` も大きい。非零の具体的有理標本、真正transfer符号の厳密な正負分離、二閾値殻非空性、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは**未証明**。次段AGGでは元の空間Wilson作用・one-slab kernelの**各リンク弦距離に比例する変動係数**と、AGEで形式証明したAFQリンク半径`4/5`を接続し、真正セル内誤差を縮小することが課題。

---

## 検証済み定理 — AGE（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAPの文書ミラー。AGD定理 #6355、正本文書 #6356、main文書ミラー #6357 のMERGEDを継承し、[AGE定理PR #6358](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6358) も **MERGED**。検証済みexact-source HEAD `384f0238b3a65e7889902717bec9d3be765ec65e`、AGE定理squash SHA `690670e85cae2ee27d2fb1d79e5e39ca1aebfb0b`。真正SU(2) Wilson作用・正規化Haar／全空間積Haar・元ZW Gauss-law中心化L² source・元one-slab transfer・Perron/FF・AFQ真正24中心は変更していない。

### L²代表元から真正連続Wilson被積分関数への厳密な接続

- **元の物理量だけを使用**：AFZの真正連続Wilson中心化source `f_c(A)=½(W_c(A)−m_H)` と、AGBの元の真正one-slab Wilson核 `K_H(A,B)` および実際の下界 `k_H` を組み、`g_B(A)=f_c(A)(K_H(A,B)−(1+k_H)/2)` を構成。元Wilson作用・核から `g_B` の連続性を証明し、元AGCのL²代表元を評価する被積分関数と **Haar-a.e.で一致すること**を証明。L²同値類の値があらゆる点で連続代表元と一致するとは仮定していない。
- **真正transfer積分の同一性**：AFZのL²等式、`ContinuousMap.coeFn_toLp`、AGCの真正中心化核積分恒等式を接続し、`∫g_B(A)dμ_H(A)=t_H(B)` を形式証明。新規の代理source・代理Haar確率や置換transfer作用素は導入しない。

### 真正AGD積セル上の有理中心と条件付き局所誤差

- **真正24中心の有限リンク積**：AGDの各元空間リンク上の真正AFQ指定中心を並べた有限配置 `a_i` を構成。各AGD積セル内のすべての元空間配置 `A` について、各リンクの真正Wilson弦距離 `d_J(A_e,(a_i)_e)≤4/5` を証明。最初の中心によるBorelセルでは、指定中心自体がそのセルに属するとは仮定しない。
- **実際の中心値の有理包囲**：`g_B(a_i)` をAFNの有理数稠密性から非計算的に選択した `q_i∈ℚ` で `|g_B(a_i)−q_i|≤1/64` と形式証明。これは真正物理値を数学的に包囲する*存在証明付きの選択*であり、測定・数値積分で得た計算済みの具体的な有理値表ではない。
- **未解決のセル内振動を独立の証明入力として保持**：全AGDセル上の真正連続物理関数 `g_B` に対して、`|g_B(A)−g_B(a_i)|≤ε` を証明した入力 `epsilon≥0` がある場合に限り、セル内包含 `|g_B(A)−q_i|≤ε+1/64` を証明。これとAGDの真正空間Haar質量 `w_i,δ_i` を使い、**`|t_H(B)−∑_i q_iw_i|≤ε+1/64+∑_i|q_i|δ_i`** をLean4で形式証明する。
- **既存AGA有理区間・厳密符号判定へ移送**：右辺を包含する証明付き有理半径 `r≥0` があれば元真正signed transferの `rationalBall` を生成。厳密な `r<∑q_iw_i` なら `t_H(B)>0`、`∑q_iw_i<−r` なら `t_H(B)<0`。実際に符号分離する非零中心・誤差半径を認証したとの主張ではない。AGCのL²代表元に対して不正なpointwise一致を要求するのではなく、同じ真の積分値を連続代表元で証明する独立経路とした。

### Exact-source Lean4 CI・公理監査・Git tree

- 追加Leanは `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalContinuousSpatialHaarCellwiseV5_PZ37AGE.lean` のみ（313行、`#print axioms` 10件）。既存Lean・物理量・workflows・公開root・Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変。
- 初回CI #42003757426は説明コメント中の `+/-` をLeanブロックコメント開始と解釈した字句監査エラーで不成功。次CI #42003973562では連続核の合成型判定タイムアウトと局所`cells.cell`記法の識別子解決エラーが生じた。Lean全文・imports・AFZ/AGB/AGC/AGDの定義とpinned mathlib APIを確認し、型付き連続写像合成と明示的セル参照へ修正。定理文・仮定は弱化していない。
- 最終[exact-source CI #42005520130](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42005520130) は **11,338/11,338 SUCCESS**。10件の公理依存は標準 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更AGE warning/error **0/0**、独立completion receipt **SUCCESS**。source/test-merge Git tree は `11b71794d1507a447a7378990f093ab49cff0280` で一致。

### 未解決obstruction・次段AGF（研究候補）

AGEは元の真正transfer積分に対する**連続代表元の型付き有理求積経路**を検証したが、元の連続Wilson被積分関数の具体的なセル内振動幅 `ε`、厳密な実効的有理評価表、数値的に正負を分離する半径は未認証。次段AGFでは真正Wilson空間作用・one-slab核のリンク変動係数とAFQ指定中心の4/5弦距離を組み、セル内振動の上界を新しい物理仮定なしに導出することが課題。真正二閾値符号殻の非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。

---

## 検証済み定理 — AGD（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAPの文書ミラー。AGC定理 #6352、正本文書 #6353、main文書ミラー #6354 のMERGEDを継承。[AGD定理PR #6355](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6355) は **MERGED**。最終検証済みexact-source HEAD `9f64b710f5be2b8194e06505f927fd9a52d3ca7a`、定理squash SHA `a2f7e77f5c956cfdbde3b812daa671db625d5b92`。元のSU(2) Wilson・正規化Haar・ZW Gauss-law中心化source・Perron/transfer/FF・AFQ真正24中心・AFT有理質量境界を変更しない。

### 真正SU(2) 24セルの全空間リンク積とHaar積公式

- **元の空間配置そのものの有限分割**：AFQ真正24中心の最初の中心Borelセル `C_i` は、単一リンクSU(2)上で可測かつ一意分割。元の有限空間リンク型 `Link_H` に対し、積セルindex `j:Link_H→Fin 24` と `C_j={A:Cfg_H | ∀e, A_e∈C_{j(e)}}` を構成。すべての元の空間配置 `A` がただ一つの積セルへ属することと、各積セルが元Haar積σ代数で可測であることをLean4で証明。リンク数を `L_H=Fintype.card Link_H` とすると、indexは24進の有限リンク配列である。
- **真正空間Haar質量の厳密積**：元の定義 `μ_H=Measure.pi(e↦normalizedCompactHaar(SU(2)))` を直接使用し、`μ_H(C_j)=∏_{e:Link_H} μ_{SU(2)}(C_{j(e)})` を形式証明。実数値 `Measure.real` に移した積公式も証明。代理離散測度や独立性の未証明追加仮定は導入しない。
- **無条件の有理有限体積質量区間**：既証明AFTの各真正一リンク質量 `1/160000 ≤ μ(C_i) ≤ 625/1781` から、`α_H=(1/160000)^{L_H}∈ℚ`、`β_H=(625/1781)^{L_H}∈ℚ` を定義し、全積セルについて `α_H ≤ Measure.real μ_H(C_j) ≤ β_H` と `α_H≤β_H` をLean4で証明。リンク数0を含む有限Hの形式的境界も保持する。
- **AGCへ厳密に接続**：真正積セルを `Fintype.equivFin` で有限Fin-indexへ変換。固定有理重み `w_j=(α_H+β_H)/2`、明示的質量半幅 `δ_j=(β_H−α_H)/2≥0` とし、`|Measure.real μ_H(C_j)−w_j|≤δ_j` を証明した `p4Q2PZ37AGC_originalHaarCells H` を外部質量入力なしで構成。未検証の数値質量や新しい測度を持ち込まず、既存AGCの条件付きsigned transfer求積へ降下する。

### Exact-source Lean4検証と構造的修正履歴

- 新規Leanのみ：`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSpatial24CellHaarProductV5_PZ37AGD.lean`（245行、`#print axioms` 7件）。既存Lean・公開root・物理定義・workflows・Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変。
- 初回CI #41998809889 の5件は、Set.piのmembership展開、`Set.mem_univ_pi` の引数、Rat実数cast/冪正規化が原因。修正後CI #41999606512 の残る1件は `(625/1781)^L = 625^L/1781^L` に関する`div_pow`正規化。変更Lean全文・imports・AFQ/AFT/AGC依存型を照合し、仮定や結論の弱化なく解消。
- 最終[exact-source CI #42000355155](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42000355155) は **11,337/11,337 SUCCESS**。新規7件の`#print axioms` はすべて標準 `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` なし。変更AGD warning/error **0/0**、独立MCP completion receipt **SUCCESS**。source／GitHub test-merge Git treeは `b297ccb73fdd1456d8e7c6335249d77d79192cae` で一致。

### 未解決の物理的障害・次段AGE（研究候補）

AGDは真正空間Haar積セルの完全な有限分割と明示的な**質量区間証明書**を構成したが、元のsigned centered Wilson/transfer被積分関数のセルごとの有理標本・局所包含誤差は未取得。AGCの非零有理中心を具体的に認証するには、真正連続Wilson代表元と元L²中心化sourceのa.e.対応、積セルの半径評価、核の変動率、有限個の実際の被積分関数の厳密有理値区間を接続する必要がある。固定質量区間は高次元で保守的であり、非零符号・真正二閾値殻非空・体積一様coercivity・Hamiltonian spectral gap・連続体4D Yang–Mills質量ギャップは**未証明**。

---

## 検証済み定理 — AGC（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAP文書ミラー。AGB定理 #6349、正本文書 #6350、main文書ミラー #6351 のMERGEDを継承し、[AGC定理PR #6352](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6352) も **MERGED**。検証済みexact-source HEAD `f240839db18c28006e95c7a2d0ee59dc9d78fd0e`、AGC定理squash SHA `e974870773c167993e2f5ceaaea0d9357e2ec56c`。真正SU(2) Wilson・元ZW中心化Gauss-law source・Perron/transfer/FF・元空間Haar・AFQ 24中心・固定Lean/mathlib pinは不変。

### 元の全空間Haar積分に対する符号付き有理中心・包含誤差

- **元のtransferを直接使用**：AGBの真正Haar平均ゼロと核の定数相殺を継承。`k_H` を元Wilson one-slab核の大域下界とすると、任意の元境界 `B` で `t_H(B)=∫f_H(A)(K_H(A,B)−(1+k_H)/2)dμ_H(A)`。新しい核・代理source・別の確率測度への置換はない。
- **真正空間Haar有限分割の型付き証明書**：元全空間配置 `Cfg_H` の有限可測分割 `C_i` に対し、厳密な被覆・重複なしの証明、真正正規化空間Haar質量 `μ_H(C_i)` の有理近似 `w_i∈ℚ` と検証誤差 `δ_i≥0`、元の符号付き中心化核積分関数のセル上の有理標本 `q_i∈ℚ` と誤差 `ε≥0` を要求する。この入力は**証明を伴う条件付き証明書**であり、具体的な有限数値表を実測・認証したものではない。
- **Lean4形式証明された真正signed transfer包含**：有限セル積分計算を元Haar上でそのまま行い、`q=∑_i q_i w_i∈ℚ`、`E=ε+∑_i|q_i|δ_i` に対し `|t_H(B)−q|≤E` を証明。検証済み有理半径 `r∈ℚ_{≥0}` が `E≤r` を満たす場合、`|t_H(B)−q|≤r` のAGA `rationalBall` およびAFV `verifiedInterval` を自動構成。AGBのゼロ中心包囲と異なり、入力表に応じて中心 `q` は**非零でもよい**。
- **符号条件を曖昧にしない**：証明済みの有理不等式 `r<q` なら元真正transfer `t_H(B)>0`、`q<−r` なら `t_H(B)<0`。実際にその条件を通過する具体的有理表、元FF受信器の二符号点、真正二閾値殻を得たとの主張ではない。既存AGA→AFV区間接口は維持する。

### Lean4 exact-source CI・公理依存・source/tree対応

- AGC追加ファイルは `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSpatialHaarSignedQuadratureV5_PZ37AGC.lean` のみ（404行・`#print axioms` 14件）。既存Lean・元Wilson/Haar/Perron物理量・CI workflow・公開root・Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は変更なし。
- 初回CI #41995905081はLean4構造体の `H` パラメータの二重捕捉、局所核下界記法 `k` と証明中変数の衝突、無名sectionの未閉鎖で不成功。**変更AGC Lean全文とAFJ・AGB・AGAの依存定義を確認し、元定理文を弱めず修正**した。
- 修正後の[exact-source CI #41996756761](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41996756761) は **11,336/11,336 SUCCESS**。14件の公理監査は全て標準 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Leanエラー0、completion receipt SUCCESS。source/test-merge Git tree は `8aa6c88c8a0541cc244ebee403b946e07737b69e` で一致。

### 未解決obstruction・次段AGD（研究候補）

AGCは真正空間Haarに対する**条件付き有限有理積分証明書の一般定理**であり、元空間配置の具体的セル分割の構築、真のHaar質量の精密な有理評価、元L² source代表元の局所包囲、区間半径の実効的縮小と非零符号点の認証はまだ必要。次段ではAFQ真正SU(2) 24中心セルの有限リンク積分割と、元核・中心化sourceに対する局所誤差の結合を研究する。真正二閾値殻の非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは**未証明**。

---

## 検証済み定理 — AGB（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAPの文書ミラー。AGA定理 #6346、正本文書 #6347、mainミラー #6348 のMERGEDを継承し、[AGB定理PR #6349](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6349) も **MERGED**。検証済みexact-source HEAD `76dc9fc62f38659f69d6b5bb6bb1260b8bb7a538`、定理squash SHA `526dc6016dcb5fcc25ca8fb0d8b2f504f3c19807`。真正SU(2) Wilson作用・正規化Haar・ZW中心化Gauss-law物理source・Perron/transfer/FF受信器・AFQ真正24中心・AFT固定有理重みは不変更。

### 真正ZW中心化sourceのHaar平均ゼロと元Wilson核の定数相殺

- **真の中心化sourceの期待値は厳密0**：元の空間Wilson連続代表元 `W_c(A)`、真のHaar平均 `m_H=∫W_c dμ_H`、既存ZW Gauss-law中心化sourceのHaar-L²代表元 `f_H(A)=½(W_c(A)−m_H)`（Haar-a.e.）を直接使用し、`∫f_H(A)dμ_H(A)=0` をLean4で証明。代理source・再定義測度や平均ゼロの追加公理は導入しない。
- **元のsigned transferの厳密な恒等式**：真正one-slab Wilson核 `K_H(A,B)` と元のtransfer `t_H(B)=∫f_H(A)K_H(A,B)dμ_H(A)` について、任意の実定数 `c` に対し `t_H(B)=∫f_H(A)(K_H(A,B)−c)dμ_H(A)` を証明。定数核成分の消去は真のHaar平均ゼロに由来し、物理transfer作用素は変更しない。
- **真正核の中点で半幅を改善**：既証明の元Wilson核の大域範囲 `k_H≤K_H(A,B)≤1`（`k_H=exp(−β₀·originalOneSlabActionBudget(H))>0`）に対し `c=(1+k_H)/2` を用い、`|K_H(A,B)−c|≤(1−k_H)/2`。AEVの元signed variationと元sourceのHaar-L¹質量 `M_src,H` より `|t_H(B)|≤(1−k_H)M_src,H/2≤p_H/2` を導出。ここで `p_H` は実際の空間plaquette列長。AFZの `|t_H(B)|≤p_H` を無条件に半減する。より鋭い `(1−k_H)M_src,H/2` の実数評価も保持。

### 有理区間証明書と既存の真正物理降下

- **具体的な有理半径**：`q_H=(periodicHypercubicEvenSpatialSlicePlaquetteList H).length/2∈ℚ` と `(q_H:ℝ)=p_H/2` をLeanで証明。元の符号付きtransferについて、全境界 `B` で真の包含 `−q_H≤t_H(B)≤q_H` を満たすAFV `verifiedInterval` を外部数値入力なしで構成。
- **実際の24中心更新先へ一貫して適用**：元AFG境界サンプルで未更新 `B` と真正AFQ SU(2)中心 `g_i` による更新境界 `B[e:=g_i]` の両方に、同じ証明付き包含を自動供給。AGA transfer-only、AFX厳密四文字、AFV→AFT→AFIの真正係数／分散証明書へ型付き接続。`toOriginalCoefficientVariance` は既存シェル標本 `c` と `0≤lo` を保持する。
- **符号認証との境界**：改善区間の中心は依然として厳密0で、非零transfer符号やFF受信器の正負を証明したわけではない。AGAの有理符号分離条件が満たされたとの主張はしない。既存の条件付き鋭い証明書を弱化しない。

### exact-source Lean4 CI・公理監査・Git tree

- AGBの追加は `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCenteredTransferKernelCancellationV5_PZ37AGB.lean` 1ファイル（292行、`#print axioms` 10件）のみ。既存Lean・workflow・公開root・固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は変更なし。
- [exact-source CI #41991998412](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41991998412) は **11,335/11,335 SUCCESS**。新規10件の公理監査は標準 `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` なし。変更AGB warning/error 0/0、独立MCP completion receipt SUCCESS。source／GitHub test-merge Git tree は `6f20b247fcc2faec4a747a1cfc00a1e9e72c7050` で一致。マージ後の定理正本HEADは `526dc6016dcb5fcc25ca8fb0d8b2f504f3c19807`。

### 未解決obstruction・次段AGC（研究候補）

非零中心を持つ、**元の真正signed transfer積分の検証付き有理包含**は未取得。次段AGCでは元のWilson作用とHaar平均の相関から具体的なsigned transfer標本の有理中心 `q≠0` と厳密包含誤差 `ε` を構成し、AGAの `q>ε` または `q<−ε` を通す条件を研究する。証明されない数値サンプルを非零と仮定しない。真正二閾値符号殻の非空証明、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。

---

## 検証済み定理 — AGA（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAP文書ミラー。AFZ定理 #6343、正本文書 #6344、main文書ミラー #6345 の全件MERGEDを継承し、[AGA定理PR #6346](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6346) も **MERGED**。最終exact-source HEAD `88fa8310169d44e21288bb73da223cb73bb1d2c8`、定理squash SHA `9e2dc0526493d0fcc96784ceb590254969ebfc16`。真正Wilson SU(2)・正規化Haar／境界pair-Haar・元Gauss-law中心化物理source・Perron/transfer/符号付きFF受信器・AFQ真正24中心・AFT固定有理重みは変更していない。

### 真正FF物理受信器の符号付き有理区間・積誤差

- **元の真正物理恒等式**：AFZが証明済みの `F_e(z,g)=a(u-rv)` をそのまま使用。ここで `a=‖T_H‖⁻¹>0`、`u=t_H(B)`、`r=ρ_H(z)/ρ_H(z_g)`、`v=t_H(B_g)` はすべて既存の真正Perron/transfer/FF物理量。新規AGAの `rationalBall` は `sample∈ℚ`、`radius∈ℚ`、`radius≥0`、`|x−sample|≤radius` を型付きで持ち、既存AFVの真正有理端点区間から変換できる。
- **四因子の厳密な誤差合成**：入力を `(q_a,ε_a),(q_u,ε_u),(q_r,ε_r),(q_v,ε_v)` とすると、`q_w=q_u−q_r q_v`、`E_w=ε_u+|q_r| ε_v+|q_v| ε_r+ε_r ε_v`、`q_F=q_a q_w`、`E_F=ε_a(|q_w|+E_w)+|q_a|E_w` はすべて明示的有理数。Leanで `|F_e(z,g)−q_F|≤E_F` を、既存AFV証明書の型を使って証明。積誤差の交差項 `ε_r ε_v` は省略しない。
- **真正符号判定の十分条件**：証明付き区間の `q_F>E_F` なら `F_e(z,g)>0`、`q_F<−E_F` なら `F_e(z,g)<0` を形式証明。さらに、**`a=‖T_H‖⁻¹>0` のため `F_e=a(u−rv)` の符号は `u−rv` の符号と一致**するので、精密な逆ノルム認証を要求しない独立の正負判定定理を追加。元のtransfer積分の有理区間だけを入力し、AFZの既証明Perron比の `[0,3/2]` を自動投入する `transferOnly_originalBracketBall` が `q_w>E_w` または `q_w<−E_w` を確認できたときのみ、実際の受信器の符号を結論する。
- **既存物理証明書への型付きdescent**：元の真の4因子区間から受信器の真正有理包含区間を構築し、**AFW→AFX→AFV→AFT→AFI** の既存24中心Fourier係数／分散証明書へ接続。AFZの `‖T_H‖⁻¹∈[0,Q_H]` と `ρ(z)/ρ(z_g)∈[0,3/2]` を使った低精度transfer-only入力も別経路として実装。低精度区間自体は非零符号を保証しない。正負に分かれる実際のtransfer区間が確認されたという主張はしない。

### Lean4 exact-source CI・公理監査・Git tree

- 新規Leanファイルは `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSignedFactorIntervalsV5_PZ37AGA.lean` のみ（465行・`#print axioms` 21件）。既存Lean・Wilson/Perron/transfer/FF物理量・公開root・CI workflowは変更せず。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` のpinを保持。
- 最終[exact-source CI #41989125954](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41989125954) は **11,334/11,334 SUCCESS**。全21件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` なし。変更AGAのwarning/error 0/0。独立MCP completion receipt `chatgpt-ci-receipt/PR Lean Fast Check` はSUCCESS。source HEAD・PR test-mergeのGit treeは `7d67f73aa8babb10490fc603a3de25c50c17a456` で一致。
- 初回AGA HEADのCI不成功は独立に扱い、最終成功したHEADのみをマージ対象にした。元の符号判定を曖昧にする不正確な数値サンプルや仮想Perron法則は作らない。

### 未解決の物理的障害・次段候補 AGB

元の真の符号付きtransfer積分 `t_H(B)` と `t_H(B_g)` に対して、非自明な有理中点・誤差を持つ**実際に検証済みの包含証明**が必要。Perron密度比の粗い `[0,3/2]` を絞るか、比による差の相殺を定量化して、上記符号検査を通すことが次の課題。二閾値殻の非空認証、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは**未証明**。

---

## 検証済み定理 — AFZ（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAPの文書ミラー。AFY定理 #6340、正本文書 #6341、mainミラー #6342 のMERGEDを継承し、[AFZ定理PR #6343](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6343) は **MERGED**。最終exact-source HEAD `17703818947cfee5f7d0cb5bf1e227fba3d561c6`、定理squash SHA `92e590996451eef2e7850372ddb3bca3d3be2eb4`。真正SU(2) Wilson作用・元の正規化Haar／境界pair-Haar・Gauss-law中心化物理source・Perron/transfer/符号付きFF受信器・AFQ真正24中心・AFT有理重みは不変更。

### 元の真正物理受信器に対する外部区間入力なしの有理包囲

- **明示的有限体積有理数**：元の空間plaquette列の長さを `p_H`、元のone-slab組合せ体積（plaquette列長＋link列長）を `v_H` とし、`n_H=(v_H+31)/32`（自然数除算）、`Q_H=(3/2)^n_H∈ℚ`、`R_H=(5/2)p_H Q_H∈ℚ` を定義。固定結合 `β₀=log(3/2)/64` の既証明恒等式 `exp(64β₀)=3/2` と元物理transferノルム下界より `‖T_H‖⁻¹≤Q_H` をLean4で導出した。
- **本物の中心化Gauss-law sourceからの評価**：元のWilson空間作用の `0≤W_H≤2p_H` と真のHaar平均の同範囲包含を使い、元ZW中心化sourceの真のHaar-L²代表元が `|(f_H:A↦ℝ)|≤p_H` をHaar-a.e.で満たすことを証明。元の符号付きsourceに対するHaar-L¹量 `M_src,H≤p_H`、真正Wilson核 `0<K_H≤1` から、元のsigned transfer積分 `|t_H(B)|≤p_H` を導出。仮想source・正値sourceへの置換はない。
- **Perron比と真正FFの有理区間**：既証明AELの元joint sqrt-densityの1リンクHarnackと `exp(8β₀)≤3/2` から、元右境界を1リンク更新した密度比 `0≤ρ_H(z)/ρ_H(z_g)≤3/2` を証明。元ABZ/AFMの真正FF恒等式 `F_e(z,g)=‖T_H‖⁻¹[t_H(B)−ρ_H(z)t_H(B[e:=g])/ρ_H(z_g)]` を用い、**全ての有限H・元境界z・真のSU(2) gに対して `|F_e(z,g)|≤R_H`** と形式証明。`[-R_H,R_H]` は元AFVの `verifiedInterval` の証明付き真正包囲となり、AFWの受信器区間の外部入力をこの保守的包囲で満たせる。
- **元物理証明書への直結と限界**：元 `F_e(z,z.2(e))=0` の厳密恒等式、上記区間の有理中点 `0` と誤差 `R_H` をLean4で証明。元AFX→AFV→AFT→AFI係数・分散証明書へ型付き接続。さらに、この選択による真正24中心AFTの係数sampleは **厳密0** と証明した。これは非零係数・正負符号・真正非空二閾値殻の数値認証ではなく、精密なsigned receiver intervalの課題は残る。既存のより鋭い条件付き区間証明書は保持する。

### exact-source Lean4 CI・公理監査・Git tree

- 新規Leanは `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalRationalReceiverEnvelopeV5_PZ37AFZ.lean` のみ（416行、19件 `#print axioms`）。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、既存Lean・物理モデル・公開root・workflowsは変更なし。
- 初回CI #41932350756はnotation projectionのquotation失敗とL²内積のelaboration失敗から不成功。Lean4の記法・real inner product・作用素ノルム型・不等式向き・定義展開を修正。最終[exact-source CI #41957129057](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41957129057)は **11,333/11,333 SUCCESS**。AFZ19宣言の公理依存は全て標準 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更AFZ warning/error 0/0。独立MCP completion receipt `chatgpt-ci-receipt/PR Lean Fast Check` はSUCCESS。
- 最終source HEADとsquash SHAのGit treeは `a28fd9dc5d5361ea09e3daff6419d9801d149c5f` で一致。従来のAFY以前のソース、形式証明記録は保持。

### 未解決obstruction・次段AGA（仮称）

AFZは本来のFF受信器について保守的な有理包含を無条件に構成したが、区間中心は0で非零符号を判別できない。次は真正Perron/transfer/FFの有理値を中心に持つ**非自明かつ証明付きの区間認証**と、局所変動誤差・二閾値殻条件の接続が必要。体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。

---

## 検証済み定理 — AFY（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAP文書ミラー。AFX定理 #6337、正本文書 #6338、mainミラー #6339 の全件MERGEDを継承し、[AFY定理PR #6340](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6340) を **MERGED**。最終exact-source HEAD `8f9c9451e560ccca72d174ce77ca56fc75a07201`、定理squash SHA `0851bb926b0a8b138ba6df4d780a0766866b5607`。真正SU(2) Wilson/正規化Haar・AFQ24先着中心Borelセル・AFT固定有理重み・元のPerron/transfer/FF物理受信器を不変とし、代理量や新しい物理仮定は導入しない。

### 真正24中心の文字誤差ゼロ・元の物理受信器積評価

- **実際の中心積の鋭い有理証明書**：AFXが元Wilson四文字に対して証明した真の有理値 `qφ(j,i)=φ_j(g_i)` を使い、元FF受信器 `F_e(a,g_i)` のAFV認証有理中点 `qF(a,i)` と認証半幅 `εF(a,i)` から、各元境界サンプル `a∈c.s`、四モードj、真正SU(2)24中心iに対して `|F_e(a,g_i) φ_j(g_i) − qF(a,i) qφ(j,i)| ≤ |qφ(j,i)| εF(a,i)` をLean4で形式証明した。文字側の誤差は厳密0であり、元の受信器区間包含のみが外部証明書入力となる。
- **既存AFV乗算との型付き厳密一致**：元の `AFV_ballMul` が作る積の有理sampleは `qF*qφ`、errorは **厳密に** `|qφ| εF` に等しいことを定理化。AFVの一般誤差項から未検証のcharacter誤差を単に捨てたのではなく、AFX singletonによるzero errorを用いて具体的に評価した。
- **元AFT 24中心係数誤差への直接接続**：元AFT証明書の `coefficientSample` と `coefficientSampleError` に対する等式 `E_{a,j}=∑_{i=0}^{23}|qφ(j,i)|εF(a,i)≤∑_{i=0}^{23}εF(a,i)` をLean4で証明。後半の不等式は元ACK四文字の無条件 `|φ_j(g)|≤1` に由来する。元AFUの中心化Haar誤差評価・AFJ係数・AFI係数分散証明書への既存経路を保持した。

### exact-source Lean4 CI・公理監査・source対応

- AFY新規Leanファイル `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExact24CenterProductErrorV5_PZ37AFY.lean` のみ（326行・14件の `#print axioms`）。既存Leanやworkflow、root、物理測度を変更しない。固定Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。
- [最新exact-source CI #41928091102](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41928091102) は **11,332 / 11,332 SUCCESS**。Lean診断アーティファクトを独立取得し、新規AFY14宣言すべての公理依存が標準 `propext`・`Classical.choice`・`Quot.sound` のみであること、`sorry`・`admit`・追加`axiom`・`constant` 0、変更AFY warning/error 0/0を確認。独立MCP completion receiptは `chatgpt-ci-receipt/PR Lean Fast Check` = SUCCESS。旧Leanファイルに存在する既存警告は新規AFYのものではない。
- PR source HEAD・GitHub test-merge `75a00168b21d8348c70a4e436325f0d0dc16cdec`・squash SHAで新規AFYファイルのGit blob SHA `ad49cbe6c929e7efd95e6c78607bc25083de836b` は完全一致。source→test-mergeはファイル差分なし。正本のAFX基点からの追加差分は新規AFY Leanファイル1件のみ。

### 残存obstruction・次段AFZ

AFYは真正24中心での文字側の有限誤差を完全に除去したが、元Perron/transfer/FF受信器の**具体的な数値的有理区間包含証明**は依然未取得。AFG真正二閾値の非空符号殻も未証明。次段AFZでは、真正受信器について有限有理区間の検査可能な生成・包含条件、局所振動幅とAFU中心化Haar誤差への接続を研究する。体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。

---

## 検証済み定理 — AFX（2026-11-05 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAP文書ミラー。AFW定理 #6334、正本文書 #6335、mainミラー #6336までの全件MERGEDを継承し、[AFX定理PR #6337](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6337) は **MERGED**。定理squash SHAは`a0f626cd2e5e4a0ac46f9b33de185df28419b3e5`。真正SU(2) Wilson・元の正規化compact Haar／境界pair-Haar・Perron/transfer・符号付きFF受信器・AFQ真正24先着中心Borelセル・AFT固定有理重みを保持し、代理群・代理測度・追加の物理仮定を導入しない。

### 真正24中心の四成分Wilson文字に対する厳密有理値

- **元の実4座標との直接対応**：PZ35Bの真正SU(2)Quaternion元とPZ35D2の真正複素行列trace・ADRの元2×2行列再構成を使い、元ACKの四成分Wilson文字 `φ_j(g)` は、元の実4座標 `(x₀,x₁,x₂,x₃)` に対し**`(φ₀,φ₁,φ₂,φ₃)=(x₀,-x₂,-x₁,-x₃)`**とLean4で証明。符号とindexの対応を元のPauli行列の定義から直接導出し、任意の抽象同型や未証明の座標選択に依存しない。
- **真正24中心の固定有理テーブル**：AFQの元24中心は、ADSで構成した元のSU(2)への真正逆写像を使った座標軸8点＋半対角16点である。各中心の各文字は、軸では `-1,0,1`、半対角では `-1/2,1/2` の固定有理値となる。具体的な `Fin 4×Fin 24→ℚ` テーブル `p4Q2PZ37AFX_exactRationalCharacter` と全indexでの真正値との等式をLean4で形式証明した。数値積分、元Haar質量計算、FF受信器測定に置き換えたものではない。
- **文字区間の誤差ゼロ**：元AFVの型付き `verifiedInterval` で上下端点を同一の真の有理文字値に置き、`intervalToBall` の文字誤差が**厳密0**となることを証明した。AFWの全球的で保守的な `[-1,1]` 区間の幅1から、元24中心に限った有理singletonへ真正の意味で厳密化した。
- **物理証明書への型付き接続**：外部入力は依然として、AFG境界サンプルの各点と真正SU(2)24中心における元FF/Perron/transfer受信器の有理区間包含証明だけ。文字側の入力をAFX固定表から作り、元のAFV `originalFiniteIntervalInput` に接続し、AFT受信器積分証明書・AFI係数／分散証明書へ移送。AFUのHaar質量保存・中心化誤差評価も既存の型付き経路のまま使用できる。FF受信器の具体的有理数値自体を認証したとの主張ではない。

### exact-source Lean4 CI・公理監査・Git tree

- 新規Leanは `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExact24CenterFourModeV5_PZ37AFX.lean` のみ（281行、11件の `#print axioms`）。既存Lean・公開root・CI workflows・元物理測度・pinは変更なし。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。
- 初回[CI #41922258657](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41922258657)は失敗。その後の修正で[CI #41923287180](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41923287180)がSUCCESSとなり、さらに未実行戦術の削除後に最終exact-source HEAD `1fbd329a8aeca4daf1bfbf922d6fa60c484630f7` で[CI #41924187506](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41924187506)が **11,331/11,331 SUCCESS**。公理依存11件はすべて標準 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorry`・`admit`・追加`axiom`・`constant` 0、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- 最終source HEAD、test-merge `5453fa897fd6d11d850d37def919be0a78ea185e`、squash `a0f626cd2e5e4a0ac46f9b33de185df28419b3e5` のGit treeは `e312a4cfb168859127fcbb2c4938d5561c13eb14` で完全一致。

### 残存obstruction・次段AFY

真の24中心でのQuaternion四文字は有理値として厳密確定したが、元FF受信器の具体的な有理区間包含、独立したPerron/transfer数値認証、真正二閾値の非空符号殻は未確定。次段AFYでは、真正物理FF受信器の数値区間認証を検査可能な有限入力に落とし、中心での実際の数値評価と局所振動誤差の接続を進める。体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。

---

## 検証済み定理 — AFW（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラー。AFVの定理PR #6331、正本文書 #6332、mainミラー #6333 は全件MERGED。[AFW定理PR #6334](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6334) も **MERGED**。定理squash SHA `1922810011e6940a52bd6566da4b0bbbce90da4b`。真正SU(2) Wilson/Haar・元のAFQ 24先着中心Borelセル・AFT固定有理重み・Perron/transfer/符号付きFF受信器・AFM→AFJ→AFI型付き接続を不変更で継承する。

### 元の真正Wilson四成分文字の無条件有理区間

- **既証明ACKの平方和から導く真の境界**：真正SU(2)上の元Quaternion変換Wilson四文字 `φ_j(g)` について、既証明の等式 `∑_{j:Fin 4} φ_j(g)^2=1` と各平方の非負性から、任意の `g∈SU(2)`・`j∈Fin 4` で `φ_j(g)^2≤1`、`-1≤φ_j(g)≤1`、`|φ_j(g)|≤1` をLean4で無条件に形式証明。元Wilson文字そのものを使い、代理分布や追加物理仮定を導入しない。
- **文字の外部区間入力を消去**：具体的な有理端点 `-1,1∈ℚ` と、上の真正値包含証明からAFVの `verifiedInterval` を各元24中心 `c_i` に自動構成。AFVの有理区間中心は厳密に `0`、半幅誤差は厳密に `1`。これは全域的で保守的な包囲であり、真の24中心における四文字の具体値を数値評価したものではない。
- **真のFF受信器だけを外部証明書入力として残す**：元AFG有限境界サンプル `c.s` の各点と元24個のSU(2)中心における `F_e(a,c_i)` の有理区間包含だけを要求する新構造を追加。文字側はACKから導出し、AFVの元 `originalFiniteIntervalInput` へ型付き移送する。AFVの区間平方・積演算を使ってAFTの真正受信器標本、元AFM→AFJ→AFI係数・分散証明書に接続する。
- **AFU中心化誤差への条件付き直結**：元の四成分係数・Haar平均・二次Haarモーメントについて、AFUの中心化Haar質量誤差評価を、新しい「受信器区間のみ」入力に直接移送。定数モード誤差消去は元Haarの確定した24セル質量保存則に由来する。四文字の区間幅1は保守的であり、実効的係数精度の改善や新しい非零物理標本を主張しない。

### exact-source Lean4 CI・公理監査・Git tree

- 新規Leanは `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAutoFourModeIntervalsV5_PZ37AFW.lean` のみ（239行）。既存Lean、root、元物理、CI workflowsは不変更。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。
- 初回CI [#41912670809](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41912670809) は、有理端点 `-1,1:ℚ` から実数型へのキャスト簡約と有理中央値 `0` の `rfl` に失敗。新規Lean全文・ACK四成分平方和・AFV有理区間構造・AFUの係数/平均/二次モーメント依存型を照合し、`simpa` と `norm_num` で修正。定理文や外部仮定の弱化なし。
- 最終exact-source HEAD `cf4bdff83fcc2637e252513408457a5a7bb7b7df` の[CI #41913764357](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41913764357) は **11,330/11,330 SUCCESS**。新規13件 `#print axioms` はすべて `propext`・`Classical.choice`・`Quot.sound` のみ、`sorry`・`admit`・追加 `axiom`・`constant` 0、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- source HEAD、test-merge `53b38623d95b945131762caa2bc495cede162c5e`、定理squash `1922810011e6940a52bd6566da4b0bbbce90da4b` のGit treeは `7c5734209c32198b34334398615e3743f6a2ce99` で完全一致。

### 残存obstruction・次段AFX

AFWの文字区間 `[-1,1]` は無条件だが粗く、四成分積の標本はゼロ中心で物理的な数値閾値を構成していない。次段AFXでは真正24中心の四文字の具体有理値とその型付き証明書を元のSU(2)↔S³座標から導出し、AFVの積区間を実効的に縮小する。元FF/Perron/transfer受信器の具体数値包囲、真正二閾値の非空符号殻、体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き未証明。

---

## 検証済み定理 — AFV（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAP文書ミラー。AFU定理 #6328・正本文書 #6329・main文書 #6330 の全件MERGEDを継承し、[AFV定理PR #6331](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6331) は **MERGED**。定理squash SHA `e62fc7cc6a451cc84d4f4a82e8678c6a64036c2b`。元の真正SU(2) Wilson/Haar・24個の先着中心Borelセル・固定重み1/24・Perron/transfer/FF受信器・元AFM→AFJ→AFI型付き接続は不変更。

### 原FF受信器の証明付き有理区間演算

- **真正値の有理区間入力**：実数 `x` と有理端点 `l,u∈ℚ` に対し、実際の包含証明 `(l:ℝ)≤x≤(u:ℝ)` を要求する構造を導入。証明を伴う場合だけ、具体的有理中心 `q=(l+u)/2` と実誤差 `ε=(u−l)/2≥0` を作り、`|x−q|≤ε` をLean4で証明。端点の順序も包含証明から導く。上下端点は有理計算できるが、真正元FF数値に対する包含証明を自動生成したという意味ではない。
- **元物理量の二乗・積を区間演算で保証**：`|x−q_x|≤ε_x` なら `|x²−q_x²|≤ε_x(2|q_x|+ε_x)`。また `|y−q_y|≤ε_y` なら `|xy−q_xq_y|≤ε_x(|q_y|+ε_y)+|q_x|ε_y` をLean4で証明。数値解析上の単純な未検証浮動小数点操作ではなく、実数の不等式として確定。
- **有限・真正24中心への型付き適用**：元のAFG有限境界サンプル集合 `c.s` の各点 `a` と元のAFQ真正24中心 `c_i` で、実際の元FF受信器 `F_e(a,c_i)` の包含を要求。Wilson四成分文字 `φ_j(c_i)` は境界に依存しない別の区間証明書として一度だけ要求する。平方標本 `F²` と四成分積 `Fφ_j` は上の区間代数から構成し、独立の平方値・積値の数値観測を新たに仮定しない。
- **AFT/AFUへの接続**：実際の区間データから `p4Q2PZ37AFT_original24CellVerifiedSamples` を作り、元の `p4Q2PZ37AFT_toOriginalReceiverQuadrature`・`toOriginalCoefficientVarianceCertificate` に接続。したがって既証明AFUのHaar質量保存・任意定数モード中心化誤差評価にも型付きで利用可能。元の物理受信器が定めた実数値・元Haar・物理閾値条件を置換しない。
- **真正符号の条件付き判定**：端点の有理不等式 `0<l` または `u<0` と真正値包含が証明されれば、元のSU(2)中心における物理FF受信器値がそれぞれ厳密正または負であることをLean4で証明。具体的な二符号点の存在・元殻の非空性は主張しない。

### exact-source Lean4 CI・公理監査・Git tree

- 新規Leanのみ：`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalVerifiedRationalIntervalReceiverV5_PZ37AFV.lean`（388行）。既存Lean・root・CI workflows・元物理測度は変更なし。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 不変。
- exact-source HEAD `c804f53d97c503d3b26ad961bba7231dd32175c7` の[CI #41906037567](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41906037567) は **Lean 11,329/11,329 SUCCESS**。新規11件 `#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorry`・`admit`・追加`axiom`・`constant` 0、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- source HEAD、test-merge `31d3c02986e10d48f474049f9c2f8d21e6c26332`、定理squash `e62fc7cc6a451cc84d4f4a82e8678c6a64036c2b` のGit treeは `4544ff0338e9bdb55c558d95b0ec3cf038eeacf4` で完全一致。

### 残存obstruction・次段AFW

AFVは**与えられた真正区間包含証明を検査して伝播する**定理であり、元FF受信器の具体的有理上下限の区間演算器を実行・認証したという主張ではない。次段AFWでは真正24中心の四文字の実効的な有理値検証、元Perron/transfer/FF受信器の実際の数値区間包囲、独立の有限証明書入力の充足を優先する。二閾値非空殻、体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き未証明。

---

## 検証済み定理 — AFU（2026-11-05 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` はREADME・ROADMAPの文書ミラー。AFTまでの真正SU(2) Wilson・Perron/transfer・符号付きFF受信器・元の24個の先着中心Borelセル・正規化compact Haar・固定重み `1/24` を保持し、[AFU定理PR #6328](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6328) を **MERGED**。定理squash SHAは `d141c233c8aa969c95f5a4d97d5fd07db2374a8b`。既存Leanソース・外部仮定・Haar測度・toolchain pinsは不変更。

### 真正24セルHaar質量保存と中心化求積

- **元の真正24セル質量の厳密保存**：AFQ/AFJのBorelセル分割と元の正規化SU(2) Haar測度から、全24セル質量の総和 `∑ᵢ μ(Cᵢ)=1` をLean4で証明。AFR/AFTの文字通りの固定有理重み `wᵢ=1/24` も `∑ᵢ wᵢ=1`。従って `∑ᵢ(μ(Cᵢ)−wᵢ)=0`。測度・有限群・中心を代理に置換していない。
- **任意の有理定数モードに対する誤差消去**：AFTの証明済み個別誤差 `δ=13219/42744` を継承し、任意の有理標本表 `qᵢ` と任意の有理シフト `s` について `|∑ᵢ(μ(Cᵢ)−wᵢ)qᵢ| ≤ δ ∑ᵢ|qᵢ−s|` をLean4で証明。定数表 `qᵢ=s` に関してHaar質量重み誤差は**厳密に0**。従来のAFJ誤差と中心化誤差の最小値による、AFTより弱くならない区間も形式化。
- **真正FF受信器への型付き接続**：元のAFM→AFJ→AFI物理経路を変更せず、元のFourMode係数、Haar平均、Haar二次モーメントに、24セル中心化誤差と真正セル上の振動誤差から成る評価を接続。原物理標本の有理精度任意小の**存在**をAFNの有理数稠密性から構成するが、Classical.chooseによる非計算的選択であり、数値的区間評価の独立認証ではない。
- **数学的境界**：符号殻サンプル表 `c`、閾値条件 `0≤lo` 等の元の型付き証明書条件を保持する。具体的な非零FF数値標本、二閾値符号交差の存在、体積一様coercivity、物理Hamiltonianのspectral gap、連続体4D Yang–Mills質量ギャップは証明していない。

### exact-source Lean4検証・公理監査・Git tree一致

- 新規ファイルは `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCenteredHaarMassErrorV5_PZ37AFU.lean` のみ。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、公開root・既存Leanファイルは不変更。
- 初回CI #41878353128は `simp` の後に残った自己同一の有限和の等式が未解決で失敗。修正後CI #41897462557は全Leanビルド成功だが戦術結合子 `<;>` に非致命的warning 1件を検出。変更ファイル全文とAFT/AFJ/AFQの依存定義を確認し、通常の `simp`、続く `rfl` の2段階へ変更。定理文・仮定は弱めていない。
- 最終exact-source HEAD `dfe639cee4d39e89acce409f7db9c12e695fe323` の[CI #41898383151](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41898383151)は **Lean 11,328/11,328 SUCCESS**、新規13定理の `#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorry`・`admit`・追加 `axiom`・`constant` 0、変更Lean warning/error **0/0**。独立MCP completion receipt **SUCCESS**。
- exact-sourceとtest-merge `f477ffcec91404e1bb748d0093040ee4712e5ef5`、定理squash `d141c233c8aa969c95f5a4d97d5fd07db2374a8b` のGit treeは `962c845fd68211a7027057ebda8e35577a7fc8a7` で完全一致。

### 残存obstruction・次段AFV

中心化により定数モードのHaar重み誤差はゼロとなったが、実際のFF有理標本の独立かつ計算可能な区間認証、真正24セル質量の狭い実効区間、非空二符号閾値殻、体積一様coercivityと物理spectral gapはいずれも未解決。次段では有理標本表の有限認証と、真正S³/SU(2) Haar幾何による実効区間の更なる改善を検討する。

---

## 検証済み定理 — AFT（2026-11-04 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main`はREADME・ROADMAP文書ミラー。[AFT定理PR #6325](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6325)は**MERGED**。AFS #6322〜#6324のMERGEDと厳密な元SU(2) Wilson・Perron/transfer・FF受信器・正規化compact Haar・pair-Haar・元弦距離を継承し、新たな代理測度・物理仮定は導入しない。

### 真正Wilson二次モーメントの最適有理シフトと24セル証明書

- **Markovシフトの最適性**：元Haarで`∫χ dμ=0`、`∫χ² dμ=1/4`、元半径4/5球では`χ>17/25`。任意`c+17/25>0`に対する`(c²+1/4)/(c+17/25)²`の最小値が`625/1781`で、`c=25/68`により達成されることをLean4で証明。整数係数の真正物理文字の平方`Q=(68χ+25)²≥0`の元Haar期待値が`1781`、元球上で`Q≥3171961/625`であることを固定mathlibの実Markov不等式に接続し、**`m(4/5)≤625/1781<1250/3481`**を無条件に形式証明。
- **真正24セルへ移送**：ADMの同一元SU(2) Haar球の中心不変性、AFQの元24個の先着中心BorelセルとAFRの小球下界を用い、全`i`に対し**`1/160000≤μ(C_i)≤625/1781`**。元24セル、被覆半径`4/5`、測度は変更していない。
- **固定有理重みの厳密改善**：全セルで`w_i=1/24∈ℚ`を保持し、**`|μ(C_i)-1/24|≤13219/42744`**を証明。AFSの`26519/83544`より小さい。真正AFJの重み誤差汎関数もAFTがAFS以下であることを証明。
- **真正物理証明書への型付き直結**：元AFQの真の24中心と有理重みを固定し、真正受信器の中心値・二乗・四成分積について**実際に証明された数値有理標本と誤差のみに基づく**`p4Q2PZ37AFT_original24CellVerifiedSamples`を導入。AFMの真正Perron/transfer/FF envelope・弦距離slopeを経由してAFJ積分証明書・AFI係数／分散区間に接続。非零標本を許容するが、非零の数値標本がすでに実測・認証されたと主張しない。ゼロ標本の場合は重み誤差項がゼロなのでHaar区間改善だけでは物理的積分誤差が縮小しないことを明示。

### exact-source Lean4 CI・公理監査・source tree

- 新規Leanは`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOptimalMomentHaarV5_PZ37AFT.lean` **358行の1ファイル**のみ。既存Lean、pins、rootは不変更。Lean`v4.30.0-rc2`／mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。
- CI #41840825958の初回失敗は積分定数倍の簡約と構造体`center`への局所記法の捕獲、CI #41841772703の残余は`center`の旧参照1件。変更Lean全文・AFM/AFI/AFJ/AFQ/AFSの依存型を再照合し、積分の固定mathlib正規化`integral_const_mul`と`gridCenter`に修正。定理・仮定を弱めず解消。
- exact-source HEAD **`b936d3853e5961ee190c9a56946282138629f8dc`**、[CI #41842798348](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41842798348)は**11,327/11,327 SUCCESS**、新規`#print axioms` **15件**すべて標準`propext`・`Classical.choice`・`Quot.sound`のみ、`sorry`・`admit` 0、変更ファイルにwarning/errorなし、独立MCP CI completion receipt **SUCCESS**。
- source HEAD、test-merge`03ab2610cbadbd255c8c47a3c9fab95ec03bdee3`、定理squash **`0758c888f7e53a9a7f599742c9be5697562b3371`**のGit treeはすべて **`aba732d0c23bce9c7e69151b7002fdf753f17c8e`**で完全一致。

### 残存obstruction・次段

これは二次モーメントに基づくMarkov型上界の最適化であり、各セルの実際のHaar質量の計算でも、真正FF受信器の有理標本の数値認証でもない。真正二閾値符号交差、体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。次段は元の物理受信器に対する有理標本の独立認証、または元Haar高次モーメント／真正幾何を用いたさらに有効な区間を検討する。

---

## 検証済み定理 — AFS（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main`はREADME・ROADMAPの文書ミラー。AFR定理 #6319、正本文書 #6320、main文書 #6321 の全件MERGEDを継承し、[AFS定理PR #6322](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6322) を**MERGED**。定理squash SHAは`ae6a40d78bfdc10d4207aa33c967a916e208563f`。真正SU(2) Wilson相互作用、ZW中心化Gauss-law源、Perron/transfer、符号付きFF受信器、正規化compact Haar、境界pair-Haar、元距離`d_J,D_H`、公開root、固定Lean/mathlibは変更していない。

### 元Wilson Haar二次モーメントとMarkovによる24セル質量区間の厳密改善

- **物理量・測度を置換しないモーメント証明**：既存ACKの真正Quaternion四文字Gramから、元の`χ(g)=1−E(g)`について、元の正規化SU(2) Haar上で`∫χ dμ=0`と`∫χ² dμ=1/4`を継承する。固定多項式`P(g)=(χ(g)+1/2)²≥0`は連続・可積分で、`∫P dμ=1/2`。仮定・代理Haar・新規元群なし。
- **元半径4/5球での真正不等式**：ADKのWilson校正`d_J(1,g)²=2E(g)`から`g∈B_J(1,4/5) ⇒ χ(g)>17/25`。したがって`P(g)>(59/50)²=3481/2500`。固定mathlibの`mul_meas_ge_le_integral_of_nonneg`（実数版Markov）から**`m(4/5)≤1250/3481<1/2`**をLean4で無条件に証明。
- **真正24 Borelセルへの移送**：AFQの先着中心セルは元の`B_J(c_i,4/5)`内。ADMの真正Haar球中心不変性とAFRの各セル内部`B_J(c_i,1/5)`の正のHaar下界から、**全24セルについて`1/160000≤Measure.real μ(C_i)≤1250/3481`**を形式証明。実際のセル質量の数値積分値を求めたものではない。
- **固定有理重みを保った誤差縮小**：AFRの実効的な`w_i=1/24∈ℚ`（全て正、合計1）を変更せず、実際のセルとの誤差上界を**`|μ(C_i)−1/24|≤26519/83544`**と認証。AFRの`11/24`に比べて厳しく、AFQの非計算的`1/64`の小さい形式的近似誤差とは区別する。元のAFJ `originalHaarCells`に改善済みの型付き証明書を格納。実際のFFサンプル値・非空二符号閾値・新しい物理解は主張しない。

### exact-source Lean4 CI・公理監査・Git tree一致

- 新規`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2Original24CellMomentMarkovHaarV5_PZ37AFS.lean`1ファイルのみ（新規13件`#print axioms`）。既存Leanや元物理模型・workflows・公開rootを変更せず、Lean`v4.30.0-rc2`／mathlib`5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。
- 初回[CI #41835136403](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41835136403)は積分の加法性`integral_add`を点ごとの多項式に対して直接`rw`した際、Lean elaboratorの関数和と被積分関数の式の一致に失敗した。変更Lean全文とACK/PZ35Cの元Haar二次モーメント、ADK/AFRの依存型、固定mathlib Bochner積分・Markov補題を再照合し、中間積分加法等式を型付きで明示する形に修正。定理・仮定の弱化なし。
- 最終exact-source HEAD`25ece6e4494b0a48ff5ae919f78e141350b5c9e6`の[CI #41836184579](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41836184579)は**11,326/11,326 SUCCESS**、13件の公理依存は標準`propext`、`Classical.choice`、`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- source HEAD`25ece6e4494b0a48ff5ae919f78e141350b5c9e6`、test-merge`9fa606be0d1cbbcb6e6ad7fdd0290387054f3679`、定理squash`ae6a40d78bfdc10d4207aa33c967a916e208563f`のGit treeは**`9d609048dfd57b3485b1ef5713652616052bfd67`**で完全一致。

### 残存obstruction・次段AFT

AFSで真のHaar上の二次モーメントから上界が約0.359へ改善したが、実際の24セル質量の狭い有理区間計算、重み`1/24`に対する精度`1/64`程度の実効的認証、元FF受信器中心値の評価、真正二閾値符号交差、体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは**未証明**。次段AFTは同じHaar二次モーメントの最適有理シフトと、元のAFM物理受信器証明書への改善区間移送を検討する。

---

## 検証済み定理 — AFR（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main`は文書ミラー。AFQ定理 #6316 と文書 #6317/#6318 の全件MERGEDを継承し、[AFR定理PR #6319](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6319) を **MERGED**。定理squash SHA `94f3ce7d6583a89a96a2ea358081f1f9733f5d03`。元Wilson SU(2)、中心化Gauss-law物理源、Perron/transfer、符号付きFF受信器、真正正規化SU(2) Haarとboundary pair-Haar、弦距離`d_J`、公開root・Lean/mathlib pinsを変更しない。

### 真正24頂点の整数距離証明・全セルHaar質量の実効的有理上下界

- **座標軸8点＋符号付き半対角16点を整数に正規化**：AFQの真のSU(2)↔S³等距離による24個の元行列中心を使用。4座標を2倍した`ℤ`ベクトル`vertexZ`で、全相異なる頂点の整数内積`Σ vertexZ_i(k)·vertexZ_j(k)≤2`を有限場合分けで形式証明し、元弦距離で`1≤d_J(c_i,c_j)`を導出。代理群・新Haar分布なし。
- **各セルの真正内部球**：AFNの先着中心24個のBorelセル`C_i`は、その中心の`B_J(c_i,1/5)`を含み、半径`4/5`の元のAFQ球に含まれる。この内包は`1/5+4/5=1`と厳密な開球不等式、元ADK三角不等式、上述の1-分離から証明。各セルが空でなく正のHaar質量を持つことも従う。
- **真のHaar質量へのリテラル有理区間**：既存ADZ/AECの真正半径`1/5`球質量下界`(1/20)^4=1/160000`、ADNの半径`4/5`球上界`1/2`から全24セルについて **`1/160000≤Measure.real μ(C_i)≤1/2`** を形式証明。セル積分の浮動小数点計算や一様セル質量の仮定ではない。
- **元Haar球と固定重み**：実際の24中心が元の半径`4/5`有限ネットであることからADPの有限net質量定理により`m(4/5)≥1/24`。固定有理重み`w_i=1/24`は全て正で、和は厳密に1。真の24セルへの誤差`|μ(C_i)−1/24|≤11/24`をLean4で証明し、AFJの元の真正HaarCellsへ格納する。誤差11/24は**AFQの非計算的1/64より数値的に粗い**が、固定され独立に検査可能な有理数である。
- **元物理のauthority境界**：AFRは既存AFQのAFM→AFI真正FF受信器証明書を改変せず、新たな原物理受信器標本の数値測定や閾値交差を導入しない。セル質量の区間証明は、元物理Hamiltonianのspectral gapや体積一様coercivityを直接証明するものではない。

### CI検証・Lean4記法修正・公理監査

- 新規`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2Original24CellEffectiveHaarV5_PZ37AFR.lean`1ファイルのみ。既存Lean、project root、workflow、測度、pin不変。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。
- 初期CIでは有限Bool/Fin場合分けの重い一括`decide`、`simp`後の不要`split_ifs`、数値仮定の未具体化、`No goals to be solved`、最後に`hij : True ⊢ False`へ無効な矛盾証明を使う問題を発見。**新規Lean全文、import、AFQ/AFN/ADT/ADK/ADP/ADZ/AEC/ADNの依存シグネチャと固定mathlibの`fin_cases`・`norm_num`記法を再確認**し、座標軸同士の整数比較は`norm_num [...] at *`で仮定と目標を同時に正規化。原定理の仮定は弱めていない。
- 最終exact-source HEAD `b3e98c04bc85b10e61c0a13e268c73d4ca2751a1` の [CI #41831372711](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41831372711) は**11,325/11,325 SUCCESS**、新規14件`#print axioms`監査は標準`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- source HEAD `b3e98c04bc85b10e61c0a13e268c73d4ca2751a1`、test-merge `a585c36690193c9264c88ab6c318b283f29fc8ee`、squash `94f3ce7d6583a89a96a2ea358081f1f9733f5d03` のGit treeは**`959802c17bc86b044582eeb9011ed61c37b42c10`**で完全一致。

### 残存obstruction・次段AFS

セル毎の実効的な正の有理質量区間と、有限24中心の一様球mass floorは確定した。一方、狭いセル質量の計算可能な区間（例えば1/64精度）、実際の元FF中心値の狭い有理包囲、真正二閾値の非空符号殻、体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは**未証明**。次段AFSは、原Haar・球面の対称性を証明済み等長変換に限定して使い、各セルの質量区間の実効的精度向上に進む。

---

## 検証済み定理 — AFQ（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。AFPまでの全PR #6313–#6315 をMERGEDとして継承し、[AFQ定理PR #6316](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6316) も **MERGED**。定理squash SHA `2915464ade5ab17e44a927d5ac6edd2fc2e7d351`。元の真正SU(2)相互作用Wilson、中心化Gauss-law物理源、真正Perron真空・transfer、符号付きFF受信器、正規化compact Haar・元境界pair-Haar、元弦距離 `d_J` と全リンク距離 `D_H`、公開root・固定Lean/mathlib pinは変更しない。

### 真正SU(2)≃S³の明示24中心・開半径4/5被覆

- **実4次元の真正格子**：ADR/ADSで既証明の元SU(2)↔実S³全単射、ADTで既証明の元Wilson弦距離との等長性を採用する。元の`E4=EuclideanSpace ℝ (Fin 4)` の符号付き4本の座標軸8点と、各座標が`±1/2`の半対角16点を、`Sum (Fin 4 × Bool) (Fin 4 → Bool)`により厳密に24個列挙。ADSの逆写像で全てを元の真正SU(2)行列へ移し、代理群・コンパクト性での未指定中心選択は行わない。
- **新しい無条件定量被覆**：全ての`x∈S³`について、`max_j |x_j|≥7/10`、または`∑_j |x_j|≥7/5`をLean4で証明。対応する軸点／符号付き半対角点との内積は少なくとも`7/10`。元ADTの等距離から、全ての真正`g∈SU(2)`について**`∃i∈Fin 24, d_J(c_i,g)^2≤3/5<(4/5)^2`**、したがって**24個の開球`B_J(c_i,4/5)`が元SU(2)全体を覆う**。AFPの閉半径1、実証明書半径9/8から真に縮小する。
- **真正Haar Borelセル**：AFNの先着中心規則で24個の可測セルに一意分割し、`C_i⊆B_J(c_i,4/5)`を同じ元正規化Haarで証明。各真のセル質量はAFNの有理数稠密性により誤差`≤1/64`の有理包囲を**非計算的に選択**できる。これは**算定済みセルHaar質量、固定された具体的有理重み、有理重みの総和1、実行可能な区間求積を証明したという意味ではない**。AFPの具体的`1/8±3/8`より形式的な近似誤差は狭いが、数値証明書の実効性として優位とは主張しない。
- **元FF受信器との厳密接続**：真正`F_z(g)`、`F_z(g)^2`、4個の`F_z(g)φ_j(g)`の有理中心標本を文字どおり`0∈ℚ`とし、同じ元FF BCFノルム`M_FF(H,e)`、その二乗、`M_FF(H,e)`を真の誤差上界として保持。AFGの独立境界shell sample table `c`と`0≤θ_lo`を与える場合、AFM→AFL→AFK→AFJ→AFIの既存係数・分散証明書に型付き接続する。真の厳密二閾値符号交差の実例は構成していない。

### exact-source Lean CI・公理監査・source/test-merge/squash一致

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2Original24CellSphereGridV5_PZ37AFQ.lean` **1ファイル・430追加行**。他のLeanファイル・元物理モデル・workflowは変更なし。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- 初回 [CI #41812088785](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41812088785) はLean 11,324/11,324 SUCCESSだが新規内積補題に`simp`の未使用引数warningが1件。定理全文・既存ADR/ADS/ADT/AFN/AFPソースを照合して不要引数のみを除去。最終source HEAD `5eeab182fad6d3ad2432953617d49ef9352bb4bb` の [exact-source CI #41812851027](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41812851027) は**11,324/11,324 SUCCESS**。直接`#print axioms`監査12件（残り2件の補題は監査済み証明から参照）、依存公理は`propext`、`Classical.choice`、`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。過去の変更外ファイルの非致命的警告は区別する。
- source `5eeab182fad6d3ad2432953617d49ef9352bb4bb`、test-merge `6549b9fbcfe9fcbba739151afca668f484bbea2c`、squash `2915464ade5ab17e44a927d5ac6edd2fc2e7d351` の Git tree は**`23d87164474ffc63cbc0b9a80fb0bcb1e221262c`**で完全一致。

### 未解決obstruction・次段AFR

真正SU(2)24中心の開半径4/5被覆はLean4で確定。一方、24セルの**実際の**Haar質量を計算するアルゴリズムと具体的な数値区間、各セルの非空性・正質量、FF中心標本のノルムに比べ狭い数値包囲、具体的二閾値符号交差、H一様coercivity、物理Hamiltonianのspectral gap、連続体4D Yang–Mills質量ギャップは未証明。次段AFRでは24セルの実効的なHaar質量上界・下界と計算可能な有理重みを優先し、非計算的な有理近似を数値認証と混同しない。

---

## 検証済み定理 — AFP（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFOの定理PR #6310・正本文書 #6311・main文書 #6312 の全件MERGEDを継承し、AFP新規定理PR [#6313](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6313) は **MERGED**。定理squash SHA `8f5860a0cfbffd0236e646467a514673cac4f2e5`。元の真正SU(2) Wilson模型、ZW中心化Gauss-law物理源、Perron/transfer、元符号付きFF受信器、正規化compact Haarとboundary pair-Haar、元弦距離`d_J`・全リンク距離`D_H`、FC obstruction・公開root・Lean/mathlib pinを変更しない。

### 元SU(2) Quaternion 8中心の半径1被覆・実際の8セルHaar証明書

- **既存ABVの真正cap被覆とADKの真正Wilson弦距離の合成**：ABVで公理追加なしに証明された、真正Quaternion4元と中心符号2元による**8通りの真正SU(2)左平行移動**の低エネルギーcap被覆を利用。各元`g∈SU(2)`に、`E(a_i g)≤1/2`の元Quaternion変換`a_i`がある。ADKの元物理Wilson校正`d_J(a_i^{-1},g)^2=2E(a_i g)`と距離非負から、厳密に **`∀g, ∃i∈Fin 8, d_J(c_i,g)≤1`** をLean4で証明。中心`c_i=a_i^{-1}`は新規代理群ではなく元のSU(2)行列であり、コンパクト性による未指定ネット選択は不要。8個はインデックス付き中心で、全ての相異性を別個に宣言していない。
- **任意半径`r>1`で元の8中心開球被覆**：上の定量半径1を使い`∀r>1,∀g,∃i∈Fin 8, g∈B_J(c_i,r)`。AFNの既存「最初の該当中心」ルールから実際の8個のBorelセル`C_i(r)`を構成し、一意所属、全群被覆、`C_i(r)⊆B_J(c_i,r)`を証明。AFOの2中心半径`3/2`から幾何半径を明示的に縮小できる。
- **真正Haarの保守的・具体的有理重み**：`1<r`かつ`r²≤2`では、各真正セルは元のADN半径`r`のHaar球に含まれ、`0≤μ(C_i(r))≤1/2`を証明。具体的に全8セルの有理重みを`w_i=1/8`、有理重み総和を厳密に1とし、**`|μ(C_i(r))-1/8|≤3/8`** をLean4で証明。セルの質量が実際に互いに等しいという未証明の対称性仮定は一切導入しない。質量誤差`3/8`はAFOの`3/16`より広く、改善は中心を指定した被覆半径の縮小である。
- **真正元FF受信器の8セル型付き有限有理証明書**：実際の有理半径`r=9/8`で上記8セル・全重み`1/8`をAFJの元HaarCellsへ接続。AFMで同定した真正符号付きWilson/Perron `F_z(g)`、`F_z(g)^2`、四つの真のQuaternion文字による`F_z(g)φ_j(g)`の中心有理標本を`0∈ℚ`に固定し、誤差を元FF BCFの真のノルム`M_{FF}(H,e)`、`M_{FF}(H,e)^2`、`M_{FF}(H,e)`で保証。独立の元AFG境界標本表`c`と`0≤θ_lo`が与えられる場合にのみ、AFM→AFL→AFK→AFJ→AFIの既存係数/分散証明書へ型付き移送する。実際の二閾値符号交差中心は証明していない。

### exact-source CI・公理監査・Git tree一致

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalEightQuaternionChordalCellV5_PZ37AFP.lean` **1ファイル・344追加行、公開11定理・11件の`#print axioms`**。既存Lean・元物理模型・Haar則・workflows・公開rootは不変。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` に固定。
- 初回exact-source [CI #41808197221](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41808197221)では、真正Haarセルの有理重み `1/8 : ℚ` と実数の等式をLeanが`change`で自動正規化できないエラー1件を検出。ソース全文とABV/ADK/AFN/ADN/AFOの型を確認し、`(p4Q2PZ37AFP_eightRationalWeight i : ℝ)=(1/8 : ℝ)`を明示証明して修正。最終exact-source HEAD `b1f593172faed92d09d61305573048d5be1a5bb0` の [CI #41809074860](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41809074860) は **11,323/11,323 SUCCESS**。11定理公理依存は`propext`、`Classical.choice`、`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- source HEAD `b1f593172faed92d09d61305573048d5be1a5bb0`、test-merge `7e3e6038bb4b1a562c3d67af3e3e8956f6a8f249`、定理squash `8f5860a0cfbffd0236e646467a514673cac4f2e5` のGit treeは **`cd3518cf41b8fdc2688461bb19d55fdd11490181`** で完全一致。

### 未解決obstruction・次段AFQ

AFPは指定された真正Quaternion8中心で半径1被覆を無条件に証明し、実際の有理半径9/8で元Haar・元FFの有限8セル証明書を具体化した。一方、真正セルHaar質量の均等性・精密有理区間、より高密度な真正S³格子による半径`<1`の実効的被覆、元FF中心値の狭い有理評価、具体的二閾値非空符号殻、体積一様coercivity、物理Hamiltonianのspectral gap、連続体4D Yang–Mills質量ギャップは未証明。次段AFQでは、原SU(2)≃S³の実4座標を用いた細分格子と狭い真正Haarセル質量区間を重点的に形式化する。

---

## 検証済み定理 — AFO（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFN定理PR #6307・正本文書 #6308・mainミラー #6309 の全件MERGEDを継承し、AFO定理PR [#6310](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6310) は **MERGED**。定理squash SHA `69694abf4a1bfdef85588f1a20b95f783ac59753`。既存の真正SU(2)相互作用Wilson、中心化Gauss-law物理源、Perron真空・transfer、真正符号付きFF受信器、元正規化Haarと境界pair-Haar `ν_H`、`d_J`・`D_H`、FC obstruction、公開root・固定Lean/mathlibを変更しない。

### 真正SU(2) Haarの明示2セル・真正FF有理ゼロ標本証明書

- **非計算的な有限ネット選択を不要にした2セル**：元SU(2)の単位元 `1` と既存の真正中心反対元 `z=-1` を中心とする、半径 `3/2` の真正ADK弦距離球を用いる。ADNの既証明 `B_J(1,3/2) ∪ B_J(z,3/2)=SU(2)` から、`C₀=B_J(1,3/2)` と `C₁=SU(2)∖C₀` はBorel可測な重複のない完全分割であり、`C_i⊆B_J(g_i,3/2)` をLean4で証明。中心は元のSU(2)行列であり、代理群・有限置換Haarではない。
- **具体的有理Haar重みを厳密に認証**：ADOの真正元Haar半径評価 `1/2 ≤ μ(C₀) ≤ 7/8` と確定的な補集合恒等式 `μ(C₀)+μ(C₁)=1` を使用し、**`|μ(C₀)-11/16|≤3/16`、`|μ(C₁)-5/16|≤3/16`** を証明。重み `(11/16,5/16)` は固定された文字通りの有理数で、両方厳密に正、和が厳密に1。セル質量誤差も `3/16` に固定。AFNの`Classical.choose`による任意実数の有理近似ではなく、真正Haar幾何から具体的な区間認証済み数値を導く。
- **真正符号付きFF受信器の明示有理ゼロ標本**：`F_z(g)`、`F_z(g)^2`、`F_z(g)φ_j(g)` の2中心における有理候補をすべて `0` に固定。元FF有界連続関数の真のノルム `M_{FF}(H,e)` とAFLの真正四文字上界 `|φ_j|≤1` により、各中心の真の誤差を順に `M_{FF}(H,e)`、`M_{FF}(H,e)^2`、`M_{FF}(H,e)` で無条件に証明する。誤差係数は具体的数値に評価されておらず、真正物理受信器の体積依存ノルムのまま。
- **元AFM→AFL→AFK→AFJ→AFI証明書へ接続**：独立に与えられたAFG真正元境界標本表 `c` と `0≤θ_lo` の下で、半径 `3/2`、中心2個、有理Haar重み・誤差、元FF・FF²・FFφ_j有理ゼロ標本と真の物理誤差を備える `originalNumericOnlyCellSamples` を直接構成。さらに元の係数・分散有理区間証明書へ型付きに変換する。`c`やstrict二閾値の通過中心を構成したものではない。
- **精度の限界を明示**：これは**具体的有理データをもつ粗い認証済み2セル基準例**である。半径3/2、質量誤差3/16、ノルム大のゼロ標本誤差は、狭い厳密殻交差の成立や数値的な優位性を保証しない。半径を任意に縮小する実効的SU(2)≃S³格子、精密なHaar質量有理区間、受信器中心値の狭い数値区間、体積一様coercivity・物理Hamiltonian gap・連続体4D Yang–Mills質量ギャップは未証明。

### Lean4形式検証・公理監査・exact-source Git tree

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAntipodalTwoCellEffectiveHaarV5_PZ37AFO.lean` **1ファイル・349追加行、公開12定理・12件の `#print axioms`**。既存Lean、物理模型、測度・workflow、公開rootは不変。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を固定。
- 初回CI [#41803889688](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41803889688) で`Set.mem_union.mp`の補題名誤り、`Fin 2`正規化と`change`の定義同一性不一致、二乗絶対値の簡約証拠の指定を検出。全文とADN・ADO・AFM・固定mathlibの型を照合し修正。最終source HEAD `bf3b955f7d79c1ff8369144a3c5f76b912f98993` の [exact-source CI #41804745964](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41804745964) は **11,322/11,322 SUCCESS**。12定理の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- source `bf3b955f7d79c1ff8369144a3c5f76b912f98993`、test-merge `ba1dd8330de53984d142b676585fb2618a452de8`、squash `69694abf4a1bfdef85588f1a20b95f783ac59753` のGit treeは **`04287c1a375688df47fa10d01c9ad988a5ad3b7a`** で一致。

### 未解決obstruction・次段AFP

AFOで固定半径3/2の明示的な真正2セル・有理質量重み・真正FF有理ゼロ標本の型付き証明書は完成。次段AFPは、SU(2)≃S³上の**実効的なより細かい有限格子**、小半径Haarセルの具体的上下界、FF物理標本の狭い有理区間によって誤差予算を改善する。体積一様coercivity・物理Hamiltonian spectral gap・連続体4D Yang–Mills質量ギャップは未証明である。

---

## 検証済み定理 — AFN（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFM定理PR #6304・正本文書PR #6305・main文書ミラーPR #6306の全件MERGEDを継承し、AFN定理PR [#6307](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6307) は **MERGED**。定理squash SHA `0d1c0cf21d7ce0205c2b20f211f58ea48b3bfc7c`。既存の真正SU(2) Wilson相互作用、中心化Gauss-law物理源、Perron/transfer、元FF符号付き受信器、正規化SU(2) Haar、元境界pair-Haar `ν_H`、`d_J`・`D_H`、FC obstruction、公開root、固定Lean/mathlibは変更しない。

### 元SU(2)有限Borelセルの存在と真正Haar・FF有理誤差証明書

- **ADPの真正SU(2)有限ネットから厳密セルを構成**：任意の正半径 `r>0` でADPの真正SU(2)有限弦距離ネット `g_i` を使い、各 `g∈SU(2)` を、`d_J(g_i,g)<r` を満たす最初のインデックス `i` に割り当てる。`C_i=B_J(g_i,r) ∖ ⋃_{j<i}B_J(g_j,r)` と定義し、`C_i` のBorel可測性、一意所属、全体被覆、真正弦距離半径 `d_J(g,g_i)≤r` をLean4で証明。セルが空でないことや正質量を全セルで主張するものではない。
- **元の正規化Haar質量に任意精度の有理包囲が存在**：各真のセル質量 `μ_Haar(C_i)` について、任意の `ε_w>0` で `q_i∈ℚ` が存在し、`|Measure.real μ_Haar(C_i)−q_i|≤ε_w`。AFJの真正`originalHaarCells`構造に、重複のない実セル・可測性・真のHaar質量誤差証明を供給する。重みの選択は`Classical.choose`に依存し、実際の有理値・有理区間計算を実行したわけではない。
- **同じ真正FF受信器の中心有理近似を型付き証明**：任意の `ε_s>0` と有限中心について、元の `p4Q2PZ37ABZ_originalReceiverSection` による `F_z(g_i)`、`F_z(g_i)^2`、四つの真正Quaternion文字を掛けた `F_z(g_i) φ_j(g_i)` に、それぞれ絶対誤差 `≤ε_s` の有理近似が存在することを実数中の有理数稠密性から証明。中間ABZ transfer quotient `U` をFF受信器に置換せず、元の物理量と測度を保存する。
- **AFM→AFL→AFK→AFJ→AFI→AFHの元の型付き連鎖へ接続**：有限ネットから `originalNumericOnlyCellSamples` が存在し、そのセル半径が指定された真正 `r` に厳密一致することを示す。任意の既存AFG shell sample table `c` と `0≤θ_lo` を与えれば、元の係数・分散有理区間証明書が`Nonempty`となることを導く。ここで**AFG入力 `c` 自体の構成、二閾値で通過する中心の存在、真の殻正質量は証明していない**。
- **非計算的existenceと実効的numeric certificationの境界**：ADPの有限ネット存在と、`exists_rat_btwn`・`Classical.choose`による有理近似存在はLeanカーネルで検証した。しかし明示座標の有限ネット、セル質量の実数計算、具体的有理標本、セル数上界、非空二符号殻、有用な誤差余裕は未認証。これらを実測済みデータや実行可能アルゴリズムと誤認しない。

### exact-source CI・公理監査・Git tree

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFiniteBorelHaarCellExistenceV5_PZ37AFN.lean` **1ファイル・307追加行、公開7定理・7件の `#print axioms`**。既存Leanファイル、元物理模型・Haar測度、workflow、公開rootは変更なし。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- 正しい数学的型で初回からexact-source Lean成功。最終source HEAD `7b4f45cc50b0bc61b20c022f95c6f79cb2fb4dd1` の [CI #41801635520](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41801635520) は **11,321/11,321 SUCCESS**。新規7定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ。`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- source `7b4f45cc50b0bc61b20c022f95c6f79cb2fb4dd1`、test-merge `b0f7fb8b5a6107c410e171bb83fd1571b33beadc`、squash `0d1c0cf21d7ce0205c2b20f211f58ea48b3bfc7c` のGit treeは **`ca4eeb78d61736bd86b92f2a80b9bad084013735`** で完全一致。

### 未解決obstructionと次段AFO

AFNは正半径に対する真正有限Borelセル・真正Haar質量有理包囲・真正FF中心有理近似の**非計算的存在**を形式証明した。一方、計算可能な元SU(2)格子とセル質量の明示誤差評価、具体的な有理FF標本の検算、AFG物理標本表の構成、strict二閾値符号交差、体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは**未証明**。AFOでは真正SU(2)↔S³座標と有理区間演算による**実効的な小セル構成・質量/標本認証**へ進める。

---

## 検証済み定理 — AFM（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFL定理PR #6301・文書 #6302/#6303まで全件MERGEDの正本を継承し、AFM定理PR [#6304](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6304) は **MERGED**。定理squash SHA `9b1b19e45b3770bc464ffbeb1f650cd9b2105158`。既存の元SU(2)相互作用Wilson作用、中心化Gauss-law物理源、真正Perron真空・transfer、正規化SU(2) Haarと境界pair-Haar `ν_H`、真正弦距離 `d_J` と全リンク `D_H`、FC envelope、AEX二球障害、公開root、固定Lean/mathlibは変更しない。

### 真正FF受信器の右リンク更新変動係数を外部仮定なく形式証明

- **元のFFと中間transfer quotientを厳密に区別**：AFLで使う元受信器は `F_z(g)=p4Q2PZ37ABZ_originalReceiverSection` であり、ABZの元transfer section `U_z(g)=t_f(B[e:=g])/ρ_H(A,B[e:=g])` そのものではない。ABZの同じ真のGauss-law物理源から、**`F_z(g)=‖T_H‖⁻¹t_f(B)−P_z U_z(g)`**、`P_z=‖T_H‖⁻¹ρ_H(z)>0` を保持する。元の未更新源項は差で相殺するが、正の真正Perron因子は消去しない。
- **元transfer quotientの明示包絡と単位弦距離係数**：AEU/GNの真正JQ物理受信器と元ABZ sectionの正確な関係 `F_JQ=a_H U`、`a_H=‖T_H‖⁻²>0` を使用し、**`M_U(H)=‖O_H‖/a_H`**、`|U_z(g)|≤M_U(H)` を導く。AEVの中心化物理源Haar L¹量 `M_src(H)` から `L_T(H)=13β₀M_src(H)`、AEQ/AEKの真正密度変動と下界から `L_ρ(H)=13β₀ exp(13β₀)M_ρ(H)`、`λ_ρ(H)>0` を得る。元AEFの商変動補題で、`d_J(g,h)≤1` のとき `|U_z(g)−U_z(h)|≤[(L_T+M_U L_ρ)/λ_ρ]d_J(g,h)` を証明。
- **長弦も外部条件不要**：`d_J(g,h)>1` は上記の真正`M_U`包絡で制御し、**`L_U(H)=(L_T+M_U L_ρ)/λ_ρ+2M_U`** について全 `g,h∈SU(2)` で `|U_z(g)−U_z(h)|≤L_U(H)d_J(g,h)` を形式証明。非負性も別定理化。数値上界が体積一様という主張はしない。
- **真正FF応答の変動・包絡へ型付き移送**：ABZのアフィン恒等式から全弦で **`|F_z(g)−F_z(h)|≤P_z L_U(H)d_J(g,h)`**。絶対値包絡は同じ元FFの有界連続関数ノルム **`M_{FF}(H,e)=‖p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF_e‖`** から無条件に得る。新型 `originalNumericOnlyCellSamples` は受信器側・AFL四文字側の任意Lipschitz/envelope入力を一切要求せず、元の `F_z`・`F_z²`・`F_zφ_j` の実有理標本と真正SU(2) Haarセル証明だけを入力する。
- **AFK→AFJ→AFI→AFHを元の物理量のまま接続**：元の四係数セル誤差は厳密に **`Δ_coeff,j=(P_z L_U(H)+M_{FF}(H,e))r+ε_coeff,j`**。元の真正Haarセル積分・係数/分散有理区間・二閾値殻の型付き証明書へ変換し、実際に認証された中心に限り元Wilson/Perron残差の二符号を引き継ぐ。架空の具体サンプル・Haarセル・代理測度は導入しない。

### exact-source CI・公理監査・Git tree

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPhysicalReceiverSectionChordalSlopeV5_PZ37AFM.lean` **1ファイル・460追加行、公開15定理・15件の `#print axioms`**。既存Lean、物理模型、元測度、workflow、公開rootは変更なし。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- 初回CI [#41795835331](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41795835331) は中間`U`と元FF`F`を取り違えたAFL証明書での依存型不一致5件を検出。元ABZ/AEU/AEV/AEF/AEK/AEQ/AFL/AFKの型とLeanファイル全文を照合し、真正FFアフィン項と`P_z`を保って修正した。最終exact-source HEAD `f16b0d7e7ac781b9679cc7948478000850732e16` の [CI #41797073199](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41797073199) は **11,320 / 11,320 SUCCESS**。15定理の公理は`propext`・`Classical.choice`・`Quot.sound`のみ。`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt SUCCESS。
- source HEAD `f16b0d7e7ac781b9679cc7948478000850732e16`、test-merge `524e26adb4c5d69f4a281bbb485f30feccf6854e`、squash `9b1b19e45b3770bc464ffbeb1f650cd9b2105158` のGit treeは **`04cf231516106a218200fa9893dbbff3980a9573`** で一致。

### 未解決のobstructionと次段AFN

AFMは**固定有限体積での元の物理受信器の外部包絡・Lipschitz証明条件を除去**した。なお真正SU(2)有限可測セルの具体構成、Haar質量の厳密有理区間、元FF受信器の有理中心値誤差、実際に両閾値で符号交差する中心、体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは**未証明**。次段AFNでは真正Haarセル・中心・半径・質量と有限数値標本の構成的認証を強化し、非空の厳密二符号殻の充足可能性を具体的に調べる。

---

## 検証済み定理 — AFL（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFK定理PR #6298・文書 #6299/#6300の全件MERGEDを継承し、AFL定理PR [#6301](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6301) も **MERGED**。定理squash SHA `a23be3f0ce64a6d6a0b0287f0cd4d3ecc322139e`。元の相互作用Wilson SU(2)、中心化Gauss-law物理源、真正Perron真空、元右リンク更新transfer、正規化SU(2) Haar・境界pair-Haar測度 `ν_H`、元全リンク距離 `D_H`、FC envelope、AEX保守的二球FC obstruction、公開root・固定Lean/mathlibを変更しない。

### 真正SU(2)四成分文字の明示係数1弦距離評価

- **実8成分特徴と元文字の厳密同一性**：元のSU(2)正規化実8成分特徴 `J(g)` と元Wilson一リンク文字 `χ(g)=1−E(g)` について、元の相対トレースkernelの真正Hilbert内積から `χ(g)=⟪J(1),J(g)⟫_ℝ` を証明。ADKの `‖J(g)‖²=1` により `‖J(1)‖=1`。Cauchy–Schwarzで **`|χ(g)−χ(h)|≤d_J(g,h)`** を導出。独立の代理文字・新規測度・任意のLipschitz仮定は導入しない。
- **元SU(2)左平行移動は真正等長**：ADKで検証済みの `d_J(g,h)²=2E(g⁻¹h)` を使用し、任意の真正 `a,g,h∈SU(2)` で **`d_J(ag,ah)=d_J(g,h)`** を証明。これは群作用の元行列・元Wilsonエネルギーだけを使う。
- **四つの真正Haar文字に外部上界不要**：ACKの元Quaternion要素 `q_j` による `φ_j(g)=χ(q_jg)` に左等長性を適用し、全 `j∈Fin 4,g,h∈SU(2)` で **`|φ_j(g)−φ_j(h)|≤d_J(g,h)`**。別のACK真正恒等式 `Σ_j φ_j(g)²=1` と二乗非負性から **`|φ_j(g)|≤1`** も証明。ここで「係数1」は明示上界であり、最適定数の下限・必要性を別途証明したという意味ではない。
- **AFKの文字側仮定を型から除去**：真正受信器 `F_z` のenvelope `M_F(z)` と弦距離斜率 `L_F(z)`、元SU(2)有限Haarセル・中心・半径・質量の証明、中心有理サンプル誤差のみを要求する新しい`originalReceiverOnlyCellSamples`を定義。文字側 `M_φ=L_φ=1` は外部入力でなく上記Lean定理から構成し、AFK完全証明書へ型付き移送する。四係数セル誤差は **`Δ_coeff,j=(L_F+M_F)r+ε_coeff,j`** と簡約。
- **真正Haar・物理ギャップへの条件付き連鎖**：新型からAFK→AFJの真正セル積分→AFIの元係数・分散有理区間→AFHの真の二閾値殻へ接続。検査が通った実中心では元Wilson/Perron残差ギャップの厳密二符号、同一真正境界pair-Haar殻の正質量、AFD真正 `2r` 分離packing `|t|κ_H(r)≤ν_H(Shell)`、非零振幅・閾値分離障害を引き継ぐ。物理的な中心が無条件に存在するとは主張しない。

### exact-source CI・公理監査・Git tree

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFourModeSharpChordalLipschitzV5_PZ37AFL.lean` **1ファイル・377追加行、公開11定理・11件の `#print axioms`**。既存Lean、元物理模型、Haar則、workflow、公開rootは変更なし。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- 初回CI #41792435952で `Finset.single_le_sum` の被加算関数型推論不足と、独立受信器証拠構造で体積 `H` の重複束縛による依存型不一致を検出。全Leanソース・ACK/ADK・AFK/AFJ・固定mathlibシグネチャを照合し修正。最終exact-source HEAD `823b75ac8e8fecb2d8c9db795eb985a20f92498b` に対する [CI #41793129863](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41793129863) は **11,319/11,319 SUCCESS**。11定理の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**、独立MCP completion receiptもSUCCESS。
- source HEAD・test-merge `b32d68219e0f3de69c389a8c5fda6d349054d22e`・squash `a23be3f0ce64a6d6a0b0287f0cd4d3ecc322139e` のGit treeはすべて `e1699fd75182a3871b68d86500ee28b3cd519b99` で一致。

### 未解決obstructionと次のAFM

AFLで文字側のenvelope・弦距離係数は無条件に証明した。一方、**元Wilson/Perron物理受信器 `F_z` のLipschitz係数とenvelope、真正SU(2)有限セル分割とHaarセル質量の有理区間、中心値サンプル、実際の厳密殻交差、H一様coercivity**は依然未証明。物理Hamiltonian spectral gapと連続体4D Yang–Mills質量ギャップも未証明。次段AFMでは受信器の真の右リンク更新transfer・Perron因子・中心化Gauss-law物理源を分解し、実8成分弦距離による数値検証可能な真の受信器変動係数を検討する。

---

## 検証済み定理 — AFK（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAPの文書ミラーのみ。AFJ定理PR #6295と文書PR #6296/#6297をMERGEDとして継承し、AFK定理PR [#6298](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6298) も **MERGED**。定理squash SHA `2c644f98e5769b98472ff04b89f37fb92d7d4ecb`。元の相互作用Wilson SU(2)、中心化Gauss-law物理源、真正Perron真空、元の右リンク更新transfer、正規化SU(2) Haar・境界pair-Haar測度 `ν_H`、真正全リンク距離 `D_H`、FC envelope、AEX保守的二球FC obstruction、公開root・Lean/mathlib固定pinを変更しない。

### 真正SU(2)弦距離の有限セル半径とWilson/Perron積分証明書

- **元の真正d_J・Haar分割を保持**：ADKで証明された元のSU(2)実8成分特徴距離 `d_J(g,h)=‖J(g)−J(h)‖` を使う。AFJの有限可測分割 `C_i` と真正Haar質量の認証済み有理重みをそのまま保持し、各セルに真正SU(2)中心 `g_i`、共通半径 `r≥0`、`g∈C_i⇒d_J(g,g_i)≤r` の型付き証拠を追加する。新たな代替距離・測度・receiverは導入しない。
- **元の受信器・Haar文字の上界とLipschitzを厳密な別証拠として保持**：同じ元F55/Gauss-law源から得る真正Wilson/Perron受信器 `F_z(g)` の包絡 `|F_z(g)|≤M_F(z)` と弦距離斜率 `|F_z(g)−F_z(h)|≤L_F(z)d_J(g,h)`、四つの真正Haar文字 `φ_j` の `M_φ(j)` と `L_φ(j)` をすべて元関数への型付き条件として保持。これらの正の数値評価や一様性は未証明であり、形式上の入力に限る。
- **有限セル中心値から全セル誤差へ**：真正中心 `g_i` で `F_z`、`F_z²`、`F_zφ_j` それぞれの有理標本 `q_i` と中心誤差 `ε` を厳密に検証すれば、実際のセル全体で
  `Δ_mean=L_F r+ε_mean`、
  `Δ_second=2M_F L_F r+ε_second`、
  `Δ_coeff,j=(L_F M_φ,j+M_F L_φ,j)r+ε_coeff,j`
  が成立する。二乗の因数分解および積の加減分解をLean4で直接証明し、有限個の中心誤差からAFJの無限個のcellwise不等式を導出。非負性も別途証明。
- **AFJ→AFI→AFHの真正型付き連鎖**：半径・中心・真正変動証明書からAFJの元Haar-cell quadrature構造を作り、AFIの元係数4個・真の分散の有理誤差証明書を構成。条件付きの厳密二符号選別から元の残差殻 `Shell(θ_lo,θ_hi)` に真正正Haar質量を導出し、AFDの `2r` 分離packingで `|t|κ_H(r)≤ν_H(Shell)` を保持する。認証中心では元物理振幅平方の正性と厳密に異なる二閾値も保存する。

### exact-source CI・公理監査・Git tree

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalChordalCellRadiusCertificatesV5_PZ37AFK.lean` **1ファイル・520追加行、公開10定理・10件の `#print axioms`**。既存Leanモジュール・元物理模型・Haar則・workflow・公開rootは変更なし。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- 初回CI #41785331369では数式の加法不等式補題の向きと絶対値のLean記法を修正。次のCI #41786122008では11,318/11,318のビルドが成功したが未使用前提のwarning3件を検出し、冗長な補助補題引数のみ整理。最終exact-source HEAD `651ab2071fa7b01170c9874425b41776428ee796` に対する [CI #41786776626](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41786776626) は **11,318/11,318 SUCCESS**。10件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receiptもSUCCESS。
- source HEAD・test-merge `f062617d51d517b31cd09d19d2a295a9d8740627`・squash `2c644f98e5769b98472ff04b89f37fb92d7d4ecb` のGit treeはすべて `86d8c6fae28f478db77c87723fdd98075ecb3658` で一致。

### obstructionと次段AFL

AFKは**すでに真正関数上で認証済みのセル半径・受信器と文字の変動率・中心値誤差を入力した場合の数学的な接続定理**。真正Wilson–Perron受信器の具体的Lipschitz定数・SU(2)文字の数値変動定数・具体的Haarセル分割と質量・有理標本認証・非空の厳密殻交差はまだ構成されていない。体積一様coercivity、物理Hamiltonian gap、連続体4D Yang–Mills質量ギャップの証明は主張しない。次のAFLでは、元のSU(2)8次元特徴とWilson積・Perronの正密度変動に基づく**実際の受信器・文字のchordal Lipschitz定数**を評価し、有限セル有理証明書の充足可能性を調べる。

---

## 検証済み定理 — AFJ（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFI定理PR #6292・文書PR #6293/#6294までMERGED済み。AFJ定理PR [#6295](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6295) も **MERGED**、定理squash SHA `80fd246cc3b05a13b4ac20e349a7d1a9108462c4`。元の相互作用Wilson SU(2)、中心化Gauss-law物理源、Perron真空、同じ右リンク更新transfer、真正正規化SU(2) Haar・境界pair-Haar `ν_H`、全リンク距離 `D_H`、FC envelope、AEX保守的FC no-go、公開rootと固定Lean/mathlibを変更しない。

### 真正SU(2) Haar有限セル積分の誤差認証

- **真正可測分割・質量の厳密証明書**：同じSU(2)を有限個の可測セル `C_i` へ分け、各点の一意所属、真正Haar質量 `μ(C_i)` と有理数重み `p_i` の誤差 `|μ(C_i)−p_i|≤δw_i`、`δw_i≥0` を型付きで保持。数値セル・質量を証明抜きで仮定した離散代替測度は使用しない。
- **有理有限段関数の真正積分**：各セル上の有理候補 `q_i` と実被積分関数 `f(g)` について `|f(g)−q_i|≤ε` をセルごとに真正証明する。有限指示関数の和を元の正規化Haar測度で積分し、厳密に `∫step dμ=Σ_i μ(C_i)q_i` をLean4で証明。したがって **`|∫f dμ−Σ_i q_i p_i|≤ε+Σ_i|q_i|δw_i`**。セル内振動とHaarセル質量の誤差を分離して保持する。
- **真正物理受信器そのものを積分**：AFGの元全境界有限ネットの各中心で、真正Wilson/Perron中心化受信器 `F_z`、その二乗 `F_z²`、ACK四成分Haar係数を定める `F_z φ_j` それぞれについて同一可測Haar分割に依存する有理セル標本と厳密誤差証拠を型付きで保持。元のWilson source、Perron真空、transferやHaar測度を代理データに置換しない。
- **平均と二次モーメントから分散を導出**：元の真の分散恒等式 `V_z=∫F_z²dμ−(∫F_zdμ)²` により、有理平均候補 `û`、二次モーメント候補 `ŝ` から **`v̂=ŝ−û²`** と `δV=δSecond+δMean(2|û|+δMean)` を構成し、真正分散の絶対誤差を証明。分散の独立oracleは仮定しない。
- **AFI→AFH→AEA/AFDへ型付き接続**：四係数と分散の真正有理誤差をAFI証明書へ代入し、両閾値の厳密符号を認証した場合に限り、同じ真正殻で正Haar測度と `2r` 分離packing `|t|κ_H(r)≤ν_H(Shell)` を得る。無条件の候補非空性を宣言しない。

### exact-source CI・独立公理監査・Git tree

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHaarQuadratureCertificatesV5_PZ37AFJ.lean` **1ファイル・660追加行、公開16定理・16件 `#print axioms`**。既存Lean、元SU(2)物理模型、測度、workflow、公開rootに変更なし。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- 初回CI #41778604965では固定mathlibに存在しない `Set.indicator_of_not_mem` の参照、積分ノルム評価の型推論、絶対値のLean構文、三角不等式の引数指定を検出。新規ファイル全文と元ACK・ACL・ACM・AFIの定義、固定mathlib APIを照合して修正。最終exact-source HEAD `cba2cb1d4b129bdbe1ed45829f60b0b43b23a8d0` の [CI #41779210616](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41779210616) は **11,317/11,317 SUCCESS**。16定理の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error 0/0、MCP CI completion receiptもSUCCESS。
- source・test-merge `08d6b46d629341005357d5f2a30731c22fd3824b`・squash `80fd246cc3b05a13b4ac20e349a7d1a9108462c4` のGit treeはすべて `66413cf6953493f301ea02aede90c5b00fc7a08d` で一致。

### 未解決境界・次段AFK

AFJが証明したのは、**元の物理受信器のセル内誤差と真正Haar質量誤差を個別に証明した場合**の有限有理積分・分散認証である。実際のSU(2)セル分割と数値的Haar質量区間、真正受信器のセル内振動・有理標本、非空の二閾値符号交差、有益なpacking数、体積一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップの実証ではない。次段AFKでは、元SU(2)の被覆と元の物理受信器の連続性・Lipschitz評価を使い、有限セルの誤差予算を現実に検証する方法と数値certificationの障害を解析する。

---

## 検証済み定理 — AFI（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFHの真正Wilson/Perron区間殻定理（#6289、文書 #6290/#6291、MERGED）を継承し、AFI定理PR [#6292](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6292) を **MERGED** として正式記録する。定理squash SHAは `3c5ee371e9a63a149cea3b705432b3f06a8f440e`。元の相互作用Wilson SU(2)、中心化Gauss-law物理源、Perron真空、右リンク更新transfer、真正境界pair-Haar測度 `ν_H`、元の全リンク距離 `D_H`、FC envelope、AEX保守的FC no-go、公開rootと固定Lean/mathlibを変更しない。

### 真正四成分係数・分散からの計算可能形の区間証明書

- **元物理量への証拠付き入力**：真正ACKのHaar四係数 `m_j(a)` と真正ACLのreceiver分散 `V(a)` について、AFGの同じ有限全境界ネット `s` 上の有理数候補 `q_j(a), v̂(a)` と、`|m_j(a)-q_j(a)|≤δ_j(a)`、`|V(a)-v̂(a)|≤δ_V(a)`、`δ_j,δ_V≥0` の厳密証明を依存型構造に保持。候補数値を認証なしに元Wilson/Perron物理値として扱わない。
- **真正ACM恒等式から誤差伝播**：`A(a)^2=Σ_{j:Fin 4}m_j(a)^2`、`V(a)=4A(a)^2+W(a)` をそのまま使用。有理係数の二乗和 `â=Σ_j q_j²`、`Δ_A=Σ_j δ_j(2|q_j|+δ_j)`、`ŵ=v̂−4â`、`Δ_W=δ_V+4Δ_A` を構成し、真正元物理量について `â−Δ_A≤A²≤â+Δ_A` および `ŵ−Δ_W≤W≤ŵ+Δ_W` を証明。**Wの誤差を独立の仮想受信器に置換しない**。
- **区間幅と閾値別の頑健性**：振幅平方の区間幅は `2Δ_A`、高次残差の区間幅は `2Δ_W`。真正ギャップ `G_θ=W−θA²` に必要な誤差予算は `Δ_G(θ)=δ_V+(4+θ)Δ_A`（`θ≥0`）。両閾値 `0≤θ_lo≤θ_hi` に対し、`η_lo<v̂−(4+θ_lo)â−Δ_G(θ_lo)` かつ `v̂−(4+θ_hi)â+Δ_G(θ_hi)<−η_hi` を満たす有限標本は、AFHの真正区間証明書の認証済み殻内中心となる。
- **真正Haar殻への型付き接続**：厳密符号が成立した中心の元 `D_H` 球は同一真正殻 `Bad_(θ_lo)∖Bad_(θ_hi)` に包含され、AEAの `κ_H(r)>0` により正の元pair-Haar測度が従う。AFH/AFGの元greedy `2r` 分離packingへ接続して `|t|κ_H(r)≤ν_H(Shell)` を継承し、既存のAFE/AFA GI・FC条件を変更しない。

### Lean4検証・公理依存・Git tree

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCoefficientIntervalBudgetsV5_PZ37AFI.lean` **1ファイル483追加行・公開11定理と11件 `#print axioms`**。既存Leanファイルは変更なし。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- 初回は説明文中の `+/-` がLeanコメント開始記号として解釈されたソース監査エラー、次に `∑ j` の被加算項を括弧で囲まなかった束縛範囲のelaborationエラーを全文と依存定義から修正。最終exact-source HEAD `6439c7202cdf4275e163f049dd2dde22593b8be2` に対する [CI #41776343744](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41776343744) は **11,316/11,316 SUCCESS**。11件の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**。独立MCP completion receiptもSUCCESS。
- source HEAD・test-merge `d09f3a863aeab6bcd35952f51bd9249caaf8ab57`・squash `3c5ee371e9a63a149cea3b705432b3f06a8f440e` のGit treeはすべて `bc26bd9e3feb8154ba58c4ec7fb68646e0509db0` で一致。

### 証明の境界と次のAFJ

AFIは**値と誤差の証拠が供給された場合の区間導出・真正殻判定**を完成したもの。真正Wilson–Perron係数や分散の具体的な数値積分・有理上下界、非空の厳密符号交差、有益なpacking数、体積 `H` 一様coercivity、物理Hamiltonian spectral gapまたは連続体4D Yang–Mills質量ギャップを主張しない。次段AFJでは同一元物理受信器の係数積分・分散について、証明付き有理近似、有限標本誤差、独立に追試可能な数値certificateの構成を検討する。

---

## 検証済み定理 — AFH（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFG（定理PR #6286、文書 #6287/#6288、マージ後CI #41747718991 SUCCESS）を継承し、AFH定理PR [#6289](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6289) は **MERGED**。定理squash SHA `5299db6ecc751766cb1c51188b5505807f70d83c`。元のWilson SU(2)、中心化Gauss-law物理源、Perron真空、元の右リンク更新transfer、同一真正境界pair-Haar測度 `ν_H`、元の全リンク距離 `D_H`、FC envelope、固定Lean/mathlib、公開rootおよびAEXの保守的二球FC no-goを変更しない。

### 真正Wilson/Perron残差の区間上下界証明書

- **真正元物理量を保持**：有限ネット上の元振幅平方 `A_F(a)^2` と元高次残差 `W_F(a)` に対し、各中心で `ampLower(a)≤A_F(a)^2≤ampUpper(a)`、`residualLower(a)≤W_F(a)≤residualUpper(a)` を元物理量との型付き証明として保存。区間数字だけで真正上界と見なすことも、transfer・Perron重み・Haar測度を代理模型へ交換することもしない。
- **非負閾値での厳密符号検査**：`0≤θ_lo≤θ_hi` のもと、`η_lo<residualLower(a)−θ_lo*ampUpper(a)` かつ `residualUpper(a)−θ_hi*ampLower(a)<−η_hi` を有限集合で検査すると、元の真正残差ギャップ `G_θ=W_F−θ*A_F²` に対して `G_(θ_lo)(a)>η_lo>0`、`G_(θ_hi)(a)<−η_hi<0` が従う。**区間認証済み中心はAFGの真正Robust中心集合の部分集合**であり、偽陽性を生じない。
- **物理比・厳密閾値障害**：認証中心では `A_F(a)^2>0` と `θ_lo<θ_hi` が必要で、真正物理比 `θ_lo<W_F(a)/A_F(a)^2<θ_hi` が成立する。この比は元のWilson/Perron receiverの同一配置上で定義され、ゼロ振幅の点を隠れた仮定として除外しない。
- **区間を狭めると認証が維持**：`residualLower` の引上げ、`residualUpper` の引下げ、`ampLower` の引上げ、`ampUpper` の引下げが真正上下界として保持されるなら、認証済み中心集合は単調に拡大する。各標本が少なくとも一方の厳密marginを満たせない場合は当該有限区間表の認証候補が空となるが、**真の殻の空性や、より精密な区間表での不可能性は主張しない**。
- **exact-value embeddingと条件付き完全性の境界**：元の真正物理量を上下界の両方に採る形式的なexact intervalはAFGの元Robustフィルタと厳密に一致する。これは型付き構造の整合性を示すが、元の真の振幅・残差を数値評価したことではない。

### 区間認証から真正Haar・GI・FCへ

- AFDの有限greedy分離packingを**区間認証済み中心のみ**に適用し、元の全リンク距離 `D_H(a,b)≥2r` のもとで同一の真正Haar殻 `Shell(θ_lo,θ_hi)=Bad_(θ_lo)\\Bad_(θ_hi)` にある球の重複を排除。AEAの元SU(2)球下界 `κ_H(r)>0` から `|t|κ_H(r)≤ν_H(Shell(θ_lo,θ_hi))` を証明。
- これをAFGの元上界 `U_AFG=min(U_hi,U_lo−|t|κ_H(r))` に移送し、追加の真正Haar測度仮定なしで `ν_H(Bad_(θ_hi))≤U_AFG` を導出。AFHの数値認証と、AFEの独立低・高閾値表の認証はそれぞれ必要。
- 独立の真正数値条件 `θ_hi*A4_H+B_H²*U_AFG<64*A4_H` なら平均二乗GI証明書 `Budget_H>0` と元の符号付き二posterior応答が非零となる真正正Haar測度の開領域を導出。より強い真のFC条件には独立の未使用分 `Eunused_H≤σ*A4_H` と `(θ_hi+σ)*A4_H+B_H²*U_AFG<64*A4_H` が必要。元GI平均非正にはAFAの必要質量下界を保持する。

### exact-source CI・正式定理記録

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIntervalShellWitnessesV5_PZ37AFH.lean` **1ファイル560行・19公開定理と19件 `#print axioms`**。既存Lean、元物理模型、Haar測度、workflow、公開rootは一切変更しない。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を固定。
- 初回CI #41768798053で固定mathlibに存在しないFinset空集合補題名を検出。全文・依存定義を照合して `Finset.ext` による直接証明に修正。修正後のexact-source HEAD `11494dd6427302aabb4924bbf223b025f8836357` に対する [CI #41769376813](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41769376813) は **11,315/11,315 SUCCESS**。19定理の依存公理は `propext`、`Classical.choice`、`Quot.sound` のみで、`sorryAx` なし、変更Lean warning/error **0/0**。
- source HEAD、test-merge `87d33105c4acdc401c47d38b534cbdeea86030f9`、squash `5299db6ecc751766cb1c51188b5505807f70d83c` のGit treeが **`0eeec801e920c0b6c5433afe6896c1a2a9759967` で一致**。これは有限体積での真正物理量の区間条件付き形式証明書であり、具体的な数値区間・H一様coercivity・物理Hamiltonian spectral gap・連続体4D Yang–Mills質量ギャップの実証ではない。

### 次の独立課題 — AFI

真正Wilson/Perron振幅・高次残差の有限標本で、元の連続性・上下界から検証可能な誤差予算の構成を検討し、数値的に認証可能な殻内候補と空表障害を分離する。真正SU(2)・Perron・物理Gauss-law sourceとAEXのno-goは維持する。

---

## 検証済み定理 — AFG（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` はREADME・ROADMAPの文書ミラーのみ。AFF（定理PR [#6283](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6283)、文書 #6284/#6285、マージ後CI #41739389697 SUCCESS）を継承したAFG定理PR [#6286](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6286) は **MERGED**。定理squash SHA `8b3bcb6746e1eea0222621e91578c12ef9d1b927`。元の相互作用するWilson SU(2)、中心化Gauss-law物理源、Perron真空、右リンク更新transfer、同一元境界pair-Haar測度 `ν_H`、元全リンク距離 `D_H`、FC envelope、公開rootとLean/mathlib固定pinを変更せず、AEXの保守的二球FC no-goも維持する。

### 真正有限ネット・頑健な殻中心の形式証明

- **真正独立誤差つき有限ネット**：閾値 `θ_lo≤θ_hi`、二つの正の振動許容値 `η_lo,η_hi`、半径 `r>0`、実際の境界pair有限ネット `s` とその `D_H` 被覆証拠、および元の残差ギャップ `G_θ(z)=W_F(z)−θ A_F(z)^2` の両閾値での一様変動証拠を依存型 `originalShellSampleTable` に保持。AFB一様連続性とAEE有限被覆から、任意の正許容値について真正表の存在を証明する。
- **真正物理値の有限フィルタ**：`Robust(s)={a∈s | η_lo<G_(θ_lo)(a) ∧ G_(θ_hi)(a)<−η_hi}` を定義。各頑健中心 `a` について元の全リンク球 `B_D(a,r)` が真正差分殻 `Bad_(θ_lo)\\Bad_(θ_hi)` に含まれ、AEAの正Haar球下界がそのまま適用される。
- **分離packing・重複の排除**：AFDの有限greedy構成により `t⊆Robust(s)` を抽出し、異なる中心間の距離 `D_H(a,b)≥2r` を証明。ADLの元の三角不等式により各球の非重複性を得て、**`|t| κ_H(r)≤ν_H(Bad_(θ_lo)\\Bad_(θ_hi))`** をLean4で証明。ここで `κ_H(r)=κ(r/(2|Link_H|+1))^(2|Link_H|)>0` はAEAの真正SU(2)ペアHaar球下界であり、体積 `H` には依存する。
- **中心検出の条件付き完全性**：元の境界配置 `z` に厳密な二符号 `G_(θ_lo)(z)>0>G_(θ_hi)(z)` が存在すれば、正の振動余裕を選んだ真正有限ネットで頑健中心を検出でき、`|t|κ_H(r)>0` を伴う真正殻質量下界証明書が存在する。一方、そのような元物理点の**無条件存在を証明したのではない**。具体的標本値・有限比較の数値認証や体積一様下界は別課題。

### AFEとの統合・真正GI/FCへの条件付き移送

- 独立に認証したAFEの低・高閾値の有限表上界 `U_lo,U_hi` と、同一真正殻で認証した分離packing `t` から **`ν_H(Bad_(θ_hi))≤U_AFG=min(U_hi,U_lo−|t|κ_H(r))`** を証明。これは二つのHaar上界の引き算から下界を捏造する操作ではない。証明書が有効なら `0≤U_AFG≤1`、かつ両AFE表より悪化しない。
- **元の平均二乗GI証明書**：`θ_hi≥0` と別途数値認証された `θ_hi*A4_H+B_H²*U_AFG<64*A4_H` の下で、元の `Budget_H>0` と元の符号付き二posterior GI応答が非零となる真正正Haar開領域を導出。**より強い元FC判定** には独立の真の未使用分 `Eunused_H≤σ*A4_H` と `(θ_hi+σ)*A4_H+B_H²*U_AFG<64*A4_H` が必要。元GI平均証明書の非正性にはAFAの必要質量下界を移送する。

### 正本検証・依存公理・未解決境界

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFiniteShellNetPackingV5_PZ37AFG.lean` **1ファイル579行、18公開定理・18公理監査**。既存Leanファイル・workflow・物理模型・Haar測度・公開rootは不変更。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- [exact-source CI #41746954218](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41746954218) は **11,314/11,314 SUCCESS**。18定理の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**。source HEAD `f10d7905bb93b061c32a485b0bbe0ecda41e8354`、GitHub test-merge `6ab4343eacd257fac962f6ff08f3a8cc4ab73f93`、squash `8b3bcb6746e1eea0222621e91578c12ef9d1b927` のGit tree `6ac57abc8e89915d402d6e08da9bd3875dbf594e` が完全一致。
- これは**元モデルの有限体積・条件付き真正Haar証明書**であり、元の具体的gap標本の数値下界、`H` 一様coercivity、物理Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップの証明ではない。AEXの保守的FC二球no-goを保持する。

### 次の独立課題 — AFH

真正有限ネットの厳密符号検出を、元Wilson/Perronの振幅・残差の区間誤差証明書、閾値間の符号交差・空表障害、半径とpackingの検査可能な定量条件へ進める。必要な数値誤差や物理的符号交差を仮定なしに捏造しない。

---

## 検証済み定理 — AFF（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFE（定理PR #6280、文書 #6281/#6282）を継承し、AFF定理PR [#6283](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6283) は **MERGED**。定理squash SHAは `e1b82397187a259892f9b7e09d8a2b70bc3bf9f5`。真正Wilson SU(2)、中心化Gauss-law物理源、Perron真空、元の右リンク更新transfer、同一境界pair-Haar測度 `ν_H`、FC envelope、真正全リンク距離 `D_H`、固定Lean/mathlibと公開rootを変更しない。AEXの保守的二球FC no-goも保持する。

### 真正Haar閾値殻の厳密分割

- 真正残差ギャップ `G_θ(z)=W_F(z)−θ A_F(z)^2` を使い、`Bad_θ={z | G_θ(z)>0}` と証明。任意の `θ_lo≤θ_hi` に対して `Shell(lo,hi)=Bad_(θ_lo)∖Bad_(θ_hi)` は真正pair-Haar可測で、**`ν_H(Bad_(θ_hi))+ν_H(Shell(lo,hi))=ν_H(Bad_(θ_lo))`**。隣接閾値殻は互いに交わらない。
- **真正殻内球証明書**：同一の元境界配置 `a` と異なる正の許容誤差 `η_lo,η_hi` により `G_lo(a)>η_lo>0`、`G_hi(a)<−η_hi<0`、および元の `D_H` による双方の振動評価を型付きで保持する。元の `D_H` 球 `B_D(a,r)` が殻に包含され、AEAから **`ν_H(Shell(lo,hi))≥κ_H(r)>0`** を証明。ここで `κ_H(r)=κ(r/(2|Link_H|+1))^(2|Link_H|)` はSU(2)元Haar確率の真の、体積依存する球下界。
- もし実際の中心 `a` に `G_lo(a)>0>G_hi(a)` があるなら、AFBのコンパクト一様連続性により真正殻内球証明書の存在を構成する。しかし **そのような中心の無条件存在、数値的に大きな球、体積一様な下界は宣言しない**。AFEの上界同士の引き算から下界を捏造しない。

### 有限階層の非重複証明書と既存GI・FCへの接続

- 元の隣接閾値を型が固定する有限 `ShellChain` を構成し、殻ごとの真正Haar球下界を重複なく合計する。`L_chain=Σ_i κ_H(r_i)` と、AFEの独立した低閾値・高閾値の表上界を `U_lo,U_hi` とすると、元の同一Haar確率で **`ν_H(Bad_(θ_hi))≤min(U_hi,U_lo−L_chain)`** をLean4で証明。有効な表なら右辺は `[0,1]` に入り、既存AFE上界より悪化しない。
- `θ_hi≥0` および別途検査した `θ_hi*A4_H+B_H²*U_AFF<64*A4_H` の下で、元の平均二乗GI証明書が正、かつ元の符号付き二posterior GI応答が非零となる開いた正Haar測度領域が存在する。より強い元FC判定には独立の真の未使用分 `Eunused_H≤σ*A4_H` と `(θ_hi+σ)*A4_H+B_H²*U_AFF<64*A4_H` が必要。平均GI非正なら、AFAの逆向き例外質量下界が `U_AFF` へ引き継がれる。

### exact-source CIと変更境界

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHierarchicalHaarShellCertificateV5_PZ37AFF.lean` **1ファイル・564行のみ追加**、新規公開21定理と21件 `#print axioms`。既存Leanファイル・測度・模型・workflow・公開rootは変更なし。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- 初回の依存型再帰の固定引数の誤渡しを修正し、最終exact-source HEAD `f0e57b26d6a37242138b94caf20cced09147fd65` に対する [CI #41738490132](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41738490132) が **11,313/11,313 SUCCESS**。21定理すべての公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**。
- source・test-merge `adc5e982fcad8ba18a5ba7c01104e7b69600790a`・squash `e1b82397187a259892f9b7e09d8a2b70bc3bf9f5` のGit treeはすべて `4fba3de386360f7807aad887456fc2cc30fb24f8` で一致。マージ後push CI [#41739389697](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41739389697) も **11,313/11,313 SUCCESS**、21件の公理依存は標準3公理のみ、`sorryAx` なし、変更Lean warning/error **0/0** とGitHub MCPで独立再確認した。これは厳密な元モデルの有限体積・条件付き証明書であり、数値十分性、体積一様coercivity、物理Hamiltonianのspectral gap、連続体4D Yang–Mills質量ギャップの証明ではない。

### 次の独立課題 — AFG

真正殻の厳密な二符号中心を元のWilson/Perron残差ギャップから有限の認証可能な条件として得ること、半径・閾値の最適化と正下界の数値検証が次の焦点である。無条件の中心存在を暗黙に仮定せず、AEXのFC no-goと既存の権威境界を維持する。

---

## 検証済み定理 — AFE（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFE定理PR [#6280](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6280) は **MERGED**、squash SHA `b7367d835dad2d46ed97320e901bb11c25cafd4a`。AFD（#6277）・AFC（#6274）・AFB（#6271）・AFA（#6268）までの真正Wilson SU(2)、中心化Gauss-law物理源、Perron真空、元の右リンク更新transfer、同一元境界pair-Haar確率 `ν_H`、FC envelope、全リンク距離 `D_H`、Lean/mathlib固定pinおよび公開rootを変更しない。AEXの保守的AEW二球FC証明書no-goを保持する。

### 複数閾値・複数半径の真正Haar例外質量上界

- **元例外集合の閾値反単調性**：元の真正物理受信器の四成分振幅 `A_F(z)` と高次残差 `W_F(z)` で `Bad_θ={z | θ*A_F(z)^2<W_F(z)}` とすると、平方非負性から `θ_i≤θ_target → Bad_(θ_target)⊆Bad_(θ_i)`。これは独立の代理Haar lawや異なる物理量の仮定ではなく、元の同一境界・物理源に関する集合包含である。
- **真正スケール証拠を保持する依存型**：有限体積 `H` と元の物理リンク `e` について、個々の `θ_i,η_i,r_i,s_i,t_i` と真正 `D_H` ネット、元の差分 `G_θ=W_F−θ*A_F²` の変動証拠、良好中心 `t_i⊆Good(s_i)`、`2r_i` 分離証拠を一つの型として保持。数値だけを入力し、証明書なしに本物のHaar質量の上界とみなす構造ではない。
- **有限表の最小値**：各スケールのAFD真正二重上界 `Dual_i=min(Σ_{a∈Flag(s_i)}ν_H(B_D(a,r_i)),1−card(t_i)*κ_H(r_i))` に対し、有限表 `scales=[i_1,…,i_N]` から **`MultiBudget_H(scales)=min(1,Dual_(i_1),…,Dual_(i_N))`** を構成。`θ_i≤θ_target` が全ての表要素で認証されるなら **`ν_H(Bad_(θ_target))≤MultiBudget_H(scales)`** をLean4で証明する。空表では元の確率上限1を返す。
- **表の単調改善と確率範囲**：一般の有限リストfoldl-min帰納定理を追加。表中の任意の証明書 `c` について `MultiBudget_H≤Dual(c)`、さらに常に `MultiBudget_H≤1`、有効な表なら `0≤MultiBudget_H` を証明。表の要素間に同じ閾値・同じ半径・同じ有限ネットを要求せず、重複しても安全である。
- **各スケールの真正存在証明**：任意の元の物理リンク、任意の `θ`、正のguard margin `η>0` について、AFBのコンパクト一様変動、AEEの真正全境界有限ネット、AFDの有限greedy分離packingを合成し、元の物理量に基づくスケール証拠の存在をLean4で証明。ただし半径・良好packing数・Haar球質量・閾値を数値認証しない。

### 真正GI・FCへの条件付き接続と逆向き障害

- **元の真正GI平均証明書**：`θ_target≥0` かつ各 `θ_i≤θ_target`、別途検査された `θ_target*A4_H+B_H²*MultiBudget_H<64*A4_H` なら、元AFAの二乗GI平均証明書 `Budget_H>0` と真正pair-Haar正測度の開領域で元の符号付き二posterior GI応答が非零であることを導出。数値不等式が無条件に成り立つという宣言ではない。
- **より強い元のFC判定**：独立に真正FC未使用分 `E_H≤σ*A4_H` と `(θ_target+σ)*A4_H+B_H²*MultiBudget_H<64*A4_H` を認証した場合に限り、元の厳密な `B_H²<272*S_H` を証明。GI平均とFCの異なる証明書を保持する。
- **非正GI証明書のobstruction**：元の `Budget_H≤0` なら、任意の有効な多尺度表について **`((64−θ_target)*A4_H)/B_H²≤MultiBudget_H`** が必要。これは平均証明書の数値限界であり、実GIの消滅やYang–Mills質量ギャップのno-goではない。

### exact-source CI、公理・Git tree監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalMultiscaleHaarCertificateV5_PZ37AFE.lean`（396行）**1ファイルのみ追加**。既存Lean、元のSU(2)・物理模型・測度、公開root、workflow不変更。公開14定理・14件 `#print axioms`。Lean `v4.30.0-rc2` / mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- [exact-source CI #41731762702](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41731762702) **11,312/11,312 SUCCESS**。全14定理の依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。初回CIからLean elaboration failureなし。
- exact-source HEAD `9adc511e832f0617336813ed37f1c33a2b2b6f58`、GitHub test-merge、squash `b7367d835dad2d46ed97320e901bb11c25cafd4a` のGit tree `8f0625bfc7fc8d769519751967a95b30e83d4228` が一致。squash後push CIは別途独立確認する。

### 次の独立課題 — AFF

真正多尺度表は厳密な有限次元証明書だが、表の実際の標本・数値的な十分小ささ、元Wilson/Perron残差の定量勾配・良好packing密度、体積H一様な見積り、真正FC未使用分の具体的な上界は未証明。次は複数閾値の階層的差分集合、有限表による局所領域の切り分け、あるいはHaar測度の重複補正を条件付きの形で形式化し、具体的な計算可能証明書へ近づける。AEXの保守的二球FC no-goを維持し、物理Hamiltonianの必要spectral gapおよび連続体4D Yang–Mills質量ギャップは引き続き未証明。

---

## 検証済み定理 — AFD（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFD定理PR [#6277](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6277) は **MERGED**、定理squash SHA `6a67257b9dac6e4417d80cdfa09d5a561077c8bb`。AFC（#6274）、AFB（#6271）、AFA（#6268）までの真正Wilson SU(2)、中心化Gauss-law物理源、Perron真空、元の右リンク更新transfer、元pair-Haar確率 `ν_H`、FC envelope、全リンク弦距離 `D_H`、Lean/mathlib固定pinおよび公開rootを継承し、AEXの保守的二球FC no-goを維持する。

### 新規定理：元の有限良好標本から2r分離packingを構成

- **一般の有限選択定理**：対称かつ自己距離0の関数 `d`、有限集合 `s` と正半径 `r` について、有限帰納法により部分集合 `t⊆s` を構成し、異なる `a,b∈t` では `2r≤d(a,b)`、元の全ての `a∈s` はある `b∈t` に対して `d(a,b)<2r` を満たす。外部のpacking存在仮定や数値cardinalityを挿入せず、これをADLの真正物理境界 `D_H` に適用。
- **元の真正良好標本の抽出**：AFCの `Good(s)={a∈s | W_F(a)+η≤θ*A_F(a)^2}` を元のWilson/transfer振幅・残差で定義し、良好標本 `Good(s)` から上記 `t` を構成。`t⊆Good(s)` の下で `Good(t)=t`、任意の異なる選択良好中心は `2r` 以上離れること、選択した良好中心が元の良好標本全体を `2r` 以内で覆うことを証明。

### AFB・AFCの相補的な真正Haar上界を一本化

- **二重例外質量予算の定義**：AFBの真正例外候補中心 `Flag(s)` と、AFCの選択良好packing `t` を同一の真正元境界標本 `s` 上で保持し、`Dual_H(s,t,θ,η,r)=min(Σ_{a∈Flag(s)}ν_H(B_D(a,r)), 1−card(t)*κ_H(r))` を定義。ここで `κ_H(r)=κ(r/(2*card(Link_H)+1))^(2*card(Link_H))>0` はAEAの本物のSU(2) pair-Haar球下界。
- **真正例外集合の最小上界**：元の真正全リンク有限 `D_H` ネット `s`、同じ元物理残差差分 `G_θ(z)=W_F(z)−θ*A_F(z)^2` の検証済み変動条件 `D_H(a,z)<r→|G_θ(z)−G_θ(a)|<η`、および上記の選択良好packingの下で **`ν_H(Bad_θ)≤Dual_H(s,t,θ,η,r)`** をLean4で証明。元測度上の同じ例外集合にAFBとAFC双方の上界が成立することから、有限和と補集合予算の最小値が正当化される。元の `ν_H` は変更されず、`0≤Dual_H` も導出。
- **選択構成を仮定から取り除く**：任意の真正有限ネットと真正変動証明書が与えられれば、分離した良好部分集合 `t` と上記の二重上界を満たす証明書の存在を証明。さらに任意の真正物理リンク・任意の正のguard margin `η>0` に対し、AFBのコンパクト一様変動半径とAEEの有限真正ネット存在を合成し、`r,s,t` の存在を形式化。ただし数値的に有用な `t.card` や小さいdual予算の存在は主張しない。

### 元のGI・FC境界への正確な移送

- **二乗GI平均証明書**：`θ≥0`、真正数値比較 `θ*A4_H+B_H²*Dual_H<64*A4_H` が独立に成立すれば、元AFAの `Budget_H>0` と真正pair-Haar正測度の開領域での非零符号付き二posterior GI応答を導出。真正GI応答の全配置での非消滅を意味しない。
- **より強い真正FCテスト**：これとは別に実際のFC未使用分 `E_H≤σ*A4_H` と `(θ+σ)*A4_H+B_H²*Dual_H<64*A4_H` を数値認証する場合に限り、元の真正 `B_H²<272*S_H` と対応する開GI領域を証明。AFAのGI平均判定とFC判定を混同しない。
- **逆向きobstruction**：元の平均GI証明書が非正 `Budget_H≤0` なら、任意の有効な二重予算は **`((64−θ)*A4_H)/B_H²≤Dual_H`** を満たす。これは物理GIの消失や連続体Yang–Millsギャップのno-goではない。AEXのAEW二球保守的下界に限定されたno-goもそのまま維持。

### exact-source Lean4検証・公理監査・Git tree

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalDualHaarGreedyPackingV5_PZ37AFD.lean`（425行）**1ファイルのみ追加**。既存Lean・元の模型・Haar測度・公開root・workflow不変更。公開14定理／14件 `#print axioms`。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- [exact-source CI #41728015997](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41728015997) **11,311 / 11,311 SUCCESS**。新規14定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。初回CIからelaboration errorなし。
- exact-source HEAD `e8435d26e5e32de044c31dcb5a769fd54ad2ceb0`、test-merge、squash `6a67257b9dac6e4417d80cdfa09d5a561077c8bb` のGit treeは `df4ca0634d14bbe23e7b662fa6c409847174b5b5` で一致。定理squash後push CIは別途確認。

### 次の独立課題 — AFE

AFDで二重Haar上界の選択構成と統合が形式化された一方、`θ,η,r`、真正良好標本数、元の `D_H` 球の実数値測度、FC未使用分 `E_H` の強い数値認証、体積 `H` に一様な下界は残る。次は単一 `r` と単一 `θ` に固定する強い条件から、複数半径・複数閾値の適応型認証や、良好領域重複の補正を含む有限表の改良可能性を検討する。物理Hamiltonianのスペクトルギャップと連続体4D Yang–Mills質量ギャップは未証明。

---

## 検証済み定理 — AFC（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFC定理PR [#6274](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6274) は **MERGED**、squash SHA `15720bb288c8382f5bb7f1afa3f05210ffaa2833`。前段AFB（#6271）・AFA（#6268）・AEZおよびAEXの保守的AEW二球FC証明書no-goを継承する。真正Wilson SU(2)、Gauss-law中心化物理源、Perron真空、元の更新transfer、元の外側pair-Haar、FC envelope、正本root、Lean/mathlib pinは不変。

### 真正良好球のHaar下界から例外集合上界へ

- **真正良好中心の判定**：元物理受信器の四成分 `A_F`、高次Haar残差 `W_F`、真正差分 `G_θ(z)=W_F(z)−θ*A_F(z)^2` を維持。実境界標本 `s` で `Good={a∈s | W_F(a)+η≤θ*A_F(a)^2}` を定義。証明書 `D_H(a,z)<r → |G_θ(z)−G_θ(a)|<η` があれば、`Good` に属する標本中心の真正開球 `B_{D_H}(a,r)` は AFAの元例外集合 `Bad_θ={z|G_θ(z)>0}` と交わらない。
- **元ADLの三角不等式による厳密な非交差性**：異なる二つの真正良好標本中心に対して `2*r≤D_H(a,b)` が認証されれば、開球 `B_{D_H}(a,r)`、`B_{D_H}(b,r)` は互いに非交差。測度の独立性も幾何の代理量も仮定しない。
- **真正pair-Haar確率の相補上界**：良好中心を相互に `2r` 以上離した有限集合とし、実測度の有限加法性を使用して、**`ν_H(Bad_θ)≤1−Σ_{a∈Good}ν_H(B_{D_H}(a,r))`** を証明。AFBの「例外候補球の質量を上から足す」経路と相補的な「良好球の質量を下から足す」経路である。
- **AEAの真正Haar球下界への無条件接続**：全真正境界中心・任意 `r>0` で確定した `κ_H(r)=κ(r/(2*card(Link_H)+1))^(2*card(Link_H))>0`（`κ(x)=toSphereBallBound(4,x)/4`）を適用し、**`ν_H(Bad_θ)≤1−card(Good)*κ_H(r)`** を得る。これは真正SU(2) pair-Haarの有限体積 `H` 依存評価であり、無条件に多数の良好標本が存在すると主張するものではない。
- **真正GI・FCへの接続**：`θ≥0` と元AFAの数値ゲート `θ*A4_H+B_H²*(1−card(Good)*κ_H(r))<64*A4_H` が別途認証できれば、真正二乗GI平均証明書 `Budget_H>0` および元の符号付き二posterior GI応答が非零となる開・正Haar領域を得る。さらに独立の元FC未使用分 `E_H≤σ*A4_H` と `(θ+σ)*A4_H+B_H²*(1−card(Good)*κ_H(r))<64*A4_H` が必要な場合、より強い真正FC閾値 `B_H²<272*S_H` も導く。
- **逆向きの実数障害**：`Budget_H≤0` なら、有効な良好packing証明書について **`((64−θ)*A4_H)/B_H²+card(Good)*κ_H(r)≤1`** が必要。真正GIの消滅やYang–Mills質量ギャップの不可能性を意味しない。

### 正式なLean4検証と修正理由

- append-onlyで新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalGoodHaarPackingComplementV5_PZ37AFC.lean`（359行）を追加。既存Lean、物理モデル、Haar law、公開root、CI workflowは変更なし。公開12定理／12件 `#print axioms`。Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持。
- 修正版[exact-source CI #41725365393](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41725365393) は **11,310/11,310 SUCCESS**。全12定理の依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- 初回CI #41724465578では、固定mathlibで `PairwiseDisjoint` が `Set` 名前空間にあるのに未修飾で使用したためElaborationが失敗し、後続の有限和・証明式へ型エラーが波及。新規Lean全文・固定mathlibの `measureReal_biUnion_finset`・関連ソースを照合し、2か所を `Set.PairwiseDisjoint` と明示して解決。仮定、定理文、元の測度は弱めず、追加公理はなし。
- exact-source HEAD `3dc2aae39bac8bc9fcf88c9466ca5047d8a176e0`、test-merge `b6f2d21f19a958b809863f125b30e46cddca3b9d`、squash `15720bb288c8382f5bb7f1afa3f05210ffaa2833` のGit treeは `2fbb9b38e2cf27e832e6c55cf3eb125a90389541` で一致。squash後push CIの独立確認は別途行う。

### 次の独立課題 — AFD

有限体積で証明済みの球Haar下界は `H` 依存で小さくなり得る。良好標本の具体的な認証、互いに離れた良好中心のpacking数、真正 `D_H` 球測度の上界・下界を結ぶ体積一様制御、FC未使用分、連続体へのdescentは引き続き未証明。AFBとAFCの二つの例外質量上界を比較して小さい方を採用する数値証明書、あるいは境界幾何の局所分割による重複補正が次の候補。元AEXの二球FC no-go、4D Yang–Mills質量ギャップ未証明の境界は維持する。

---

## 検証済み定理 — AFB（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAPの文書ミラーのみ。AFB定理PR [#6271](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6271) は **MERGED**、squash SHA `93ce1dec59fc0ccedde96768ea72c61216366895`。前段AFA（#6268）、AEZ、AEXまでの真正Wilson SU(2)、中心化Gauss-law物理源、Perron真空、元の更新transfer、pair-Haar測度、FC envelope、原距離、Lean/mathlib pinは不変更。AEXのAEW保守的二球FC下界のno-goを維持。

### 真正例外集合の有限D_Hネット・Haar質量上界

- **真正残差差分**：元の受信器の真正境界量 `G_θ(z)=W_F(z)−θ*A_F(z)^2` を定義し、AFAの例外集合 `Bad_θ={z|G_θ(z)>0}` と対応させる。元ACRの残差連続性とACNの四成分振幅平方連続性から `G_θ` が真の境界ペア空間上で連続と証明。
- **有限体積での無条件な局所変動半径とネットの存在**：ADMの真正全境界距離 `D_H` に対するコンパクト一様連続性により、任意の `η>0` で `r>0` が存在し、`D_H(a,z)<r` なら `|G_θ(z)−G_θ(a)|<η`。既存AEEの真正有限 `D_H` ネット存在定理と接続する。半径 `r` の数値値は未計算。
- **例外候補標本だけの被覆証明**：元の真正境界配置からなる有限ネット `s` に対し、`Flag={a∈s | θ*A_F(a)^2<W_F(a)+η}` と定義。真正変動証明書があれば **`Bad_θ⊆⋃_{a∈Flag}B_{D_H}(a,r)`** をLean4で証明。全境界での残差比一様上界は仮定しない。
- **真のHaar例外質量の有限和評価**：元の真正pair-Haar確率 `ν_H` に対し、一般の有限被覆と実測度の劣加法性を利用して **`ν_H(Bad_θ)≤Σ_{a∈Flag}ν_H(B_{D_H}(a,r))`** を証明。被覆球の独立性・互いの非交差性・代理Haar分布は一切仮定しない。各球について独立に認証した上界 `cap` があれば、`ν_H(Bad_θ)≤card(Flag)*cap` とする公開定理も構成。
- **AFA数値条件と真正GI/FCへの接続**：被覆球の有限和が独立に `ε` 以下と認証され、`θ≥0`、`θ*A4_H+B_H²*ε<64*A4_H` なら、元の正の二乗GI平均証明書 `Budget_H>0` と、真正二posterior符号付きGIが非零となる開・正Haar測度領域を得る。さらに別途 `E_H≤σ*A4_H` と `(θ+σ)*A4_H+B_H²*ε<64*A4_H` が証明されれば、元のより強い `B_H²<272*S_H` を得る。
- **非正証明書の障害を有限和へ移送**：`Budget_H≤0`、`θ≥0` なら、任意の有効な真正有限ネット証明書の例外球質量和は **`((64−θ)*A4_H)/B_H² ≤ Σ_{a∈Flag}ν_H(B_{D_H}(a,r))`** を満たす。これは例外被覆の必要量であって、真正符号付きGI応答の消滅を意味しない。

### exact-source CI・公理監査・Git tree

- 既存Lean・workflow・rootを変更せず、新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExceptionalHaarFiniteNetCertificateV5_PZ37AFB.lean`（348行）1ファイルのみ追加。公開12定理、12件の `#print axioms`。Lean `v4.30.0-rc2` / mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。
- 修正版[exact-source CI #41719148881](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41719148881) は **11,309 / 11,309 SUCCESS**。12定理の公理は `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- 初回CI #41717397875の3件のLean elaboration failureは、(1) 集合所属 `hz : z∈{z|...}` が `linarith` の算術仮説へ展開されていないこと、(2) `measureReal_mono` の対象集合の有限測度証拠が自動補完されないこと、(3) ADMの `|G(a)−G(z)|` と目標 `|G(z)−G(a)|` の向きの型不一致。全集約・既存定理・固定mathlibを照合し、`change`、`(measure_lt_top ν _).ne`、`abs_sub_comm` によって修正。仮定・結論を一切弱めていない。
- 最終exact-source HEAD `166b351f500f8001298866ce857bb79ab61c37fc`、test-merge `58a5d2d4edace0e9a8dea6e08587845fee7f2238`、squash `93ce1dec59fc0ccedde96768ea72c61216366895` のGit treeは `a1edd8d9562ebb9dddafbf0961361cd46a0f67fb` で一致。定理squash後push CIは別途追跡。

### 次の研究境界 — AFC

真正有限ネットと局所変動の**存在**は証明済みだが、`Flag` の具体的な標本数、元の `D_H` 球の真正pair-Haar測度**上界**、非自明な `ε` の小ささ、FC未使用分 `E_H` の数値評価は未証明。有限体積からH一様なコントロール、物理Hamiltonianのスペクトルギャップ、連続体4D Yang--Mills質量ギャップも未証明。AEX二球FC no-goを解除したとの主張ではない。

---

## 検証済み定理 — AFA（2026-11-04 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AFA定理PR [#6268](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6268) はMERGED、squash SHA `0e92ad447852dcdf7505da25c56fa5a9a2dacceb`。AEZまでの元の真正Wilson SU(2)、Gauss-law中心化物理源、Perron真空、元の更新transfer・二posterior、SU(2) Haarと元pair-Haar、FC envelope、原距離、公開root、Lean/mathlib pinは変更しない。AEXのAEW保守的二球下界に関するFC no-goも維持する。

### 真正例外Haar集合による高次transfer残差の全積分制御

- **元の境界空間における正確な例外集合**：任意の`θ≥0`について、元物理受信器の四成分振幅平方`A_F(z)^2`と真正高次残差`W_F(z)`から `Bad_θ(H,e)={z | θ*A_F(z)^2 < W_F(z)}` を定義。元の更新transfer`U_z`とPerron係数`P_z>0`により`A_F(z)^2=P_z²*A_U(z)^2`、`W_F(z)=P_z²*W_U(z)`なので、**`z∈Bad_θ ↔ θ*A_U(z)^2<W_U(z)`** をLean4で厳密に証明。集合は元のpair-Haar位相で開・可測であり、独立Haar分布や代理受信器への置換ではない。
- **新しい無条件の全積分上界**：元FC envelopeの真正点別上界`W_F(z)≤B_H²`と、非例外側の`W_F(z)≤θ*A_F(z)^2`を組み合わせ、真のpair-Haar確率`ν_H`について **`R4_H(e)≤θ*A4_H(e)+B_H²*ν_H(Bad_θ)`** を証明。ここで`A4_H=4*S_H(e)>0`、`R4_H=W_H(e)`はAEZの実際のPerron重み付きtransferモーメント。一般のコンパクト確率空間における連続関数のindicator分割積分補題も公開証明。AEW二球下界の小さな体積因子は使用しない。
- **条件付きの真正GI数値判定**：元Haar例外質量`ν_H(Bad_θ)≤ε`が独立に評価され、**`θ*A4_H+B_H²*ε<64*A4_H`** なら、元の二乗GI平均証明書`Budget_H>0`を導き、既存の定理から真正二posterior符号付きGI応答が非零となる開・正Haar測度領域を得る。例外質量`ε`の十分に小さい値が無条件に得られたという主張ではない。
- **FC envelope経由のより強い判定**：別途AEYの真正FC未使用分`E_H≤σ*A4_H`を検証し、**`(θ+σ)*A4_H+B_H²*ε<64*A4_H`** を満たすなら、元の厳密な`B_H²<272*S_H(e)`に到達する。これはGI平均証明書の条件より強い、独立の数値条件。
- **非正証明書が要求する真正Haar質量**：`Budget_H≤0`なら任意の`θ≥0`で **`(64−θ)*A4_H/B_H²≤ν_H(Bad_θ)`**。特に`θ<64`なら元例外集合は正測度である。真のFCテスト不成立`272*S_H≤B_H²`と、別途`E_H≤σ*A4_H`の下では、**`(64−θ−σ)*A4_H/B_H²≤ν_H(Bad_θ)`**。 `θ+σ<64`なら例外集合の正測度を証明。このobstructionは**証明書の数値境界**であって真正符号付きGI応答の消滅証明でもYang–Mills質量ギャップのno-goでもない。

### exact-source Lean4検証、公理・source Git tree監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExceptionalHaarTailBudgetV5_PZ37AFA.lean`（403行）だけを追加、**公開13定理／13件`#print axioms`**。既存Lean・定理root・物理モデル・workflow変更なし。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- 最終[exact-source CI #41700621006](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41700621006) は **11,308/11,308 SUCCESS**、新規13定理は`propext`・`Classical.choice`・`Quot.sound`の標準3公理のみ、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- 初回CI #41699423749の唯一のelaboration failureは、正のPerron因子による厳密不等式の左右同値で`mul_lt_mul_left hp`に誤った型クラス`MulRightStrictMono ℝ`の合成要求が生じたこと。変更Lean全文と既存APIを検査し、固定mathlibで型が正確に適合する`mul_lt_mul_iff_of_pos_left hp`へ差替え。仮定・定理文・物理模型は弱めていない。
- exact-source HEAD `5950a117781df7bae0144c3b0d7d192f349bad2b`、test-merge `04b3d7e10314cacb550a112bc8d5810d9e964e39`、squash `0e92ad447852dcdf7505da25c56fa5a9a2dacceb` のGit treeはすべて `42188f05178f102d69196c9bd0dc430481b2fca1` で一致。定理squash後push CIを別途確認する。

### 次の独立数値課題

AFAでは、真正残差の全境界一様上界を仮定せず、例外境界集合の量的測度だけを用いる条件付き経路を証明。今後は元のWilson kernel・Perron密度・Haar幾何に由来する`ν_H(Bad_θ)`の具体的な上界、FC未使用分`E_H`の量的制御、有限Hから体積一様なcompatibilityへ移る際の障害を分けて研究する。例外質量が必要閾値を無条件に満たすこと、物理Hamiltonianの必要スペクトルギャップ、連続体4D Yang--Mills質量ギャップはいずれも未証明。

---

## 検証済み定理 — AEZ（2026-11-03 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。新規AEZ定理PR [#6265](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6265) はMERGED、定理squash SHA `a1a0a149d5a89c420dce6570654bd913fd5b86a4`。AEYまでの元の真正Wilson SU(2)、中心化Gauss-law源、Perron真空、真正更新transfer section、二posterior、Haar・pair-Haar測度、距離、root、Lean/mathlib pinおよびAEXの二球no-goを一切変更しない。

### 真正transferのPerron重み付きHaar全モーメントとFC残差を分離

- **真正transfer全積分の定義と同定**：固定正結合 `b0=log(3/2)/64` で、元ABZ・ACQの更新transfer section `U_z`、元のPerron prefactor `P_z>0`、4つの真正SU(2) character係数 `m_{U,z,j}`、その直交残差二乗 `tW_z` を用い、`A4_H(e)=∫_outer P_z² Σ_j m_{U,z,j}² dν_H(z)=4*S_H(e)>0`、`R4_H(e)=∫_outer P_z²*tW_z dν_H(z)=W_H(e)≥0` をLean4で再同定。元の更新密度・Perron重み・Gauss-law物理源を落としていない。
- **FC envelopeの真正transfer表示**：AEYで定義した未使用FC分 `E_H=B_H²−Vbar_H≥0` は、`E_H=B_H²−∫_outer P_z² Var_Haar(U_z)dν_H(z)` と一致。これは元のsource-transfer構造に由来する式であり、新しい独立Haar lawや外部非負仮定ではない。
- **無次元の厳密閾値**：`r_H=R4_H/A4_H≥0`、`s_H=E_H/A4_H≥0` と定義すると、**`Budget_H>0 ↔ r_H<64`**、**`B_H²<272*S_H ↔ r_H+s_H<64`** を形式化。前者は**元ACOの二乗GI平均証明書**の正値判定であり、真正の符号付きGIの必要十分条件ではない。後者は元FC envelopeを用いた**より強い数値十分条件**。いずれも無条件の厳密閾値到達を主張しない。
- **全境界のtransfer上界から真正Haar積分へ**：元境界ペアの**全て**の `z` で `tW_z≤θ Σ_j m_{U,z,j}²` が成り立つという**明示的な条件**から、元のpair-Haar上で積分単調性・実物理受信器の連続性を使って `R4_H≤θ*A4_H` をLean4で証明。特に `θ<64` が別途証明できれば `Budget_H>0`、さらに元の二posteriorの符号付きGI応答が非零となる開かつpair-Haar正測度の領域が実際に存在する。
- **FCの独立slack境界**：上記の全境界transfer条件に加え、真正FC未使用分を `E_H≤σ*A4_H` と**独立に認証**し `θ+σ<64` を満たすなら、**`B_H²<272*S_H`** を得て元の符号付き二posterior GI正領域まで伝播する。`θ`、`σ` は未証明の自由な上界を物理的事実として挿入したものではなく、条件付き定理の明記された入力である。
- **真正境界のobstruction witness**：元GI平均証明書 `Budget_H≤0` が成立するなら、任意の候補 `θ<64` に対して**真正境界 `z` が存在し** `θ Σ_jm_{U,z,j}² < tW_z`。同様にFC判定が不成立で、別途 `E_H≤σ*A4_H`、`θ+σ<64` の条件を課す場合にも同じ真正boundary violationが存在。GI平均証明書の非正値から実際の符号付きGI応答消滅は推論していない。

### exact-source Lean4検証と構造的エラー監査

- 既存ファイルを変更せず、新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWeightedTransferResidualFCGateV5_PZ37AEZ.lean`（365行）だけを追加。**公開14定理**、14件の `#print axioms`。Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定、定理root・CI workflow不変更。
- 最終 [exact-source CI #41641344378](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41641344378) は **11,307/11,307 SUCCESS**。新規14定理すべての公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ。 `sorryAx` なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。初回Leanでエラーなし。
- exact source HEAD `a1c4b8c1f1d840e645b9eebec4454e2b1765ce13`、GitHub test-merge `32f450da2bddbc5bdcdd9dbe4a7ce6a0a120cda8`、squash `a1a0a149d5a89c420dce6570654bd913fd5b86a4` のGit treeは **`de13683d4d6c3586b0bba5c291e125bcf68c56e9` で完全一致**。マージ後push CIは別途独立検査。

### 残る真の物理的課題

AEXの保守的二球幾何下界 `P_H(a,R)` はFC閾値を超えないというno-goを維持。一方、AEZの全モーメント `S_H` と真正transfer残差 `tW_z` は異なる実物理量であり、`Budget_H>0` も `B_H²<272*S_H` も本定理で無条件達成していない。次段階は、全境界を仮定した強いpointwise上界から離れ、元Wilson核とPerron重みを保つ**分割領域ごとの残差・振幅の積分比較**、有限格子からH一様な数値制御へのcompatibilityを研究する。物理Hamiltonianの必要スペクトルギャップと連続体4D Yang--Mills質量ギャップは未証明。

---

## 検証済み定理 — AEY（2026-11-03 JST）

唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AEY定理PR [#6262](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6262) はMERGED、squash SHA `753e32f213470ccd4df7355339efa2069569482b`。前段AEXのAEW保守的二球下界に対するFC no-goを弱めず、既存の真正Wilson SU(2)、中心化Gauss-law物理源、元の物理受信器、Perron真空・transfer、元SU(2) Haarと真正pair-Haar測度、距離、定理root、Lean/mathlib pinを保持する。

### 真正全HaarモーメントとFC envelope未使用分の厳密分解

- **真正の分散恒等式**：ACJ・ACK・ADBの元の共分散二乗モーメント `S_H(e)=∫C_e(z)^2 dν_H(z)`、4成分後の真正高次Haar残差 `W_H(e)≥0`、元受信器分散平均 `Vbar_H=16*S_H+W_H`、元FC envelope `B_H^2≥Vbar_H` を同一の物理モデル上で使用する。新たな外部仮定ではなく、**`E_H(e):=B_H^2−Vbar_H≥0`** を定義した。従って **`B_H^2=16*S_H+W_H+E_H`** が無条件に成立する。
- **真正FC閾値の必要十分条件**：正の固定結合 `b0=log(3/2)/64` において、**`272*S_H−B_H^2=256*S_H−(W_H+E_H)`**。ゆえに **`B_H^2<272*S_H ↔ W_H+E_H<256*S_H`**。これは元の全モーメントに関する**同値**であり、厳密な数値不等式の成立を証明したものではない。
- **無次元分解**：`u_H=16*S_H/B_H^2`、`ell_H=(W_H+E_H)/B_H^2` とすると、既存の真正 `B_H^2>0` より **`u_H+ell_H=1`**, **`0≤ell_H<1`**, **`B_H^2<272*S_H ↔ ell_H<16/17`**。この `u_H` は元のFC envelopeで割った割合であり、全分散で割る別の分率と混同しない。
- **本来のGI平均証明書との重要な区別**：ACPの真正高次Haar残差条件とADCの厳密な `(exp(64*b0)−1)^2=1/4` により、**`Budget_H>0 ↔ W_H<256*S_H`**、**`Budget_H≤0 ↔ 256*S_H≤W_H`** を追加形式化。つまり `W_H+E_H<256*S_H` はFC envelopeを通じた**より強い十分条件**であり、FC証明書の不成立からGI平均証明書の不成立は推論できない。GI平均証明書の非正値を実際の符号付き物理GIの消滅と同一視しない。
- **条件付きの実GI伝播**：真正数値条件 `W_H+E_H≤θ*S_H` と `θ<256` が別途検証されれば、元のFC厳密閾値、正の平均二乗GI証明書、さらに真正pair-Haar正測度の開集合上で元の符号付き二posterior GI応答が非零であることが既存ADE・ACOから従う。非正の平均証明書から `256*S_H≤W_H+E_H` が必要であることも証明。ただし、この相対残差・slack条件を無条件に得たわけではない。

### exact-source CIと公理依存の監査

- 新規ファイル `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullMomentFCVarianceSlackV5_PZ37AEY.lean`（267行）だけを追加、公開13定理・13件の `#print axioms` を検証。既存Leanファイル、元の物理モデル、測度、距離、公開root、workflowは不変更。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。
- 最終 [exact-source CI #41634463383](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41634463383) は **11,306/11,306 SUCCESS**。公開13定理の公理依存は **`propext`・`Classical.choice`・`Quot.sound`のみ**、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。
- 修正版source HEAD `191af9c5f6b51aa7b03f1b0e5d2216bed2d5ffb5`、GitHub test-merge `8e7a9f66ddac567719d0c6ef13781033c4242f04`、squash `753e32f213470ccd4df7355339efa2069569482b` のGit treeは **`c6758b211efa3b083efa3109791668bda4a097e3` で完全一致**。
- **Lean4修正理由**：初回CI #41633581758で `rw [add_div]` が等式の左辺にある内側の加法分数を先に書き換えて未解決ゴールを残した。変更Lean全文・依存元・elaboration goalを確認し、両辺を一括正規化する `simp only [add_div]` に変更。数学的な仮定・結論は弱めていない。docs-onlyのStrict Lean再実行は不要。

### AEX no-goの保持と未解決の数値境界

AEXが示した無条件の `¬(B_H^2<272*P_H(a,R))` は元のAEW保守的二球モーメント下界 `P_H` に限定され、AEYでもそのまま成立する。一方 `P_H≤S_H` により、真の全モーメントの `B_H^2<272*S_H` は未決着。今後は同じ元Wilson kernel・中心化source・transferに由来する **`W_H/S_H` と `E_H/S_H` の真正定量制御**が課題。各有限体積の無条件恒等式・正値はH一様の数値評価、物理Hamiltonianの必要スペクトルギャップ、連続体4D Yang–Mills質量ギャップを証明しない。

---

## 検証済み定理 — AEX（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AEX定理PR [#6259](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6259) はMERGED、squash SHA `5528fce1650e64b954994fa80fa77942a413b07a`。AEW以前の元の真正Wilson SU(2)、Gauss-law中心化物理源、元JQ受信器、Perron/transfer、SU(2) Haar・二境界pair-Haar、原距離、Lean/mathlib pin・公開rootを維持する。

### 重要な新規結果：AEWの保守的二球下界によるFC閾値認証は不可能

- **数値比較のauthority境界**：AEWが導出した正の半径・共分散半振幅安定性・元の共分散二乗モーメント`S_H`に対する二球下界は有効。ただし、二球**下界** `P_H(a,R)=(C_e(a)/2)^2 * 2*(min(R/(2*n_H+1),2)/4)^(8*n_H)` そのものを、元のFC envelope `B_H` に対する `B_H^2 < 272*P_H(a,R)` と比較する経路には構造的なno-goがある。ここで`n_H=card(Link_H)`、実際の物理リンク`e`が存在するため`n_H≥1`。
- **無条件の真正SU(2)点wise共分散FC bound**：元ACJの同じ共分散`C_e(a)`と同じFC envelope`B_H`について、`CompactEnergyMismatchMoment.four_covariance_sq_le_variance`と元ACAの真正受信器分散FC上界を組み合わせ、**`4*C_e(a)^2 ≤ B_H^2`** を新規公開Lean定理で再構成。ACJ内のprivate helperを不正に参照せず、既存Mathlib・物理機構から証明。
- **有限リンク球の幾何学的上限**：任意の`R≥0`、`n_H≥1`について **`(min(R/(2*n_H+1),2)/4)^(8*n_H) ≤1/256`**、従って真の二球Haar係数は高々`1/128`。これは小半径・大半径の区別なく成立する上限であり、`R_H`自体の存在・正値を妨げない。
- **証明書の定量的no-go**：二つを掛け合わせると、真正物理リンク`e`・任意の二境界`a`・任意の`R≥0`について **`272*P_H(a,R) ≤ (17/128)*B_H^2 ≤ B_H^2`**。従って **`¬(B_H^2 < 272*P_H(a,R))`** をLean4で無条件形式化。AEWが与える`a,M,R_H`の有効な正半径証拠と、このno-goが同時に成立することも公開定理として証明。
- **意味すること・意味しないこと**：AEWの**特定の保守的二球下界**をそのまま使ったGI正値十分条件は到達不能。しかし真正**全二乗モーメント`S_H`** の数値比較 `B_H^2 < 272*S_H`、本来の物理GI、非零共分散、既存の正領域、有限体積強制性そのものの不可能性は主張しない。なぜなら元の`S_H`は二球下界より大きくなり得るためである。元のHamiltonian spectral gap・体積一様強制性・連続体Yang--Mills質量ギャップは未証明。

### exact-source Lean4検証

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTwoBallFCNumericalObstructionV5_PZ37AEX.lean` だけを追加。公開6定理、6件`#print axioms`。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。既存Leanファイル・元物理模型・測度・距離・workflow・公開root変更なし。
- 最終 [exact-source CI #41630657809](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41630657809) は **11,305/11,305 SUCCESS**。新規6定理の依存公理は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。source HEAD `1a4516813c6a722739ee0b4868bab72afe085a4e`、test-merge `2ce0cd1566f6ac1b4032e8b63c4331d837608953`、squash `5528fce1650e64b954994fa80fa77942a413b07a` のGit tree `227102f4aed0f376e2cd98ce49625157debb6686`が完全一致。
- **Lean修正履歴**：初回は `rw [←pow_mul,pow_succ]` が目標の外側累乗ではなく内側の`x^8`を書き換え、未解決ゴールが生じた。全文と固定Mathlibの書換え機構・ACJ/ACA依存定義を点検し、外側`pow_mul`と`pow_succ`を明示的な別段等式に分けて修正。仮定も定理文も弱めず最終CIが成功。docs-only更新ではStrict Lean再実行なし。
- **次の研究 AEY**：元の二球局所質量を超える、真正`S_H`の全体評価、正規化された共分散エネルギー割合・分散／残差構造、FC envelopeとの直接比較を研究。AEWの球下界を改善しただけで閾値を満たせると仮定せず、未解決の数値・体積一様障害を保持する。

---

## 検証済み定理 — AEW（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AEW定理PR [#6256](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6256) はMERGED、定理squash SHA `add2cccca4683ab12d8830246a227989f3f9d203`。AEVまでの真正interacting Wilson SU(2)、元の中心化Gauss-law物理源、元JQ物理受信器、Perron/transfer、joint sqrt-density・元JQ密度、元のSU(2) Haarとpair-Haar法則、固定Lean/mathlib、公開rootは不変更。

### 元の真正受信器から共分散安定半径・Haar二球モーメントへの無条件接続

- **AEVの真正全境界Lipschitz係数を統合**：`O_H` を元の有界連続受信器、`M_F(H)=||O_H||`、`M_src(H)=∫|f0|dμ_H`、`a_H=||T_H||^(-2)`、`lambda_rho(H)=sqrt(k_H^3)`、`L_rho(H)=13*beta0*exp(13*beta0)*sqrt((k_H^(-1))^3)` とする。実際に証明済みの `L_left=M_F*L_rho/lambda_rho+2*M_F`、`L_right=(a_H*13*beta0*M_src+M_F*L_rho)/lambda_rho+2*M_F` から、明示的な本来の`L_F(H)=L_left+L_right≥0` を定義。元受信器と真正SU(2) Haar共分散分子に対して **`|F_e(z,xi)-F_e(w,xi)|≤L_F(H)*D_H(z,w)`**、**`|N_e(z)-N_e(w)|≤L_F(H)*D_H(z,w)`** を外部受信器正則性仮定なしで形式化。
- **AEKの真正密度下界を使用**：元のWilson kernel global floor `k_H>0` に対して **`lambda_q(H)=1/sqrt((k_H^(-1))^3)>0`** が全ての元二境界配置 `z` について `lambda_q(H)≤q_H(z)` であることを形式化。以前の密度net・自由な正数証明書を追加しない。
- **明示的な真正安定半径**：元の正共分散中心 `a`（`C_e(a)>0`）と本物のHaar分子絶対値上界 `M≥0`（`|N_e(z)|≤M`）に対し、`L_q(H)=13*beta0*exp(13*beta0)*exp(beta0*ActionBudget(H))/sqrt(k_H^3)` とすると **`R_H=min((lambda_q*C_e(a)/4)/(L_F+1), 1, (lambda_q^2*C_e(a)/(4*(M+lambda_q)))/(L_q+1))>0`** を新規定理で得る。数学的対象は既存AER/AESの元の共分散で、異なるsource・law・metricではない。
- **共分散半振幅安定性と真正pair-Haar二球下界**：任意の本来の二境界配置 `z,w` に対し `D_H(z,w)<R_H` なら **`|C_e(z)-C_e(w)|≤C_e(a)/2`**。さらに **`(C_e(a)/2)^2 * [2*(min(R_H/(2*card(Link_H)+1),2)/4)^(8*card(Link_H))] ≤ S(H,beta0,e)`** を無条件接続。ここで `S` は元の中心化共分散二乗モーメント。元のpair-HaarとSU(2) character `|chi|≤1` のみ使用。
- **各物理リンクでの存在を無条件化**：AEDの `p4Q2PZ37AED_originalPositiveMaximumCovariance_exists` とAEGの `p4Q2PZ37AEG_originalNumerator_positiveMaxAbs_exists` を合成し、全ての真正リンク`e`で正中心`a`、真の分子上界`M>0`、表示公式を満たす`R_H>0` と真正二球モーメント下界の存在を新しいLean4定理にした。`M` と`a`の数値認証を済ませたとの主張ではない。
- **真のGI/FC数値条件を分離**：既存の物理FC-envelope `B_H` に対し `B_H^2 <272 * [明示的二球下界]` が独立に確認できれば、元のGI平均予算`Budget(H,beta0,e)>0`を導く定理も追加。**この数値不等式の成立自体は未証明**であり、H一様強制性、物理Hamiltonian spectral gap、無限体積・連続体Yang--Mills質量ギャップは未証明のまま保持。

### exact-source Lean4検証・公理監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalReceiverExplicitCovarianceBallV5_PZ37AEW.lean` のみ。明示係数定義1件、公開7定理と7件`#print axioms`。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。既存Leanファイル、物理模型、CI/workflow、公開rootを不変更とする。
- [exact-source CI #41627473372](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41627473372) は **11,304/11,304 SUCCESS**。新規7定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。source HEAD `38789b124394edf74d7139db99ce89a449462afe`、test-merge `eeb79df229e21cd469819279c1adb697fb0e8245`、squash `add2cccca4683ab12d8830246a227989f3f9d203` のGit tree `5d16ffd52bab86b190e5f6b4211640f007af0d60` が完全一致。
- **Lean4検証理由**：AEU・AEVで導出済みの完全左・右境界係数を原定義のまま再利用し、AEKの真正q下界、AES/AERの半振幅半径定理、AEDの正共分散anchor、AEGの真のHaar numerator boundと接続。新規外部正則性仮定や数値GI仮定の無条件化を行わず、型付きsourceと既存証明のauthority境界を維持。docs-onlyではStrict Leanを再実行しない。
- **次の研究 AEX**：AEWで確立した半径と下界を、真正FC envelopeとの数値優越比較、およびH依存係数の非一様性の定量評価へ進める。両者を混同せず、H一様強制性・連続体質量ギャップへの飛躍は行わない。

---

## 検証済み定理 — AEV（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AEV定理PR [#6253](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6253) はMERGED、定理squash SHA `565a88c536b35063e62eb452b1d06b382b43e667`。AEUまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、元JQ受信器、元Perron/transfer、真正joint sqrt-density・JQ密度、元のSU(2) Haarとpair-Haar、固定Lean/mathlib・公開rootは不変更。

### 真正Wilson源積分から右非観測リンク係数を無条件導出し、受信器全境界Lipschitzを閉じる

- **元の符号付き物理源を保持**：`f0=p4Q2PZ37ZW_originalCenteredPhysicalDirection(H)`（真正Gauss-law Hilbert源）、本物の規格化spatial-slice Haar `mu_H` とone-slab Wilson核 `K_H(A,B)`を使用。`M_src(H)=∫ |f0(A)| dmu_H(A)≥0` は元の物理L²源の有限なHaar L¹質量であり、代理source・positive surrogate・独立posteriorではない。
- **真の核と符号付き積分の局所変動**：既証明AEM/AEOの物理一スラブWilson作用 `|S_H(A,B[i:=g])-S_H(A,B[i:=h])|≤13*d_J(g,h)`、Boltzmann核 `|K_H(A,B[i:=g])-K_H(A,B[i:=h])|≤13*beta0*d_J(g,h)` を継承。汎用の符号付き被積分関数について `|∫f*u-∫f*v|≤C*∫|f|` をLeanで証明し、GNの真の転送積分 `t_f0(B)=∫K_H(A,B)f0(A)dmu_H(A)` に適用。従って **`|t_f0(B[i:=g])-t_f0(B[i:=h])|≤13*beta0*M_src(H)*d_J(g,h)`** を外部変動仮定なしで形式化。
- **右境界のtyped gluing**：ADL全境界距離では単一右リンクだけの二つの置換に対し `D_H((A,B[i:=g]),(A,B[i:=h]))=d_J(g,h)`。右非観測リンク `i≠e` と受信器挿入リンク `e` の更新が可換であることを真正依存型のままLeanで証明。AETの右観測リンク `e` そのものの厳密な受信器不変性も継承。
- **真の分母と振幅上界による右係数**：`a_H=||T_H||^(-2)`、`M_F(H)=||O_H||`、AEKの `lambda_rho(H)=sqrt(k_H^3)>0`、AEQの `L_rho(H)=13*beta0*exp(13*beta0)*sqrt((k_H^(-1))^3)`、`L_T(H)=13*beta0*M_src(H)` を使用。真正GNの `F_e(A,B;xi)=a_H*t_f0(B[e:=xi])/rho_H(A,B[e:=xi])` にAEFの商評価を適用し、右非観測リンクの`d_J≤1`について `L_R,unit(H)=(a_H*L_T(H)+M_F(H)*L_rho(H))/lambda_rho(H)` を無条件に導出。
- **全弦距離・全境界の最終閉包**：`d_J>1` は真のBCF振幅上界 `2*M_F(H)` で処理し、**`L_right(H)=L_R,unit(H)+2*M_F(H)≥0`**。AEUの左係数 `L_left(H)=M_F*L_rho/lambda_rho+2*M_F` とAETの有限リンクgluingから、任意の元境界ペア `z,w`、元SU(2)挿入 `xi`、物理受信器リンク `e` について **`|F_e(z,xi)-F_e(w,xi)|≤(L_left(H)+L_right(H))*D_H(z,w)`** を無条件に形式証明。さらに元のSU(2) Haar character `|chi|≤1` を介し、元の中心化共分散分子 `N_e` にも同じ全境界Lipschitz係数を無条件に得る。
- **authority/obstruction**：今回閉じたのは有限体積 `H` ごとの元の物理受信器・真正Haar分子の定量正則性であり、係数は `H` に依存する。AEK/AEQ/AEF/AER/AESとの共分散局所安定性・正の二球モーメント接続は可能だが、元の数値GI/FC閾値の成立、体積一様強制性、無限体積の物理spectral gap、連続体Yang--Mills質量ギャップは未証明。

### exact-source Lean4検証・公理監査

- 新規2ファイル `PhysicalYangMillsWilsonSU2OriginalReceiverRightBoundaryTransferKernelSlopeV5_PZ37AEV.lean`、`PhysicalYangMillsWilsonSU2OriginalReceiverRightBoundaryExplicitFullSlopeV5_PZ37AEV.lean`（ともに `MGAP4D/MathlibAnalytic/`）を追加。公開13定理と13件`#print axioms`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。既存Leanファイル、模型、workflow、公開root不変更。
- [exact-source CI #41625031361](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41625031361) は **11,303/11,303 SUCCESS**。新規13定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error **0/0**、独立MCP completion receipt **SUCCESS**。最終source HEAD `979f6bafad3a3bb5153e649ab791a0cc27dd2b63`、test-merge `20b0a63c1ddefdc4bfd3f0a916d0e9be9c9ef624`、squash `565a88c536b35063e62eb452b1d06b382b43e667` のGit tree `af143c17dad2398ce55f7c2a44136454b200deea` は完全一致。
- **Lean4修正履歴**：CIの指摘箇所だけでなく新規Leanファイル全文、GN・AEM・AEK・AEQ・AEU・AEF・AESの依存型と固定mathlibを照合。`mul_le_mul_of_nonneg_left` が返す `|f|*C` と目標の `C*|f|` はLeanの構文上definitional equalではないため、`calc`と可換環の `ring` で明示的に接続。全13定理を維持し、最後の未使用`simp`引数を削除。docs-only同期ではStrict Leanを再実行しない。
- **次段階 AEW**：証明済みの真正全境界受信器係数をAES/AERの具体的安定半径と元の共分散二球モーメントへ完全接続する。有限体積 `H` と `H` 一様数値証明は引き続き分ける。

---

## 検証済み定理 — AEU（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AEU定理PR [#6250](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6250) はMERGED、定理squash SHA `7c784c332db9feeb078d24c051b7ddce0f411952`。AETまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、元JQ受信器、元Perron/transfer、真正joint sqrt-density・JQ密度、元のSU(2) Haarとpair-Haar法則、固定Lean/mathlibおよび公開rootは不変更。

### 真正物理受信器の左境界全リンク変動係数を無条件に導出

- **GNの真正源・密度相殺式**：元の中心化Gauss-law源`f0`と真正SU(2)積分変数`xi`に対し、元JQ受信器は **`F_e(A,B;xi)=||T_H||^(-2)*t_f0(B[e:=xi])/rho_H(A,B[e:=xi])`** と厳密に等しい。`t_f0`は変更されていないone-slab Wilson transfer源積分であり、左境界`A`には依存しない。新しい確率法則・源・受信器の再定義は行わない。
- **真の受信器の絶対振幅上界**：`O_H=normalizedPhysicalOneSlabJointReceiverProductBCF(H,2,beta0,f0)`は既存の真正有界連続BCF。`M_F(H)=||O_H||≥0`とすると、全ての元`A,B,e,xi`で **`|F_e(A,B;xi)|≤M_F(H)`** をLean4で無条件証明。コンパクト性から数値を創作せず、元BCF自体の実在するnormを使用。
- **本来の左1リンク距離**：元のADL全リンク二境界弦距離`D_H`は、左リンク`i`のみの二つの置換では厳密に **`D_H((A[i:=g],B),(A[i:=h],B))=d_J(g,h)`**。代理擬距離・外部測度は不要。
- **本来の左境界・短距離商変動**：AEKの真正Wilson joint sqrt-density下界`lambda_rho(H)=sqrt(k_H^3)>0`、AEQの`D_H≤1`での真正密度係数`L_rho(H)=13*beta0*exp(13*beta0)*sqrt((k_H^(-1))^3)`を使用。同じ右挿入境界を持つ二つの元受信器では転送積分分子が同一なので、分母の商差から`d_J(g,h)≤1`なら **`|F_e(A[i:=g],B;xi)-F_e(A[i:=h],B;xi)|≤(M_F*L_rho/lambda_rho)*d_J(g,h)`** を無条件形式化。
- **元の左全リンク・全距離の明示的Lipschitz**：`d_J>1`では真のBCF振幅上界から`|F_g-F_h|≤2*M_F≤2*M_F*d_J`。従って任意の元左リンクについて **`L_left(H)=M_F(H)*L_rho(H)/lambda_rho(H)+2*M_F(H)`** が実際に有効な有限体積正則性係数として成立。数値評価済みの`M_F`やH非依存係数を主張するものではない。
- **AETと接続して右側だけを残す**：観測右リンク`e`の独立性はAETで無条件証明済み。残る右**非観測**リンク`i≠e`の真正局所係数`L_R≥0`だけを証明書として仮定すれば、元の全境界で **`|F_e(z,xi)-F_e(w,xi)|≤(L_left(H)+L_R)*D_H(z,w)`**。これをAESの`|chi|≤1`、AERの真正Haar二球モーメントへ接続可能。右非観測リンクの係数`L_R`の存在・数値評価と体積一様性はAEUでは未証明として明示。
- **authority/obstruction**：左境界全リンク係数は無条件の定理、右観測リンクの零変動も無条件。右非観測リンクの元のWilson transfer源積分・密度比の局所変動こそが次段階AEVの課題。GI数値FC閾値、体積一様強制性、物理スペクトルギャップ、連続体Yang--Mills質量ギャップは未証明。

### exact-source Lean4検証・公理監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalReceiverLeftBoundaryExplicitSlopeV5_PZ37AEU.lean` のみ。公開7定理と7件`#print axioms`。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`固定。既存Leanファイル、物理模型、workflow、公開rootを不変更とする。
- [exact-source CI #41616736179](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41616736179) は **11,301/11,301 SUCCESS**、新規7定理の公理依存は`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。最終source HEAD `bb13a0979d6c04b0e9aec3f9d17dd389719954c3`、test-merge `ce7ff95c0970b92dcc5f7c82c5d7bf728a13face`、squash `7c784c332db9feeb078d24c051b7ddce0f411952` のGit tree `414fdc0ef7d4d2d27f665f0b7f5ddc5ae9be2baf` は完全一致。
- **Lean4修正履歴**：新規ファイルの全文とGN・AEK・AEQ・AETの依存定理を照合。局所notationを`dsimp`の書換え定理として渡せない理由を確認し、目標の`change`と正値因子の明示的積へ置換。`abs_sub_le`の3点不等式型を確認して`abs_add_le`へ修正。SU(2)のリンク変数`h`と証明名のshadowingを解消。新たな仮定を導入せず定理文を保持。docs-only同期ではStrict Leanを再実行しない。

---

## 検証済み定理 — AET（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AET定理PR [#6247](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6247) はMERGED、定理squash SHA `89ae225820b8eb7c37ce4ae0cfb4fb5659600111`。AESまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、元JQ source-link receiver、元Perron/transfer、真正joint sqrt-density・JQ密度、元SU(2) Haarとpair-Haar、固定Lean/mathlib・公開rootは不変更。

### 真正受信器の正確な右リンク独立性・全リンクLipschitz descent

- **無条件の元物理受信器不変性**：JQの受信器は元の中心化Gauss-law源 `f0` から作られ、`F_e(A,B;g)=normalizedPhysicalOneSlabJointReceiverProductBCF(A,Function.update(B,e,g))` を使う。したがって任意の真正SU(2) `h,g` に対し **`F_e(A,Function.update(B,e,h);g)=F_e(A,B;g)`** をLean4で証明。積分変数`g`で上書きされる前の右境界リンク`B(e)`の値に関する厳密な独立性であり、受信器全体の右境界独立性ではない。
- **真正SU(2) Haar分子の同一性**：元の分子 `N_e(A,B)=∫_SU2 F_e(A,B;g)*chi(g)dmu(g)` についても **`N_e(A,Function.update(B,e,h))=N_e(A,B)`** を無条件に証明。これは元Haar積分の値を変えないもので、分母`q_H`や商の共分散`C_e=N_e/q_H`が`B(e)`に依存しないとの主張ではない。
- **符号付き有限座標Lipschitz gluing**：AEPの真正finite-two-boundary exponential Harnack telescopeを`exp(f)`へ適用し、局所的`|f(update_i(g))-f(update_i(h))|≤L*d(g,h)`から、二境界全有限座標について`|f(z)-f(w)|≤L*sum_i(d(z.left_i,w.left_i)+d(z.right_i,w.right_i))`を証明。元の符号付き`f`に非負性を仮定せず、幾何学的`d`の対称性のみ使用。
- **本物の受信器への適用**：元のADK弦距離`d_J`・ADL全リンク距離`D_H`を保持する。全左リンクと、右側について**観測リンクe以外**の各リンクで同一の局所変動係数`LF≥0`が証明されれば、右eの局所評価は上書き不変性から`0`で自動的に解決し、**`|F_e(z,g)-F_e(w,g)|≤LF*D_H(z,w)`** を導く。AESの証明済み`|chi|≤1`から`|N_e(z)-N_e(w)|≤LF*D_H(z,w)`も導く。
- **AER・AESの定量的結論を継承**：真正`C_e(a)>0`、既存`lambda>0`・`M≥0`、元密度係数`Lq(H)`と局所受信器係数`LF`の証明書を入力すると、`R=min((lambda*C_e(a)/4)/(LF+1),1,(lambda^2*C_e(a)/(4*(M+lambda)))/(Lq(H)+1))>0`が元の共分散半振幅安定性と真正pair-Haar二球モーメント下界を与える。
- **authority/obstruction**：右`B(e)`独立性、有限座標の加法的gluing、条件付きAER/AES接続は形式証明済み。ただし**それ以外の元物理受信器の各リンク`d_J`変動係数`LF`はまだ無条件に証明・数値評価されていない**。したがってこの局所証明書を無条件で使えるとは主張しない。有限体積`H`の正半径存在はAERで別途証明済み。GI数値閾値、体積一様強制性、物理spectral gap、連続体Yang--Mills質量ギャップは未証明。

### exact-source Lean4検証・公理監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalReceiverLocalToGlobalChordalV5_PZ37AET.lean` のみ、公開7定理と7件`#print axioms`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、既存Leanファイル、物理模型、workflow、公開rootは不変更。
- [exact-source CI #41613092993](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41613092993) **11,300/11,300 SUCCESS**、新規7定理の公理依存は`propext`・`Classical.choice`・`Quot.sound`以内、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。最終source HEAD `cc1ff43e62f696eddba29515e69fd37a9efe6d0d`、test-merge `50b1d26ad959089c2b635dae5b7cd82bbcebcac3`、squash `89ae225820b8eb7c37ce4ae0cfb4fb5659600111` のGit tree `7389cf9c2786a7bd3f0ec9bf82fa731ce3af145a` は完全一致。docs-onlyではStrict Lean再実行不要。
- **次の段階 AEU**：元の中心化Wilson物理源・one-slab kernel・Perron因子の構造から、残る左リンクと右非観測リンクに対する本物の局所受信器変動を定量化する。有限体積ごとの局所係数の構成と体積一様上界を区別する。

---

## 検証済み定理 — AES（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AES定理PR [#6244](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6244) はMERGED、定理squash SHA `3d28af0d38e6832597fed74d4050c545ae0d9f97`。AERまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、JQの真正source-link receiver、元Perron/transfer、二境界joint sqrt-density・JQ密度、元のSU(2) Haarおよびpair-Haar、固定Lean/mathlibと公開rootは不変更。

### 真正物理受信器から元Haar分子・共分散安定半径への明示的接続

- **元Wilson characterの無条件数値上界**：元の実SU(2) character `chi(g)=1-specialUnitaryWilsonPlaquetteEnergy(2,g)`。既存のWilsonエネルギー `0≤E(g)≤2` から **`|chi(g)|≤1`** を新たにLean4形式証明。補助的に真のコンパクトSU(2)上の連続character norm `||chi||_sup<∞` もLeanで証明済み。代理character・代理群は使わない。
- **Haar分子の真の物理的同一性**：元の中心化Gauss-law Hilbert源 `f0` のJQ受信器 `F_e(z,g)=p4Q2JQ_originalPhysicalSourceLinkReceiver(H,beta0,f0,e,z,g)` と元のSU(2) normalized Haar `mu` に対し、元AEFの**真正分子**を `N_e(z)=∫ F_e(z,g)*chi(g) dmu(g)` のまま使用。点ごとの受信器変動 `|F_e(z,g)-F_e(w,g)|≤LF*D_H(z,w)` が認証されれば、`|chi|≤1` と元Haar確率性から **`|N_e(z)-N_e(w)|≤LF*D_H(z,w)`** を形式証明。符号・独立性の仮定は不要。
- **AERのrNの定量的明示式**：真正共分散正中心 `C_e(a)>0`、AEGの元密度下界 `lambda>0`、元分子上界 `M≥0`、AEQの明示的元密度係数 `Lq(H)=13*beta0*exp(13*beta0)*Mq(H)`、元受信器変動の認証係数 `LF≥0` を使用。`rN=(lambda*C_e(a)/4)/(LF+1)`、`deltaq=lambda^2*C_e(a)/(4*(M+lambda))`、`R=min(rN,1,deltaq/(Lq(H)+1))>0` と定義し、全ての元境界ペア `D_H(z,w)<R` に対し **`|C_e(z)-C_e(w)|≤C_e(a)/2`** を証明。
- **真正pair-Haar二球モーメント**：同じ元の `D_H` と元pair-Haar法則・元ゲージ符号反転を保持し、`(C_e(a)/2)^2 * 2 * (min(R/(2*card(Link_H)+1),2)/4)^(8*card(Link_H)) ≤ S(H,beta0,e)` を形式証明。元FC envelopeによるGI mean positivityは別途数値優越条件を明示した**条件付き**結論。
- **authority/obstruction**：`|chi|≤1` は無条件証明。一方 **真正JQ物理受信器のD_H-Lipschitz係数LFの実在・数値値はAESでは未証明**。従って、ここで与えた`R`は受信器認証に依存する明示式であって、数値的に確定した半径ではない。AERの定性的な正半径存在定理とは区別する。`lambda`、`M`、`C_e(a)`、`Lq(H)` の数値評価、GI数値閾値、体積一様強制性、物理スペクトルギャップ、連続体4D Yang--Mills質量ギャップは引き続き未証明。

### exact-source Lean4・公理監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalReceiverToNumeratorExplicitRadiusV5_PZ37AES.lean` 1ファイル、9公開定理・9件の`#print axioms`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、旧Lean全ファイル・物理模型・workflow・公開rootは不変更。
- [exact-source CI #41610291228](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41610291228) は**11,299/11,299 SUCCESS**。新規9定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。最終source HEAD `754d55794f463efd377a1ebf3656132e64fbca32`、test-merge `61f4a7e4b95f3632c593566034bd92596e823a7b`、squash `3d28af0d38e6832597fed74d4050c545ae0d9f97` のGit tree `564b4133acc978813d58afb3aa616dcedb76e4e6` は完全一致。
- **Lean4修正履歴**：絶対値・乗算間の字句解析（`|x| * |y|`）、局所notation`mu`の`.real`非展開に対する明示的`(normalizedCompactHaar G).real`、半径等式を前提に書き戻す`rw`、未使用証明引数の命名を修正。数学的仮定と結論は維持。次は元JQ受信器`F_e`の`LF`を真正Wilson核・連続Perron・中心化物理源から構成することが中心課題。docs-onlyではStrict Lean再実行不要。

---

## 検証済み定理 — AER（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AER定理PR [#6241](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6241) はMERGED、定理squash SHA `a5eb1ff0fa4bf1c6544df12a6c43271b092353aa`。AEP/AEQまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、元のFF受信器、Perron/transfer作用素、二境界joint sqrt-density、JQ密度、元のpair-Haar、固定Lean/mathlibおよび公開rootは不変更。

### 元の共分散 C_e=N_e/q_H の半振幅安定球

- **分母の明示的な真正評価**：AEQから、元の全リンク二境界弦距離 `D_H(z,w)≤1` で `|q_H(z)-q_H(w)|≤L_q(H) D_H(z,w)`、`L_q(H)=13*beta0*exp(13*beta0)*M_q(H)`。AEPの対数係数 `13*beta0` はH非依存だが、ここで使う絶対変動係数 `L_q(H)` はH依存。
- **分子・分母の真正予算**：元の物理リンク `e`、正の共分散中心 `a`、AEGの元密度下界 `lambda>0`、真正Haar分子 `N_e` の有限体積上界 `M≥0`、分子誤差 `lambda*C_e(a)/4` に対する真正 `D_H` 半径 `r_N>0` を使う。`delta_q=lambda^2*C_e(a)/(4*(M+lambda))`、`R=min(r_N,1,delta_q/(L_q(H)+1))>0` を定義。
- **新たに無条件形式化**：元の `q_H` にAEQ明示的変動を代入し、AEFの真正比率誤差則から、すべての元境界 `z,w` で `D_H(z,w)<R` なら `|C_e(z)-C_e(w)|≤C_e(a)/2`。AEGは真正 `r_N` の存在を、AEDは正の真正 `C_e(a)` の存在を証明済み。したがって任意の固定有限 `H` と真正物理リンク `e` について、この形式の正の半径が無条件に存在する。
- **元Haar二球モーメントへの接続**：AEEのゲージ反転・両符号球の証明を同じ元の `D_H` と元pair-Haar測度で再利用し、`(C_e(a)/2)^2 * 2 * (min(R/(2*card(Link_H)+1),2)/4)^(8*card(Link_H)) ≤ S(H,beta0,e)` を形式証明。代理測度、独立posterior、物理的源・受信器の交換を行わない。
- **authority/obstruction**：`r_N`、`lambda`、`M`、`C_e(a)`、`M_q(H)` は存在が証明された真正有限体積量だが、数値評価されていない。`R` はそれらを入力する明示式であり、特定の数値半径や体積一様正下界を算出したものではない。GIのFC数値優越、体積一様強制性、物理スペクトルギャップ、連続体4D Yang--Mills質量ギャップは未証明。

### exact-source Lean4検証・公理監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCovarianceCertifiedChordalBallV5_PZ37AER.lean` のみ、公開5定理と5件の `#print axioms`。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。旧Leanファイル、物理模型、workflow、公開root不変更。
- [exact-source CI #41605787162](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41605787162) **11,298/11,298 SUCCESS**、公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。最終source HEAD `5ded878cab71a0dea3283a91225d390f05c9ad7e`、test-merge `1f66b1b092e9505079cfc583032ab10164ddd472`、squash `a5eb1ff0fa4bf1c6544df12a6c43271b092353aa` のGit tree `5384861ef3a689c15459ef11ec9f9a63a9dbcdfb` は完全一致。
- **修正履歴**：初回CIの半振幅 `C_e(a)-C_e(a)/2=C_e(a)/2` はLeanの定義上の一致ではなく実数環の等式なので `ring` で明示証明。既にゴールを閉じる `field_simp` 後の不要な `ring` を除去し、定理の仮定・結論は維持。次段階は真正分子 `N_e` のSU(2)リンク依存の明示的変動定数、有限Hでの数値認証、および物理的FC比較。docs-only同期ではStrict Leanを再実行しない。

---

## 検証済み定理 — AEQ（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AEQ定理PR [#6238](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6238) はMERGED、定理squash SHA `1ea9d87d6973035c6fc197a8a1c2176f4c1b80d4`。AEPまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、元Perron/transfer、真正joint sqrt-density・JQ密度・境界pair-Haar、固定Lean/mathlibと公開rootは不変更。

### 真正二境界・全リンクD_Hの明示的絶対変動と球内Lipschitz

- **前提を追加しない全リンク変動評価**：AEPの無条件相対Harnack `rho_H(z)≤exp(c*D_H(z,w))*rho_H(w)`、`q_H(z)≤exp(c*D_H(z,w))*q_H(w)`（両者の逆方向も成立）を使用。ここで `c=13*beta0` はH非依存、`D_H` はADLの元の二境界全リンクℓ1弦距離。AEKの真正物理的振幅天井 `M_rho(H)=sqrt((k_H⁻¹)^3)`、`M_q(H)=exp(beta0*B_H)/sqrt(k_H^3)`（`k_H=exp(-beta0*B_H)>0`、`B_H` は元のone-slab Wilson全作用budget）をそのまま使用。
- **新たにLean4で無条件証明**：すべての実在有限Hの元境界ペア `z,w` に対して **`|rho_H(z)-rho_H(w)|≤(exp(c*D_H(z,w))-1)*M_rho(H)`** および **`|q_H(z)-q_H(w)|≤(exp(c*D_H(z,w))-1)*M_q(H)`**。代理密度、独立性、有限net標本、H一様振幅仮定は導入しない。
- **半径指定の数値Lipschitz**：実指数の標準接線不等式から `exp(x)-1≤x*exp(x)` を証明。任意の元距離 `D_H(z,w)≤R` について、**`|rho_H(z)-rho_H(w)|≤c*exp(c*R)*M_rho(H)*D_H(z,w)`** および **`|q_H(z)-q_H(w)|≤c*exp(c*R)*M_q(H)*D_H(z,w)`** を形式証明。Rの大きさに応じて係数を明示でき、AEHの定性的な一様連続性だけに依存しない。
- **authority/obstruction**：AEPの `log rho_H`・`log q_H` のH非依存係数 `c` と区別し、AEQの絶対変動振幅 `M_rho(H),M_q(H)` は有限体積Hに依存すると明示。今回の定理から源依存共分散のD_H安定球、GI 68/1:17閾値、体積一様強制性、物理スペクトルギャップ、連続体Yang--Mills質量ギャップの証明は主張しない。

### exact-source Lean4検証・公理監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullChordalExplicitDensityModulusV5_PZ37AEQ.lean` 1ファイル、6公開定理・6件 `#print axioms`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。既存Leanファイル、物理模型、workflow、公開rootは不変更。
- exact-source [CI #41601402216](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41601402216) は **11,297/11,297 SUCCESS**。新規6定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` 以内、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。最終source HEAD `095f9bf3f0734f0f30c92c9aa55fe78dc7e70ab7`、squash `1ea9d87d6973035c6fc197a8a1c2176f4c1b80d4` のGit tree `752a6ac497e116ebf16f1f6e070918c3102522a5` は完全一致。
- **次の段階**：元のsource-dependent共分散 `C_e` の真正D_H球内の定量的安定性を分離して形式化し、明示的なHaar球測度下界と二球モーメントのpositive witnessに接続する。体積一様強制性・連続体4D質量ギャップは引き続き未証明。今回のREADME・ROADMAP同期はdocs-onlyでStrict Leanを再実行しない。

---

## 検証済み定理 — AEP（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AEP定理PR [#6235](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6235) はMERGED、squash SHA `a79302bf97a7e3ab5127b46971a01dfddb9d9ee3`。AEOまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、元Perron/transfer、二interacting posterior、元境界pair-Haar、固定toolchainおよび公開rootを不変更に保つ。

### 全リンク有限telescopingと元の二境界弦距離D_H

- **有限座標の型付き経路**：原始的な有限リンク集合を `Finset` で走査し、`Function.update` による選択リンクの置換を累積する真正 `finiteBlend` を定義。空集合では元配置、全体集合では目標配置になることを関数外延性により証明。局所 `f(update(u,i,g))≤exp(c*d(g,h))*f(update(u,i,h))` から全有限座標の `f(a)≤exp(c*∑d(a_i,b_i))*f(b)` を帰納証明し、さらに二境界へ合成。新しい確率測度や密度の独立性は仮定しない。
- **真正二境界D_H**：ADLで確定した元の全リンク距離 `D_H(z,w)=∑_{e∈Link_H}(d_J(z.1_e,w.1_e)+d_J(z.2_e,w.2_e))` をそのまま使用。AEOの第二境界・第一境界の相対係数 `exp(13*beta0*d_J)` を順次合成し、元の `rho_H` と真正JQ `q_H` について、任意の元境界ペア `z,w` に対し **`rho_H(z)≤exp(13*beta0*D_H(z,w))*rho_H(w)`、`q_H(z)≤exp(13*beta0*D_H(z,w))*q_H(w)`** を無条件に形式証明。両式の逆方向も成立。
- **対数密度の数値Lipschitz係数**：元 `rho_H>0` は真正joint sqrt-density正値から、`q_H>0` はAEKの元Wilson密度下界から証明。全リンク両側指数比較の対数を取り、**`|log rho_H(z)-log rho_H(w)|≤13*beta0*D_H(z,w)`** および **`|log q_H(z)-log q_H(w)|≤13*beta0*D_H(z,w)`** を形式証明。係数 `13*beta0` は有限体積Hおよびリンク総数に依存せず、真正D_Hは全元リンクの距離を合算する。
- **同一性と境界**：元のJQ相殺式 `q_H(z)=‖T_H‖⁻¹/rho_H(z)` による二境界対称性もLean4で形式証明。元の物理真空・Wilson核・二interacting posterior・Haar法則を置換せず、全リンクLipschitzからH一様強制性・スペクトルギャップ・連続体Yang--Mills質量ギャップを導いたとは主張しない。

### Lean4 exact-source証明と記録監査

- 追加した真正Leanモジュールは `PhysicalYangMillsWilsonSU2OriginalFullChordalTelescopingV5_PZ37AEP.lean`、`PhysicalYangMillsWilsonSU2OriginalFullChordalDensityHarnackV5_PZ37AEP.lean`、`PhysicalYangMillsWilsonSU2OriginalFullChordalLogDensityLipschitzV5_PZ37AEP.lean` の3件、17公開定理・17件の `#print axioms`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- 最終exact-source [CI #41595248815](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41595248815) は **11,296/11,296 SUCCESS**、17定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` 以内、`sorryAx` なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。最終source HEAD `a797421515a9b793dc8a028645a8468e7cdfa32a` とsquash `a79302bf97a7e3ab5127b46971a01dfddb9d9ee3` のGit tree `9483d8719e6b70b88fc0ab8687245ff4e8469756` は完全一致。マージ後push CI [#41596154568](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41596154568) もSUCCESS。
- 初期CIで発見した `Finset` の空集合・全体集合の関数外延性証明、局所証明の型合わせ・linter問題を、全ファイルと既存の定理型を照合して修正。既存Lean、物理模型、公開root、workflow、toolchain pinは変更しない。README・ROADMAPの両ブランチ計4文書に同一の追記を行い、docs-onlyではStrict Leanを再実行しない。

### 次段階のobstruction

- 数値的に明示された全リンク対数Lipschitz係数から、真正 `rho_H`・`q_H` の有限Hの絶対変動上界、共分散 `C_e` の同じD_H球における安定性、元のHaar球質量とGI 68/1:17必要条件を結ぶ定量評価へ進む。有限体積の密度振幅の上界がH依存であること、および体積一様強制性・物理スペクトルギャップ・連続体4D質量ギャップが未証明であることを明記する。

---

## 検証済み定理 — AEO（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` はREADME・ROADMAP文書ミラーのみ。AEO定理PR [#6232](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6232) はMERGED、定理squash SHA `001cf697e13714e4bf194061312b35c7df63d61e`。AENまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、元Perron/transfer、二interacting posterior、元境界pair-Haar、固定toolchainと公開rootを不変更とする。

### 真正有限HのWilson作用・核・連続Perron真空の距離依存Harnack

- **実際の原始幾何**：AEMで確定した真正SU(2)弦距離 `d_J` と有限接続数により、1リンク置換 `B_g=B[e↦g]`・`B_h=B[e↦h]` で元空間Wilson作用差 `≤24*d_J(g,h)`、元時間crossing作用差 `≤d_J(g,h)`。対称一スラブ作用の絶対差 `|S_H(A,B_g)-S_H(A,B_h)|≤13*d_J(g,h)` をAEOで形式証明。
- **指数への真正移送**：元のBoltzmann式 `K_H(A,B)=exp(-beta0*S_H(A,B))` から、`R(g,h)=exp(13*beta0*d_J(g,h))` として `K_H(A,B_g)≤R(g,h)*K_H(A,B_h)` および逆方向を無条件に形式証明。元の正規化real-eight Wilson特徴における `R(g,g)=1`、Rの対称性および `R(g,h)≥1` を区別して保持。
- **真正物理Perron固有方程式**：元の非負Haar `L²` top eigenvector `V_H` と正の元transferノルム `lambda_H` を保持し、既存の厳密点ごと式 `lambda_H*Omega_H(B)=∫V_H(A)*K_H(A,B)dmu_H(A)` に積分単調性を適用。`Omega_H(B_g)≤R(g,h)*Omega_H(B_h)` と逆方向を形式証明。代理真空、独立性、新しい確率則、未知のH一様下界は仮定しない。

### 真正joint weight・rho・JQ qへの無条件相対比較

- **元joint weightの構造**：`W_H(A,B)=lambda_H⁻¹*Omega_H(A)*K_H(A,B)*Omega_H(B)` をそのまま使い、第二境界の1リンク置換で `W_H(A,B_g)≤R(g,h)^2*W_H(A,B_h)` と逆方向を証明。真正 `rho_H=sqrt(W_H)` について `rho_H(A,B_g)≤R(g,h)*rho_H(A,B_h)` と逆方向を証明。元Wilson核の二境界対称性により第一境界の同型比較も成立。
- **元JQ密度**：AEGの厳密相殺恒等式 `q_H(z)=lambda_H⁻¹/rho_H(z)` と真正rho正値を使い、`q_H(A,B_g)≤R(g,h)*q_H(A,B_h)` および逆方向を形式証明。真のinverse transfer、元の二interacting posteriorとpair-Haarを維持。
- **小距離に応答する絶対変動**：AEKの真正有限Hの大域上界 `M_rho(H)`・`M_q(H)` に基づき `|rho_H(A,B_g)-rho_H(A,B_h)|≤(R(g,h)-1)*M_rho(H)` とqの同型式を証明。`R-1→0` は弦距離とともに消えるが、上界M自体はH依存。AEL/ADLの真正1リンク校正 `D_H((A,B_g),(A,B_h))=d_J(g,h)` にも移送。**今回は任意の二境界配置を結ぶ全リンクtelescopingの形式証明までは含まない**。

### exact-source Lean4・公理監査・正本記録

- 新規Lean `PhysicalYangMillsWilsonSU2OriginalDistanceDependentKernelVacuumHarnackV5_PZ37AEO.lean` と `PhysicalYangMillsWilsonSU2OriginalDistanceDependentRhoPerronHarnackV5_PZ37AEO.lean` の2ファイル、21公開定理・21件の `#print axioms`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- 最終exact-source [CI #41590838422](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41590838422) は **11,293/11,293 SUCCESS**。全21件の依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立commit-status receipt SUCCESS。最終exact-source HEAD `0c797ee5a72dea6f0439739b3f09a5645329de76`、test-merge `4b979176a42fa6e385b2622ad2fd394cb7e6621a`、squash `001cf697e13714e4bf194061312b35c7df63d61e` のGit tree `c23d403ca8eb6d13f38762b684c16cb7beeb0152` は完全一致。既存Lean・物理模型・公開rootは変更なし。
- **次の数学的課題**：真正 `D_H` の全リンクtelescopingによるグローバルな相対比較・対数密度Lipschitzを導出し、真正共分散と二球モーメントの数値評価へ接続する。GI 68/1:17、H一様強制性、物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップは未認証・未証明のまま保持。文書同期はdocs-only、Strict Leanを再実行しない。

---

## 検証済み定理 — AEN（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main`はREADME・ROADMAP文書ミラーのみ。AEN定理PR [#6229](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6229)はMERGED、squash SHA `42e07b20ef8c39e9e031a709c1f520490fa75100`。AEMまでの真正interacting Wilson SU(2)、中心化Gauss-law物理源、元Perron/transfer、二interacting posterior、境界pair-Haar、固定toolchainおよび公開rootを変更しない。

### 真正Wilson核から元の連続Perron真空への小距離変動移送

- **元の固有方程式をそのまま使用**：実際の物理transferノルム `lambda_H=‖T_H‖`、真正非負規格化Haar `L²` 固有ベクトル `V_H`、元のspatial-slice Haar確率 `mu_H` と真正Wilson核 `K_H` に対し、既存の点ごと恒等式 `lambda_H*Omega_H(B)=∫V_H(A)*K_H(A,B)dmu_H(A)` を使用。AEMの定理 `|K_H(A,B_g)-K_H(A,B_h)|≤13*beta0*d_J(g,h)` は全ての元のAと任意の1リンク置換について無条件。
- **重み付き積分の一般補題**：元の非負 `V_H` と真の二核切片の可積分性から、積分の差分が `(13*beta0*d_J(g,h))*∫V_H dmu_H` 以下となることをLean4証明。AEKの `Omega_H≤k_H⁻¹` と元の連続真空のa.e.一致を使う粗い上界 `∫V_H≤k_H⁻¹` から、`|Omega_H(B_g)-Omega_H(B_h)|≤13*beta0*k_H⁻²*d_J(g,h)` を独立証明。
- **真正Haar L²規格化による改善**：Haar確率測度の定数1ベクトルの `L²` ノルムが1、元の規格化されたPerron固有ベクトルのノルムも1であることから、実Hilbert Cauchy–Schwarzにより **`∫V_H dmu_H≤1`** をLean4証明。AEJの真正 `lambda_H≥k_H>0` と組み合わせ、**`|Omega_H(B_g)-Omega_H(B_h)|≤13*beta0*k_H⁻¹*d_J(g,h)`** へ係数を改善。新規正則性・独立性・代理真空は仮定しない。
- **元の全二境界弦距離への校正**：AEL/ADLで証明済みの1リンク恒等式 `D_H((A,B_g),(A,B_h))=d_J(g,h)` を用いて両版の真正 `D_H` 一座標変動評価を形式証明。任意の二境界配置間を結ぶ全リンクtelescopingについては今後の拡張対象。

### 未証明境界と次の研究

- 係数 `13*beta0/k_H` は各有限Hで明示的であるが、`k_H` は元の全Wilson作用budgetに依存するので**体積一様Lipschitz係数とは断言しない**。次は元の `Omega_H` の変動を真正joint sqrt-density `rho_H` と厳密JQ `q_H` に移送する。さらにAEMの作用差分から小距離指数Harnack `exp(13*beta0*d_J)` を構成し、体積一様な相対比較を検討する。
- 元の源依存共分散のD_H安定球、GI 68/1:17、H一様強制性、物理スペクトルギャップと連続体4D Yang–Mills質量ギャップは未認証・未証明のまま維持する。

### exact-source Lean4検証と定理正本

- 新規Lean `PhysicalYangMillsWilsonSU2OriginalPerronOneLinkChordModulusV5_PZ37AEN.lean` および `PhysicalYangMillsWilsonSU2OriginalPerronSharpHaarL2ModulusV5_PZ37AEN.lean` の2ファイル、7公開定理・7件の `#print axioms`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- 最終exact-source [CI #41588933158](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41588933158) は **11,291/11,291 SUCCESS**。7/7件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。source/test-mergeファイル差分なし、最終source HEAD `dd64a4fbc6e223f2a2bc4d5f1ff069e351a25914` とsquashの新規2 Lean blobは完全一致。
- 初回CIのLean4関数加算の点ごと展開、局所notationをsimpへ与えた型エラー、`le_div_iff₀` の乗法順序を修正し、物理モデルや定理文の仮定は弱めていない。既存Lean・公開root・workflow・toolchain pinは不変更。README／ROADMAPは両ブランチ計4文書で同一の追記を保持し、docs-onlyでStrict Leanは再実行しない。

---

## 検証済み定理 — AEM（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。AEM定理PR [#6226](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6226) はMERGED、定理squash SHA `23ac7379b8f076c844c8f77245cc4849cc2610d4`。AELまでの元interacting Wilson SU(2)、centered Gauss-law物理源、元Perron/transfer、二interacting posterior、元boundary pair-Haar、固定toolchainおよび公開rootを不変更とする。

### 元の正規化SU(2)弦距離による無条件1リンクWilson核Lipschitz評価

- **真正Hilbert特徴から直接**：元のSU(2) normalized real-eight trace feature `J` と `d_J(g,h)=‖J(g)-J(h)‖` を保持し、`‖J(g)‖=1` と真正Cauchy–Schwarzより `|E(a⁻¹*g)-E(a⁻¹*h)|≤d_J(g,h)` をLean4証明。連続性を新規仮定するのではなく、元Wilson作用そのものから導出する。
- **群作用と原始4辺ホロノミー**：真正 `d_J` のSU(2)左・右乗法および逆元に関する不変性を証明。元の空間4辺plaquette holonomyは同じ1リンクの置換 `B_g=B[e↦g]`、`B_h=B[e↦h]` で `d_J(Hol(B_g,p),Hol(B_h,p))≤4*d_J(g,h)`。幾何上の辺重複も許容する保守的な4倍評価。
- **真正有限接続数を使用**：元空間リンクeに接する空間プラケットは最大6個。無関係プラケットの元エネルギー差は0で、全空間作用 `|Spatial_H(B_g)-Spatial_H(B_h)|≤24*d_J(g,h)`。時間crossing作用の変動は `≤d_J(g,h)`、対称one-slab作用は `|S_H(A,B_g)-S_H(A,B_h)|≤13*d_J(g,h)`。
- **無条件Wilson核の定量係数**：元の `K_H(A,B)=exp(-beta0*S_H(A,B))` と `S_H≥0`、非正の実引数上の `exp` の1-Lipschitz評価を組み合わせ、**すべての有限H、同じ真正A,B,e,g,hについて `|K_H(A,B_g)-K_H(A,B_h)|≤13*beta0*d_J(g,h)`**。固定 `beta0=log(3/2)/64>0` のもとでこの核係数はHに依存せず、`d_J→0` で差分上界も0となる。代理Wilson核・独立Haar法則・追加の局所正則性仮定は導入しない。

### 元Perron密度・joint sqrt-density・全リンクD_Hへの残る段階

- 今回確定したのは**元Wilson核の真の1リンクLipschitz評価**まで。元の連続Perron真空 `Omega_H` の積分固有方程式による定量差分、真正 `rho_H`・厳密 `q_H` への積・平方根・逆数評価、全二境界・全リンク `D_H` へのtelescopingは次段階として未形式化。AELの粗いHarnack因子と今回の小距離比例評価を混同しない。
- 既存AEKの体積依存の真の核・Perron・joint密度上下界は保持。現時点でGI 68/1:17、元source-dependent共分散の安定球、H一様強制性、物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップは未認証・未証明。

### exact-source Lean4・公理監査および正本記録

- 新規Lean `PhysicalYangMillsWilsonSU2OriginalOneLinkChordKernelModulusV5_PZ37AEM.lean` と `PhysicalYangMillsWilsonSU2OriginalSpatialChordKernelV5_PZ37AEM.lean` の2件のみ、19公開定理・19件 `#print axioms`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- 最終exact-source [CI #41572482075](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41572482075) は **11,289/11,289 SUCCESS**、全19件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立commit status receipt SUCCESS。
- 初回のLean `simp` 局所記法引数、`abs` 展開の負号正規化、tactic linterを**元の定理文・物理仮定を変えずに修正**。最終exact-source HEAD `68e8c43b1f7d449f931d77bf6995837ff1d3cff0`、test-merge `88a493f0742393bbf482ce0f0f3408c15628df2a` は差分0件、squashに含まれる新規2 Leanファイルの内容blobはsourceと完全一致。既存Lean・物理模型・workflow・公開rootは不変更。README/ROADMAPの追加記録のみ両ブランチで同文に同期し、docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — AEL（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。AEL定理PR [#6223](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6223) はMERGED、定理squash SHA `be751761848391bad1edc32a9007ada456b1beb2`。AEKまでの真正interacting Wilson SU(2)、centered Gauss-law物理源、元Perron/transfer、二interacting posterior、boundary pair-Haar、固定Lean/mathlibおよび公開rootを保持する。

### 元の二境界joint sqrt-density・Perron密度の1リンクHarnack評価

- **真正Wilson核と連続Perron真空を同じモデルで比較**：元の固定結合 `beta0`、元の1リンク置換 `B_g=B[e↦g]`、`B_h=B[e↦h]`、`t=exp(8*beta0)` を使用。既存の元Wilson核の `K_H(A,B_g)≤t*K_H(A,B_h)` と元連続真空の `Omega_H(B_g)≤t*Omega_H(B_h)` を掛け合わせ、実際の元joint weight `W_H(A,B_g)≤t²*W_H(A,B_h)` をLean4で証明。
- **真正joint sqrt-densityとJQ分母**：`rho_H=sqrt(W_H)` から `rho_H(A,B_g)≤t*rho_H(A,B_h)` と逆方向を証明。元の厳密相殺恒等式 `q_H(z)=‖T_H‖⁻¹/rho_H(z)` から同じ係数 `t` の真正Perron密度 `q_H` 比較を証明。元Wilson核の交換対称性からjoint weight・rhoの二境界入替対称性、および第一境界の1リンク比較も証明。代理密度、積独立、別作用素は導入しない。
- **明示的な絶対変動評価**：AEKの大域上下界と組み合わせ、`k_H=exp[-2*beta0*(P_H+L_H)]>0` に対して、同じ1リンク変更で `|rho_H(A,B_g)-rho_H(A,B_h)|≤(t-1)*sqrt((k_H⁻¹)^3)`、`|q_H(A,B_g)-q_H(A,B_h)|≤(t-1)*exp(beta0*2*(P_H+L_H))/sqrt(k_H^3)` を形式証明。どちらも固定Hで数値式が明示されるが体積一様評価ではない。

### 真正全リンク弦距離 D_H への厳密な境界と残るobstruction

- **元D_Hへの正確な校正**：元のSU(2) normalized trace feature弦距離 `d_J` と全二境界・全リンク `l1` 和 `D_H` を用い、`D_H((A,B_g),(A,B_h))=d_J(g,h)` をLean4で証明。距離の取り替えや一般化された合成幾何は使わない。
- **限界を明示**：今回の `exp(8*beta0)-1` 上界は `d_J(g,h)→0` で消えないため、真正 `D_H` におけるLipschitz／数値的epsilon-delta変動率を証明したとは主張しない。次は元Wilsonエネルギーと連続真空の差分を `d_J` に比例させる鋭い評価を構成し、`rho_H`・`q_H` の小距離変動率からAEFの真正共分散および二球Haarモーメントへ接続する。GI 68/1:17、H一様強制性、物理スペクトルギャップおよび連続体Yang–Mills質量ギャップは未証明。

### exact-source Lean4・公理監査

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSqrtDensityOneLinkHarnackV5_PZ37AEL.lean` のみ、14公開定理・14件 `#print axioms`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。最終exact-source [CI #41563025656](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41563025656) は **11,287/11,287 SUCCESS**、14件全て `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- 最初のCIで見つかった真正transferノルムの型付き正値証拠および `exp(8*beta0)≥1` の固定結合正値証明を修正。数式・元の物理仮定は弱めていない。最終source HEAD `6284076e0510bec4ab74536ef8c16694d4c6c8f8`、test-merge `0406d357eaf6b46ab8d4d68cbab74a0d50480de4`、squash `be751761848391bad1edc32a9007ada456b1beb2` のGit tree `0cac5cf5f27364cf1bf8bf916dd9aa1b17c01648` は完全一致。従来のLeanファイルと公開rootに変更なし。README/ROADMAPはappend-only同期し、docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — AEK（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。AEK定理PR [#6220](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6220) はMERGED、定理squash SHA `5972a2fc20deafd5ec72ba5e6e0383a1bb98c711`。AEJまでの真正interacting Wilson SU(2)・centered Gauss-law源・Perron/transfer・二interacting posterior・元のboundary pair-Haar・固定toolchain・公開rootを保持。

### 元Wilson核とPerron方程式から真正連続真空・joint sqrt-densityの明示的上下界

- **真正有限HのWilson作用budget**：`B_H=2*(P_H+L_H)`（元の空間プラケットリスト長と空間リンクリスト長）および `k_H=exp(-beta*B_H)>0` を使用。元のWilson一スラブ核 `k_H≤K_H(A,B)≤1`、AEJで証明済みの**未正規化Gauss-law物理transferノルム** `k_H≤lambda_H=‖T_H‖≤1` をそのまま引き継ぐ。
- **真正連続物理真空の大域Harnack比較**：元の非負Haar `L²` top eigenvectorの正確な点ごとのPerron方程式に対し `k_H*K_H(A,B)≤K_H(A,C)` と積分の単調性を適用し、`k_H*Omega_H(B)≤Omega_H(C)` を全元境界配置で証明。既存の真正 `L²` ノルム1および元のHaar確率測度の全質量1を使い、**無条件の固定H点ごと上下界** `k_H≤Omega_H(A)≤k_H⁻¹` を得る。元の真空代表とHaar法則を入れ替えない。
- **元の真正joint sqrt-densityの無条件有限H上下界**：元の `continuousJointWeight_H(z)=lambda_H⁻¹ * (Omega_H(z.1)*K_H(z.1,z.2)*Omega_H(z.2))` と `rho_H(z)=sqrt(continuousJointWeight_H(z))` を展開し、全元境界ペアで `sqrt(k_H^3)≤rho_H(z)≤sqrt((k_H⁻¹)^3)` をLean4形式証明。有限net、rho標本M/m、代理密度、物理的独立性は仮定しない。
- **元のJQ Perron密度の無条件有限H上下界**：AEGの厳密相殺恒等式 `q_H(z)=lambda_H⁻¹/rho_H(z)` とAEJの逆ノルム `lambda_H⁻¹≤exp(beta*B_H)=k_H⁻¹` から、全元境界ペアについて `0<1/sqrt((k_H⁻¹)^3)≤q_H(z)≤k_H⁻¹/sqrt(k_H^3)`。AEH/AEI/AEJで残っていた**大域の有限ネット標本上下界の独立数値認証を不要化**する。ただし粗い有限体積指数評価であり、H一様の下界ではない。

### 真正D_H変動率への接続と未解決条件

- 元の `rho_H` の真の `D_H` 変動証明 `|rho_H(z)-rho_H(w)|≤delta` が `D_H(z,w)<R` で確認できれば、`|q_H(z)-q_H(w)|≤(exp(beta*B_H)/sqrt(k_H^3))*delta/sqrt(k_H^3)`。AEHの元密度一様連続性から任意の正のdeltaについて対応する正の半径Rの**存在**も証明。ただし数値的なRや最適なLipschitz定数を今回求めたわけではない。
- 物理source-dependent Wilson Haar分子の具体的振幅と変動、同じ境界での二球モーメントマージン、GI 68/1:17閾値、H一様強制性、物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップは**未認証・未証明**。次は元のPerron・Wilson局所作用から具体的な `rho_H` 変動率と半径Rを評価し、既存AEFの元共分散へ接続する。

### exact-source Lean証明監査と継承正本

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalVacuumDensityExplicitHarnackV5_PZ37AEK.lean` 1本のみ（8公開定理・8件 `#print axioms`）。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41558724690](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41558724690) は **11,286/11,286 SUCCESS**、8件全ての依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- 初回からの修正は固定mathlibの正値不等式・逆数・実数 `L²` ノルムおよび確率Haar全質量1を明示したもので、定理文・真のWilson物理モデル・元の証明を弱めていない。最終source HEAD `6c1b646cd825429a3563ce1446054cb188ae6a81`、test-merge `c8c3c5f64423b52d5796bea0fb01d631e93315b1`、squash `5972a2fc20deafd5ec72ba5e6e0383a1bb98c711` のGit tree `835dfaa1791c48f945663649ad3f408fb6f78cdf` は完全一致。既存Lean・物理作用素・公開rootは不変。README/ROADMAPはappend-only同期、docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — AEJ（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。AEJ定理PR [#6217](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6217) はMERGED、定理squash SHA `861d21996c82e5d5cbdf617afc310191fef211d5`。AEIまでの真正SU(2) Wilson・Gauss-law・Perron/transfer・二interacting posterior・元boundary pair-Haar・固定toolchain・公開rootを保持する。

### 元Wilson作用の明示的下界から真の未正規化物理transferノルムを二側評価

- **実際のWilson作用budget**：元モデルの空間プラケットリスト長 `P_H` と空間リンクリスト長 `L_H` によって、元のone-slab Wilson作用は `A_H(A,B)≤B_H=2*(P_H+L_H)`。既存の真正SU(N) Wilson核下界 `k_H(beta)=exp(-beta*B_H)≤K_H(A,B)≤1` を使用し、代理transferや新しい確率核を作らない。
- **真正Gauss-law物理ノルム下界**：元のHaar `L²` 上のGauss-law不変な定数単位ベクトルを使い、元ambient Wilson kernelの真の行列要素 `<T_H 1,1>=∫K_H d(Haar×Haar)≥k_H` を得る。内積のCauchy–Schwarzと物理Hilbert上の作用素ノルムから、任意の有限H、正ランクN、非負結合betaについて `0<k_H(beta)≤‖T_phys(H,N,beta)‖≤1` をLean4で証明。右側はAEIの真正未正規化作用素定理。
- **元物理transfer逆ノルムの数式化**：正ノルムの逆数単調性から `‖T_phys‖⁻¹≤exp(beta*B_H)`。元の固定結合SU(2)もこの不等式を満たす。体積に依存して指数増大する粗い上界であり、H一様なギャップは意味しない。

### 元のPerron密度・有限ネット・共分散・二球Haarへ伝播

- 元の厳密恒等式 `q_H(z)=‖T_H‖⁻¹/rho_H(z)` をそのまま使用。真正全リンク弦距離 `D_H` の有限ネットで、実際のrho上下標本 `m≤rho_H(a)≤M`、真正変動誤差 `epsilon`、`0<epsilon<m` が認証されれば、`1/(M+epsilon)≤q_H(z)≤exp(beta*B_H)/(m-epsilon)`。
- `D_H(z,w)<R≤r` なら `|q_H(z)-q_H(w)|≤exp(beta*B_H)*epsilon/(m-epsilon)^2`。AEFの実source-dependent Wilson Haar分子の上界・変動率とこのq変動を組み合わせ、元共分散の変動および元のゲージ反転二球Haarモーメント下界に接続。正の中心振幅対変動誤差マージンは別途必要。
- **証明済みと未認証を区別**：真のtransfer逆ノルム上界は無条件で具体的有限体積式になった。一方、実D_H-net、rho上下標本数値、rhoの具体的変動半径、真正Wilson Haar分子の振幅・変動率、GI 68/1:17はまだ数値認証していない。H一様強制性・物理スペクトルギャップ・連続体4D Yang–Mills mass gapを主張しない。

### exact-source Lean監査と継承境界

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTransferExplicitKernelFloorV5_PZ37AEJ.lean` 1本、12公開定理と12 `#print axioms`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。最終exact-source [CI #41553827962](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41553827962) は **11,285/11,285 SUCCESS**、12/12標準公理 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- 初回CIの `inv_le_inv₀` 正値証拠2か所の引数順を、変更ファイル全文とAEI・元Wilson kernel・Gauss-law・固定mathlib署名の照合に基づき修正。数式・定理文・元物理モデルの弱化なし。最終exact-source HEAD `b8613f06df78ab1fe313632cdfa0576711a43362`、test-merge `e64adf3ca9a3505f946ef48004def91c9fa85da3`、squash `861d21996c82e5d5cbdf617afc310191fef211d5` のGit tree `ce2ce3c357a4b9d90d56b58b9b82fd260582a9e4` は完全一致。
- **次の障害**：真正 `rho_H` の具体的な上下界および変動率を、連続真空 `Omega_H`・真のWilson核・Perron固有方程式から量的に取り出す。数値を仮定して終わらせず、有限H依存の数学的上界と実行可能なinterval証明書を区別する。docs-only PRではStrict Leanを再実行しない。

---

## 検証済み定理 — AEI（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。AEI定理PR [#6214](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6214) はMERGED、定理squash SHA `2a9a09ace31ff90bee6a431b095e5d850c730765`。AEHまでの真正SU(2) Wilson・Gauss-law・Perron/transfer・二interacting posterior・元boundary pair-Haar・固定toolchain・公開rootを保持。

### 元Wilson核から、未正規化物理transferノルム上界 U=1 を無条件に証明

- **真正kernelのノルム制御**：元のone-slab Wilson Boltzmann kernelの `0<K_H≤1` と真正正規化spatial pair-Haar確率測度を使い、`‖K_H‖_{L²(pair-Haar)}≤1` を形式証明。既存のHilbert–Schmidt評価とGauss-law物理部分空間への制限を合成して、任意の有限H・正ランクN・非負結合betaで、**元の未正規化** `‖T_phys(H,N,beta)‖≤1` をLean4で証明。正規化後の作用素ノルム1を仮定して元作用素へ逆輸入したものではない。
- **固定結合の物理正値とAEH改善**：真正SU(2)固定結合で `0<‖T_H‖≤1`。したがって、AEHが数値入力として残した `‖T_H‖≤U` を**定理によってU=1と確定**。真正有限D_H-net、元のrho_Hの上側標本 `rho_H(a)≤M`、実際の変動証明書 `|rho_H(z)-rho_H(w)|<epsilon` があれば、元物理分母は `0<1/(M+epsilon)≤q_H(z)`。元の `q_H(z)=‖T_H‖⁻¹/rho_H(z)` をそのまま使用する。

### 真正rho_Hの下側標本からq_Hの変動と二球モーメントまで接続

- **二側有限ネット証明書**：真正D_H-net上で `m≤rho_H(a)` が確認され、真の変動誤差epsilonが `epsilon<m` なら、全元境界配置で `m-epsilon<rho_H(z)`。さらに `D_H(z,w)<R≤r` に対し `|q_H(z)-q_H(w)|≤(‖T_H‖⁻¹/(m-epsilon))*epsilon/(m-epsilon)` を厳密に導出。逆transferノルムの絶対値評価そのものは**まだ別途必要**で、上界 `‖T_H‖≤1` だけで逆数を上から制御したとは主張しない。
- **元Wilson source-dependent共分散と真正二球Haar下界**：上記`q_H`変動をAEFの実分子`N_e`条件へ代入し、元`C_e`の変動およびAEE/AEFの反対ゲージ二球モーメント下界へ移送。分子上界・変動率・中心振幅が変動誤差を超える条件は独立の検証義務として残す。

### exact-source CI・公理監査・未解決境界

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTransferKernelUnitNormDensityModulusV5_PZ37AEI.lean` 1本。10公開定理、10件の`#print axioms`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41548934002](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41548934002) は **11,284/11,284 SUCCESS**、全10定理が `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- source HEAD `85a4fef8d4be0801f088b02b9b7667713556db1a`、test-merge `d165b4228bcf2979785ad0095f69f691dee1d4ee`、squash `2a9a09ace31ff90bee6a431b095e5d850c730765` のGit tree `08cfd4b43c92d39bdc60fe38714e921cc7da6e9f` は一致。既存Leanファイル・物理モデル・公開rootは変更しない。
- **未認証**：具体的D_H-net、rho_H上下標本の数値、実用的変動半径、逆transferノルムの数値上界、真正Wilson分子の上界と変動および振幅、GI 68/1:17、H一様強制性、物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップ。次は元kernelの明示的下界と正規化真空構造から、`‖T_H‖` の実際の正下界と`rho_H`変動率を定量化する。docs-only変更でStrict Leanを再実行しない。

---

## 検証済み定理 — AEH（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。AEH定理PR [#6211](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6211) はMERGED、定理squash SHA `02e3f35651eb18e10b718060152d6696fe4fbdd3`。元のinteracting Wilson SU(2)、centered Gauss-law物理源、Perron/transfer作用素、FF receiver、二つのinteracting posterior、元boundary pair-Haar、Lean/mathlib pin、定理rootは変更しない。

### 真正有限D_Hネットの観測データによる物理正規化分母の検査可能な下界

- **実際のjoint sqrt-densityを使用**：元の `rho_H(z)=continuousJointSqrtDensity_H(z)` は真正二境界ペア空間上で連続であり、ADMの元全リンク弦距離 `D_H` に関して任意の正誤差に対する一様連続性半径が存在することをLean4で証明。代理densityや異なる距離は導入しない。
- **真正有限サンプルから大域評価**：AEEで定義済みの実境界配置有限net `s` に対し、`∀z, ∃a∈s, D_H(a,z)<r`、`D_H(z,w)<r ⇒ |rho_H(z)-rho_H(w)|<ε`、`∀a∈s, rho_H(a)≤M` が**実際に検証できれば**、`∀z, rho_H(z)<M+ε` を証明。元のrhoの正値性と真正net非空性からサンプル上界 `M>0` も証明。
- **元Perron/transferノルムを数値認証へ分離**：真正未正規化物理transfer作用素 `T_H` に独立に `‖T_H‖≤U` が確認できた場合、AEGの元物理分母の厳密恒等式 `q_H(z)=‖T_H‖⁻¹/rho_H(z)` を使い、全元境界配置について
  `0<λ_cert(H)=1/(U*(M+ε))≤q_H(z)`
  をLean4形式証明。これは**チェック可能な条件付き有限H数値式**であって、net、変動半径、サンプル数値M、transferノルム上界Uの実値が既に認証されたことは意味しない。

### 元のWilson共分散変動・二球モーメント定理へ移送

- **AEFの厳密な分子／分母証明書へ代入**：元のsource-dependent Haar分子 `N_e(z)` について `|N_e(z)|≤Nmax`、`D_H(z,w)<R ⇒ |N_e(z)-N_e(w)|≤dN`、元分母について `|q_H(z)-q_H(w)|≤dq` を**別途認証**できた場合、真正共分散変動は `|C_e(z)-C_e(w)|≤(dN+(Nmax/λ_cert)*dq)/λ_cert`。元のGauss-law・FF受信器・Perron重みを変えず、実数の補題と真正物理定理で接続する。
- **真正ゲージ反転二球下界**：同じ真正共分散の正の中心振幅 `C_e(a)` が上記変動誤差 `δ_C` より大きいことが**別途確認できた場合**、AEE/AEFの互いに素な二球から `(C_e(a)-δ_C)^2*2*(min(R/(2*card(Link_H)+1),2)/4)^(8*card(Link_H))≤S(H,b₀,e)` が形式的に成立。物理振幅の数値、FCの68/1:17閾値、体積一様強制性、物理スペクトルギャップ、連続体4D Yang–Mills mass gapは未証明のまま保持する。

### exact-source Lean検証・形式証明境界

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSampledDensityNormBudgetV5_PZ37AEH.lean` 1本のみ。8公開定理、8件の `#print axioms`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。最終exact-source [CI #41545186979](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41545186979) は **11,283/11,283 SUCCESS**、8件すべて公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0、独立exact-head completion receipt SUCCESS。
- 初回CIの固定mathlib `inv_le_inv₀` 引数順エラーは、新規AEHファイル全文とAEG・AEE・AEFの依存シグネチャを再照合し修正。定理文・数値式・元物理モデルを弱めず、最終source HEAD `ba917e8829015758f57b7f77f002c786eca56d77`。source/test-merge/squash Git tree `12ea18c4648f40ff5cd1f62d0927987a792f15cd` 完全一致。
- **次の定量的obstruction**：本当に検査可能な有限net中心・cardinality、`rho_H` のサンプルと変動半径、元transfer作用素ノルムの具体的上界U、Hに依存する共分散分子の数値、実際の物理二球の安定半径と振幅を独立に評価する必要がある。現時点では条件付き証明書が完成した段階。docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — AEG（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。AEG定理PR [#6208](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6208) はMERGED、定理squash SHA `2977080e8b9a65b250ea64ea08182c53ffd00505`。真正interacting Wilson SU(2)、元centered Gauss-law source、Perron/transfer、FF receiver、元二つのinteracting posterior、boundary pair-Haar、固定Lean/mathlib、定理rootは不変更。

### 真正Perron分母の厳密な真空相殺と有限体積正下界

- **真正密度の恒等式**：JQ/FFで定義済みの元の物理密度 `q_H(z)` は、元の半密度 `W_H(z)` と逆真空重み `V_H(z.2)` の積。FFの定義と真正正値定理をLean4で展開し、真空重みの厳密な相殺により `q_H(z)=‖T_H‖⁻¹ / ρ_H(z)` を証明。ここで `T_H` は元Perron/transfer作用素、`ρ_H(z)=continuousJointSqrtDensity_H(z)` は元の真正joint sqrt-density。新しい確率測度・代理分母を導入しない。
- **固定Hの無条件正下界**：真正boundary pair空間のコンパクト性、元密度の連続性・正値性、上記恒等式から `ρ_H` は厳密に正の有限最大値 `M_H` を持ち、元の全境界配置zに対し `λ_H=‖T_H‖⁻¹/M_H>0`、`λ_H≤q_H(z)` をLean4形式証明。これは**各有限H依存の存在定理**であって、`M_H`、`λ_H` の数値計算や体積一様下界ではない。

### 元Haar分子の連続性・最大値・共通誤差半径

- **同一真正物理分子**：AEFの元のsource-dependent SU(2) Haar積分 `N_e(z)` と同じ物理共分散 `C_e(z)` に対し `N_e(z)=C_e(z)q_H(z)` を証明。ACDで証明済みの元物理共分散連続性と元density連続性を使い、`N_e` の連続性を証明。ACI/AEFの非零物理証人より、全真正物理空間リンクeで `|N_e|` の達成された厳密正値の有限大域最大値が存在する。
- **AEFの個別条件が同時充足可能**：任意の真正リンクe、各 `δ_N>0`、`δ_q>0` に対して、同じ元の全リンク弦距離 `D_H` 上の共通 `R>0` と、真正密度下界 `λ_H>0`、分子上界 `M_{H,e}>0` が存在し、`D_H(z,w)<R` なら `|N_e(z)-N_e(w)|≤δ_N` と `|q_H(z)-q_H(w)|≤δ_q` が同時に成立することをLean4で証明。独立な一様連続性半径のminを使用し、元のAEF商の誤差評価へ接続できる。半径・振幅・分母上界の具体的数値は未認証。

### Lean4 CI・公理監査・境界

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalDensityCompactNumeratorFloorV5_PZ37AEG.lean` 1本。公開11定理、11件の `#print axioms`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。最終exact-source [CI #41541628032](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41541628032) は **11,282/11,282 SUCCESS**、全11定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- 初回失敗で局所記法 `W.continuous`・`rho.continuous` のLean識別子解釈を確認し、元FFの連続写像型と、通常関数としての `continuousJointSqrtDensity` を区別。元密度の連続性と真空相殺からsqrt-density連続性を導き、最後にtransferノルム非零証拠を用いて逆数正規化を完了。数式・物理仮定・元ファイルは弱めていない。最終source HEAD `d7208d8a205e31a304f70a5961147d858777c21f`。source/test-merge/squash Git tree `836a858d4a5c2952f138169f26bd81703dc73a7c` は完全一致。
- **未解決の数値obstruction**：元`ρ_H` の実際の最大数値、元transferノルム、`λ_H`、真正Haar分子の振幅・変動率、元共分散の数値、GI 68/1:17条件、体積一様強制性、物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップは本定理からは数値確定しない。次は元のsqrt-density・Perron/FF量に対する計算可能な上下界を別途調べる。docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — AEF（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。P4-Q2-PZ37AEF定理PR [#6205](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6205) はMERGED、定理squash SHA `0f0ecf47e0f6c3e2c216595d83e6294583910606`。真正interacting Wilson SU(2)、original centered Gauss-law source、Perron/transfer、FF receiver、二つのinteracting posterior、元boundary pair-Haar、固定pin、公開rootは変更なし。

### 真正Wilson共分散を元のHaar分子・元の正密度分母へ分離

- **物理比率の恒等式**：ACIの完全に元の物理リンクreceiver `J_e(z,g)` と元のSU(2) Wilson character `χ(g)` を用いるHaar分子 `N_e(z)=∫ J_e(z,g) χ(g) dμ_SU(2)(g)` を新しく命名するだけで、`C_e(z)=N_e(z)/q_H(z)` を元の固定結合 `b₀` でLean4形式証明。分母 `q_H(z)` はJQの元の半密度・Perron/transfer逆密度からなる真正の厳密正値な正規化重みであり、代理確率分布ではない。ACI/AEDの非零真正共分散点から、各物理リンクeについて実際の `N_e(z)≠0` の存在もLean4証明。
- **分子／分母の独立した定量証明書**：任意の真の `λ>0` について `λ≤q_H(z)` と `|N_e(z)|≤Nmax` が個別に検証できれば `|C_e(z)|≤Nmax/λ`。任意の元の二点の真正Haar分子・密度誤差がそれぞれ `dN,dq` 以下なら、元の真正共分散は `|C_e(z)-C_e(w)|≤(dN+(Nmax/λ)·dq)/λ`。さらにこれを元の全リンク弦距離 `D_H` における半径Rの統一モジュラスへ形式化した。数値のλ・Nmax・dN・dqそのものは計算していない。

### 同じ元物理二球・モーメント・条件付きFCへの接続

- **AEFの変動証明書の代入**：`ε=(dN+(Nmax/λ)·dq)/λ` とおき、実際に `R>0`、真正分子・密度のグローバルな境界および `ε<C_e(a)` が確認できた場合、AEEの元の反対符号・互いに素な二球と、AECの元boundary pair-Haar多項式下界から `(C_e(a)-ε)^2·2·(min(R/(2·card(Link_H)+1),2)/4)^(8·card(Link_H))≤S(H,b₀,e)` を証明。半径 `R=1/2` では真の係数 `2·(1/(8·(2·card(Link_H)+1)))^(8·card(Link_H))` となる。全て有限H依存を保持。
- **元GI検証の厳密な条件境界**：元のFC envelope `B(H,b₀)^2` が `272` 倍の上記の真正二球モーメント下界より厳密に小さいとの**追加数値判定が成立する場合にのみ**元のGI squared mean budgetが正と証明。GI 68/1:17の閾値を無条件で通過したという意味ではない。

### exact-source Lean監査・未解決境界

- 追加は新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPhysicalNumeratorDenominatorModulusV5_PZ37AEF.lean` 1本。公開Lean4定理11件、`#print axioms`11件。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。exact-source [CI #41537256383](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41537256383) は **11,281/11,281 SUCCESS**、全11定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、新規Lean warning/error 0/0、独立completion receipt成功。source HEAD `8a562e06faf2616cc8ea416867be3e7049c3f1e2`、source/test-merge/squash Git tree `c6cf5fd14f9c57aa43ba9fabb194fccf30cc984c` 完全一致。
- **未解決の真の物理的obstruction**：元の `q_H` の数値的で一様な正下界、Haar積分分子 `N_e` の数値振幅・変動、真正 `D_H` に対する具体的変動率、実共分散 `C_e(a)` の認証、有限体積一様強制性、物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップは依然として未証明。新規定理は検査可能な条件付き定量ルートであり、数値認証の代わりではない。docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — AEE（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。P4-Q2-PZ37AEE定理PR [#6202](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6202) はMERGED、定理squash SHA `a0420dca1ed357378db6f9e233096871ecf1904c`。旧Leanファイル、元のinteracting Wilson SU(2)、centered Gauss-law source、FF receiver、Perron/transfer、二つのinteracting posterior、真正boundary pair-Haar、pin、公開rootに変更はない。

### 真正D_H有限ネットと物理共分散の有限サンプル証明書

- **有限ネットの無条件存在**：ADLの元の全リンク校正弦距離 `D_H` と元のboundary pair空間のコンパクト性から、各有限体積Hと任意の実半径r>0に、全真正境界配置を覆う実際の有限 `D_H`-net `s` が存在することをLean4で証明。netの中心とcardinalityの具体的な数値は未計算。
- **有限データから大域振幅への厳密評価**：真正net証明 `∀z, ∃a∈s, D_H(a,z)<r` と真の共分散一様変動証明 `D_H(z,w)<r ⇒ |C_e(z)-C_e(w)|<ε` があれば、各zであるサンプルa∈sについて `|C_e(z)|<|C_e(a)|+ε`。特に実サンプルが全て `|C_e(a)|≤M` なら `∀z, |C_e(z)|<M+ε` を証明した。ADMの真正一様連続性とコンパクト性から、各ε>0にこのような有限サンプル証明書が存在することも無条件にLean4証明。
- **非零有限サンプル**：ACIの各真正リンクeの非零物理共分散証人と有限近似から、十分細かい有限netに非零共分散の実サンプルが存在する。これは**有限サンプルの存在**であって、数値的に算出したサンプルや一様半径の提示ではない。

### 可変誤差の二球Wilsonモーメント下界

- **固定値1/2から可変誤差へ**：真正元の中心aで `R>0`、`0≤ε<C_e(a)`、`D_H(z,w)<R ⇒ |C_e(z)-C_e(w)|≤ε` が確認されたとき、ACCのゲージ符号反転、相反する二つの互いに素な真正 `D_H` 球、AECの真正pair-Haar下界およびADEの二乗積分から、
  `(C_e(a)-ε)^2 × 2 × (min(R/(2·card(Link_H)+1),2)/4)^(8·card(Link_H)) ≤ S(H,b₀,e)`
  をLean4で証明。半径1/2では厳密な有理係数 `2×(1/(8(2·card(Link_H)+1)))^(8·card(Link_H))` となる。誤差・半径・振幅は数値認証されていない。
- **FC/GIとの正確な境界**：元のFC envelope `B(H,b₀)^2` が `272×`上記の真の二球積下界より厳密に小さいと**別途検証できた場合のみ**、ADEの元のGI squared mean budgetの正値性を導く。閾値68/1:17の無条件判定を意味しない。

### exact-source Lean検証・公理監査・未解決課題

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCovarianceFiniteNetErrorCertificateV5_PZ37AEE.lean` に8公開定理と8 `#print axioms`。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。最終exact-source [CI #41534328138](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41534328138) は **11,280/11,280 SUCCESS**。8定理すべて `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- 初回CIの絶対値差の対称性・固定mathlibの `add_le_add_right` の加法順序とunused hε linter warningを新規Leanファイル全文・ADE/ADM/AEC/AEDシグネチャ照合後に修正。定理型・物理法則・必要な仮定は変更なし。最終source HEAD `aaf6744d9db8444b3d534d35dbd0e69349867cac`。source/test-merge/squash Git treeは `411399842c9452544fb4a0a568aba4f1d0c8b697` で完全一致。squash `a0420dca1ed357378db6f9e233096871ecf1904c`。
- **未解決**：実際に構成・検証した有限netの具体点と規模、数値的な真正共分散値・変動率・半径、H一様強制性、厳密なGI閾値、物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップは未証明。次の物理研究では元のPerron/FF密度分母と共分散分子に対する計算可能な上界・下界を分離する。docs-onlyではStrict Leanを再起動しない。

---

## 検証済み定理 — AED（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。P4-Q2-PZ37AEDの定理PR [#6199](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6199) はMERGED、定理squash SHA `576f89f2476744e862a76ffb0758ebe42569e518`。元のinteracting Wilson SU(2)、centered Gauss-law源、FF receiver、Perron/transfer、二つのinteracting posterior、元boundary pair-Haar、Lean/mathlib pin、theorem rootは変更していない。

### 最大真正共分散と中心ゲージ対称性から得る二球・2倍の物理モーメント下界

- **真正物理共分散の最大振幅**：ACIが各有限体積H・元の空間物理リンクeについて構成した非零共分散点、ACDの元のFF receiver共分散連続性、真正boundary pair空間のコンパクト性を接続。元の `C_e(z)` について `M_(H,e)=max_z |C_e(z)|>0` の実際の達成点をLean4証明。ACCの真正central gauge `Γ_e` で `C_e(Γ_e(a))=-C_e(a)` を使い、`C_e(a)=M_(H,e)>0` とする**正の最大中心**と負の対中心を無条件に構成。これは振幅の数値計算ではない。
- **元の全リンク距離で共通の安定半径**：ADMがコンパクト性から証明した元のWilson共分散一様連続性により、`R>0` を選んで、真正 `D_H` 球 `Ball(a,R)` 内で `C_e(z)≥M_(H,e)/2`、対中心の `Ball(Γ_e(a),R)` 内で `C_e(z)≤-M_(H,e)/2` を証明。両方の球は実際に互いに素で、共通の真の半径Rを用いる。Rの無条件数値評価は未達成。
- **2倍の真正boundary pair-Haarと物理二乗モーメント**：AECの初等的な原Haar多項式 `P_H(R)=(min(R/(2·card(Link_H)+1),2)/4)^(8·card(Link_H))` を各球に適用。固定mathlibの `measureReal_union` と真正pair-Haarの加法性で、互いに素な球の和の質量 `ν_H(Ball(a,R)∪Ball(Γ_e(a),R))≥2P_H(R)` を証明。ADEの元Wilson共分散二乗モーメント `S(H,b₀,e)` へ `0<(M_(H,e)/2)^2·2P_H(R)≤S(H,b₀,e)` を、**全元物理空間リンクe** に対し無条件の存在証人付きでLean4証明。従来のAEC単一球下界を係数2で強化した。
- **検査可能な半径1/2の有理下界**：もし元の真の共分散一様連続性が `D_H(z,w)<1/2 ⇒ |C_e(z)-C_e(w)|<C_e(a)/2` を満たすと確認できるなら、`(C_e(a)/2)^2·2·(1/(8(2·card(Link_H)+1)))^(8·card(Link_H))≤S(H,b₀,e)` が従う。これは**検査可能な条件付き半径1/2証明書**であり、この物理安定半径自体が数値認証されたという主張ではない。

### Lean4検証・修正履歴・未解決境界

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTwoSignCovarianceDoubleBallV5_PZ37AED.lean` に10公開定理と10 `#print axioms`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。最終exact-source [CI #41528288716](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41528288716) は **11,279/11,279 SUCCESS**。全10定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- 初回CIでは真正SU(2)の局所コンパクト／Borelインスタンスと、固定mathlib `IsMaxOn` が点を暗黙引数にするシグネチャ等でelaboration失敗。変更Lean全文と依存定理シグネチャ・固定mathlib APIを照合し修正。次回は `IsMaxOn` に集合所属証明だけを渡す形へ修正し、最終CI成功。元の物理モデル・新規定理文・正下界・係数2は弱めず、不要な仮定のみ削除した。
- Exact-source HEAD `f951407eeac10513dbfdd45fb1379aa0d79b3d2e`、source/test-merge/squash Git treeは `9ba92b8d0db5dfaff0105c53c575984fb47684ca` で完全一致。新規Lean blob `5a145f3e9669b9399822a2a9693d3450b392fd8f`。squash SHA `576f89f2476744e862a76ffb0758ebe42569e518`。マージ後push CIはexact-source CIと分離して確認する。
- **未解決**：真正物理共分散の最大振幅 `M_(H,e)` と共通安定半径Rの計算可能な数値、H一様な強制性、GI 68/1:17閾値、物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップは未証明。次は実際のWilson共分散の振幅・安定半径を定量評価するための真正物理的解析を別に行う。docs-onlyではStrict Leanを起動しない。

---

## 検証済み定理 — AEC（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。P4-Q2-PZ37AEC定理PR [#6196](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6196) はMERGED、定理squash SHA `29d667b08174ab833a0e20c8b503c99121e33410`。元のinteracting Wilson SU(2)、centered Gauss-law源、FF receiver、Perron/transfer、二つのinteracting posterior、元boundary pair-Haar、pin、theorem rootは不変更。

### 固定mathlibに基づく真正Haar下界の初等的な四次・冪式

- **固定mathlibの定義を厳密展開**：pinned `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` の `Measure.toSphereBallBound` は、`n≠0∧r>0` で `n*((min (Real.toNNReal r) 2)/4)^n`。従ってADQの元の `κ(r)=((toSphereBallBound 4 r : NNReal):ℝ)/4` に対し、全 `r>0` で `κ(r)=(min r 2/4)^4` をLean4で無条件証明。小半径 `0<r≤2` では `κ(r)=(r/4)^4`、`r≥2` では `κ(r)=1/16`（これは元Haarの等号値ではなく下界）。特に元のnormalized SU(2) Haar radial mass は `m(1)≥1/256`。
- **真正boundary pair-Haarへ移送**：AEAの全有限体積H・全中心a・全 `R>0` の証明から、真正 `ν_H(B_D(a,R))≥(min (R/(2·card(Link_H)+1)) 2/4)^(8·card(Link_H))` を定理化。元の両boundaryの `2·card(Link_H)` 因子と実4次元の四次下界を保持し、指数 `8·card(Link_H)` の正確な掛け算を形式証明。
- **半径1/2の完全有理下界**：実際の元の full `D_H` 球 `B_D(a,1/2)` の質量は `(1/(8*(2·card(Link_H)+1)))^(8·card(Link_H))` 以上。有限Hのリンク数が定まれば計算できる式であり、有限ネットの未知cardinalityを使わない。
- **元の物理共分散二乗モーメント**：球内振幅 `A>0` が実際に検証できれば、ADE/AEBの元Wilson二乗モーメント `S(H,b₀,e)` へ `A²*(min(R/(2·card(Link_H)+1),2)/4)^(8·card(Link_H))≤S` を形式証明。全元物理空間リンクeについて、ACIの非零共分散点とADMの真の安定半径から、同じ多項式付き正下界の存在証人を無条件に得る。

### exact-source Lean・修正理由・未解決境界

- 新規 `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExplicitSpherePolynomialFloorV5_PZ37AEC.lean` の9定理／9 `#print axioms`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。修正後exact-source [CI #41522554271](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41522554271) は **11,278/11,278 SUCCESS**、全9件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error 0/0、独立MCP completion receipt SUCCESS。
- 初回CIでLean `push_cast` により `↑(min a b)` が `min (↑a) (↑b)` に正規化され、元のキャスト形へ `rw` できず失敗。変更Lean全文・import先・固定mathlibの定義と依存シグネチャを確認し、正規化後の `Real.coe_toNNReal` で等式を証明。定理の型や物理仮定は弱めず、linterの不要sequence-focusも修正。
- 最終source HEAD `6d8e13728eeb1ca0e1fb858a8197ca00c461cd31`、test-merge/squash Git tree `85fd436a3c38650022c6015bbb1e7972c3aa8527` で一致。新規AEC Lean blob `209b5f34137dfae8d1b21a52fd7c67d7c3fec913`。定理squash `29d667b08174ab833a0e20c8b503c99121e33410`。マージ後push CIは独立に記録する。
- **未解決**：Hに依存しない強制性、実際の物理共分散振幅・安定半径の具体的な数値、68/1:17閾値判定、物理スペクトルギャップおよび連続体4D Yang–Mills質量ギャップは本定理からは導かれない。docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — AEB（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。P4-Q2-PZ37AEB定理PR [#6193](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6193) はMERGED、定理squash SHA `1dd4c2f5fa2b5013dcc84e87960cd15b534eb6ee`。元のinteracting Wilson SU(2)、centered Gauss-law物理源、FF受信器、Perron/transfer、二つのinteracting posterior、元boundary pair-Haar、定理rootと固定pinは変更なし。

### 真正Wilson共分散二乗モーメントへの半径依存・振幅依存の明示的定量接続

- **検査可能な球内振幅証明書**：実物理リンク `e`、元のboundary pair中心 `a`、`R>0`、`A>0` について、真正全リンク球 `Ball_D_H(a,R)` 内の全点で `A≤|C_e(z)|` が検証できれば、元ADEの共分散二乗モーメント評価とAEAの真正pair-Haar下界から、`A² κ(R/(2·card(Link_H)+1))^(2·card(Link_H)) ≤ S(H,b₀,e)` をLean4で証明。ここで `κ(r)=((Measure.toSphereBallBound 4 r : NNReal):ℝ)/4` はADZの固定mathlib由来の明示関数。
- **任意の非零共分散点から存在証人**：元ADMの真正全リンク距離に関する一様連続性から、`C_e(a)≠0` なら、ある実際の `R>0` で球内振幅 `|C_e(a)|/2` を維持。従って `0 < (|C_e(a)|/2)² κ(R/(2·card(Link_H)+1))^(2·card(Link_H)) ≤ S(H,b₀,e)` を無条件に構成。
- **全物理リンクの明示的存在証明書**：ACIが元の固定結合・元Gauss-law源・元FF受信器で構成した各空間リンク `e` の非零共分散証人を代入。すべての実リンクに、上記の正の定量証明書 `(a,R)` が存在し、真正の物理共分散二乗モーメント `S(H,b₀,e)>0` をLean4で再証明。有限体積 `H` に依存する半径・振幅は数値未評価。

### Lean4 exact-source検証・継承境界

- 新規Lean `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCovarianceExplicitMomentFloorV5_PZ37AEB.lean` の6定理・`#print axioms`6件を検証。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41514706212](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41514706212) **11,277/11,277 SUCCESS**、変更Lean warning/error 0/0、公理依存は `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` なし。独立completion receipt SUCCESS。
- 定理source HEAD `9a5875334aeae829be8ff1dd8fab874a0fb503bc`。source/test-merge/squashのGit treeは `b47715de07970fc835f5d9acd7d01b007e64971f` で一致。追加Leanのblob SHAは `60e5483209a151571ceaa48c8ede6e22b6c4d17a`。定理正本のマージ後HEADは `1dd4c2f5fa2b5013dcc84e87960cd15b534eb6ee`。マージ後push CIはexact-source CIと分離して確認する。
- **残る定量obstruction**：真の `R` と `|C_e(a)|` の計算可能な数値評価、volume-independent物理強制性、68/1:17テスト、実物理スペクトルギャップ、連続体4D Yang–Mills質量ギャップはいずれも本定理の結論ではない。次は物理振幅と安定半径の実数値評価・半径関数の具体化を別々に検証。docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — AEA（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。P4-Q2-PZ37AEA定理PR [#6190](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6190) はMERGED、定理squash SHA `e9709855fb25e40273ca17f876123a30268088ca`。元のinteracting Wilson SU(2)、Gauss-law源、FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootおよびpinは不変更。

### 真正boundary pair-Haar全リンク球の無条件・半径依存定量下界

- **一リンクから全リンクへの厳密接続**：ADZの元のnormalized SU(2) Haar `m(r)≥κ(r)>0`（`r>0`、`κ(r)=((Measure.toSphereBallBound 4 r : NNReal):ℝ)/4`）と、ADMの元boundary pair-Haar全弦距離球 `ν_H(B_D(a,R))≥m(R/(2·card(Link_H)+1))^(2·card(Link_H))` を、追加の測度輸送条件なしで接続。正の分母とscaled radius、自然数冪の実数単調性をLean4形式証明。
- **無条件の真正全リンク球評価**：すべての有限体積 `H`、元boundary pair中心 `a`、`R>0` で `ν_H(B_D(a,R))≥κ(R/(2·card(Link_H)+1))^(2·card(Link_H))>0`。指数は左右境界の元の実リンク数 `2·card(Link_H)` で、有限体積依存を明示。半径 `R=1/2` についても同じ下界を形式証明。
- **真正Wilson共分散への接続**：全実物理空間リンク `e` についてACI/ADMの非零Wilson共分散証人 `a` と正半径 `R` を取り、上記の明示的pair-Haar正下界と既存ADEの真正共分散二乗モーメント評価を同時に形式証明。Gauss-law源・元の2 posterior・FF receiver・pair-Haar分布の置換なし。

### 検証・未解決境界

- 新規Lean `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPairHaarExplicitFloorV5_PZ37AEA.lean` に7定理・`#print axioms`7件。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41487286710](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41487286710) は **11,276/11,276 SUCCESS**。全7件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし、変更Lean warning/error 0/0。独立MCP completion receipt SUCCESS。
- 定理source HEAD `9fceb07db8962406dad9879ab4147cf44db4d2d6`、test-mergeとsquashのGit treeはすべて `c301320d34f945087653498b3101cc6492f86664` で一致。定理正本のマージ後HEADは `e9709855fb25e40273ca17f876123a30268088ca`。マージ後push CIの完了は別途確認対象であり、exact-source CIと混同しない。
- **未解決**：この`κ`下界はHに依存する。体積一様な強制性、厳密な物理スペクトルギャップ、厳密数値68/1:17判定、連続体4D Yang–Mills質量ギャップはこの段階では証明されていない。次の研究では、この明示的H依存の球測度下界を真の物理的評価へ定量接続し、非零共分散振幅と半径の数値化を独立に扱う。docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — ADZ（2026-11-03 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。default `main` は文書ミラーのみ。P4-Q2-PZ37ADZ定理PR [#6187](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6187) はMERGED、定理squash SHA `381369eb6f91ffb82685b0e5ddf0d600018543d5`。元のinteracting Wilson SU(2)、Gauss-law源、FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootは不変更。

### 真正SU(2) Haarに対する正半径の無条件・全中心下界

- **Haar／球面測度の厳密逆像評価**：ADUの元SU(2)↔S³ homeomorphism `Φ` と固定mathlib `MeasurableEquiv.map_apply` により、任意の球面集合 `s` で `μ_SU2(Φ⁻¹(s))=ν_G(s)` を証明。ADYの真正 `ν_G=σ̂`（独立固定mathlib球面測度の確率正規化）を使用し、可測集合に制限しない測度同一視を保持。
- **元の表面測度の正規化・正値性**：有限測度 `μ=Measure.toSphere(volume)` に対して、固定mathlib `FiniteMeasure.self_eq_mass_mul_normalize` と実数値測度の変換を使い、全集合 `s` で `σ̂(s)·σ(S³)=σ(s)` を証明。`Measure.toSphere_ne_zero` と `measureReal_univ_pos` から `σ(S³)>0` を証明。非正規化の球面測度を元Haarと誤認しない。
- **既存ADQ条件の無条件解除**：ADTで証明済みの元弦距離球 `BallJ(1,r)=Φ⁻¹(ball(Φ(1),r))` と、上記の測度輸送・総質量正値性をADQの条件付き定理に代入。全 `r>0` で、元のnormalized compact SU(2) Haarの半径質量 `m(r)` に `m(r)≥κ(r)>0` を**無条件**に証明。ここで `κ(r)=((Measure.toSphereBallBound 4 r : NNReal):ℝ)/4` は固定mathlib由来の陽な半径関数。
- **全SU(2)中心へ拡張**：元の全 `a∈SU(2)` と `r>0` で `μ_SU2(BallJ(a,r)).toReal≥κ(r)` を証明。元の物理ゲージ・boundary pair-Haar・受信器・事後分布を置き換えない。

### 正本検証・継承事項

- 新規Lean `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUnconditionalHaarRadiusV5_PZ37ADZ.lean` の7定理・`#print axioms`7件。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。exact-source [PR Lean Fast Check #41441980869](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41441980869) は **11,275/11,275 SUCCESS**。変更Lean warning/error 0/0、公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし。独立completion receipt SUCCESS。
- 定理source HEAD `203eb5da6954fbff47e918012ad35d4a91719550` のsource/test-mergeに差分ファイルなし。source／squashの新規ADZ LeanファイルGit blob SHAは `cf3f533d30370b5533e98d372a8043f4a9b9b32e` で一致。親ADY正本に対する変更ファイルはADZ Leanファイル1件のみ。
- **残る問題**：全有限体積Hで一様な強制性・volume-independent物理スペクトルギャップ・連続体4D Yang–Mills質量ギャップは、この球測度下界だけでは証明されない。次は真正boundary pair-Haar積への半径依存下界の定量移送などを別個に検証。docs-onlyではStrict Leanを再実行しない。

---

## 検証済み定理 — ADY（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADY定理PR [#6184](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6184) はMERGED、定理squash SHA `38acbb00232f42db39790ebba1ad090d272b5c4b`。元のinteracting Wilson SU(2)、Gauss-law源、FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootは不変更。

### 真正SU(2)直交左作用によるMathlib球面測度の無条件不変性

- **放射状sectorの厳密移送**：ADXの真正SU(2)左作用を延長する実4次元線形等長同型 `L_g` と、ADU/ADVの元球面作用 `T_g` に対し、任意の球面集合 `s` で `L_g⁻¹(radialSector(s)) = radialSector(T_g⁻¹(s))` をLean4証明。集合の表示に由来するLean4 `rw` の照合差は、定義上の等式を明示し `congrArg` で運ぶことで解決。
- **独立Mathlib球面測度の不変性**：固定mathlib `LinearIsometryEquiv.measurePreserving` のLebesgue体積保存、`Measure.toSphere_apply'` の放射状領域公式から、`σ = Measure.toSphere (volume : Measure E4)` に対し `Measure.map (T_g) σ = σ` を証明。
- **正規化と元Haar一意性**：固定mathlib `Measure.toSphere_ne_zero` による非零性、`FiniteMeasure.normalize`、`Measure.map_smul` で `σ̂` の不変性を証明。ADUで既に証明した真正SU(2)左作用に関するHaar確率一意性に接続し、元の確率Haarの押し出し `Measure.map Φ μ_SU2 = σ̂` を**無条件**にLean4証明。別のSU(2)群・代替Haar・追加測度仮定を導入しない。

### exact-source Lean4・公理依存・次の段階

- 固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41439134813](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41439134813) は **11,274/11,274 SUCCESS**、Leanジョブ・独立completion receiptともSUCCESS。新規4定理すべての `#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error 0/0。
- 定理PRのsource/test-mergeで差分ファイルなし。source HEAD `11a656c7bd5a041ce3441ef427922c93bd2ed0eb` とsquashの変更対象2ファイル（新規ADY Leanファイル・CI実行時間設定）のGit blob SHAが一致し、親ADX正本に対する変更ファイル集合も一致。
- **次のADZ課題**：ADTの元弦距離球と真正S³球の逆像一致、ADYの独立正規化球面Haar同一視、ADQの半径下界を接続し、元normalized SU(2) Haarの `m(r) ≥ toSphereBallBound(4,r)/4 > 0` （`r>0`）を無条件化する。全有限体積Hで一様な強制性や連続体4D Yang–Mills質量ギャップは引き続き別の未証明課題。docs-onlyでStrict Leanは再実行しない。

---

## 検証済み定理 — ADX（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADXの定理PR [#6181](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6181) はMERGED、定理squash `376cf3e0f8f75908e81e2e3bb3c4a97b4ae37f29`。元のinteracting Wilson SU(2)、Gauss-law源、FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootは不変更。

### 真正SU(2)左作用と実4次元線形直交変換の厳密一致

- **ADW四元数の符号整合**：元SU(2)の第1列4実座標とADW真正四元数の第4成分の符号差を固定mathlibの`LinearIsometryEquiv.piLpCongrRight`による実4次元線形等長反射で補正。真正 `Quaternion.linearIsometryEquivTuple` と合成し、元の4実座標 `V(g)` と正確に一致することをLean4で証明。
- **無条件の実4次元直交作用**：ADWの元SU(2)四元数左乗法線形等長同型を、固定mathlib `EuclideanSpace ℝ (Fin 4)` の `≃ₗᵢ[ℝ]` へ共役で移送。全元 `g,h∈SU(2)` で `L_g(V(h))=V(gh)`、全球面点 `x∈S³` で `L_g(x)=T_g(x)` をLean4無条件証明。ここで `T_g(x)=Φ(g Ψ(x))` はADV/ADUで確立した**同じ元の物理SU(2)作用**。
- **真の球面保存**：`L_g` は元の4次元ノルムを保存する線形等長同型なので、元のMathlib単位3球を保ち、元の作用 `T_g` と完全一致する。別の群・物理ゲージ・Haar法則は導入しない。
- **残存obstructionの限定**：独立の固定mathlib球面測度 `σ=Measure.toSphere(volume)` が上記線形直交変換 `L_g` で保存されることはこのPRでは未証明。従って `ν_G=σ̂` や元Haarの無条件半径依存下界はまだ主張しない。H一様強制性・連続体4D Yang–Mills質量ギャップも別問題。

### exact-source Lean4・公理依存

- 新規5定理と`#print axioms`5件。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41394507779](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41394507779) は **11,273/11,273 SUCCESS**。全5件の公理依存は標準3公理 `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error 0/0、独立completion receipt SUCCESS。
- Source/test-merge/squash treeは `a697191c476a65576e7d95977879a55f0435f747` で一致。次のADYでは固定mathlib `Measure.toSphere_apply'` と線形等長変換の体積保存から球面測度不変性を形式化する。docs-onlyでStrict Leanを再実行しない。

---

## 検証済み定理 — ADW（2026-11-02 JST）

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、default `main` は文書ミラーのみ。P4-Q2-PZ37ADW定理PR [#6178](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6178) はMERGED、定理squash SHA `e2f09f7f33ae0c3a1703ea4de996a57eef33cbea`。元interacting Wilson SU(2)、Gauss-law物理源、FF受信器、Perron/transfer、二interacting posterior、元boundary pair-Haar、定理rootは不変更。

### 真正SU(2)の単位四元数表示と実4次元線形等長作用

- **真正SU(2)→Mathlib四元数の正確な符号付き対応**：ADRで証明した元の行列`g=[[a,-conj(b)],[b,conj(a)]]`について、固定mathlibの`Quaternion ℝ`へ`q(g)=(Re(a),Im(a),Re(b),-Im(b))`を構成。第四成分の負符号は元SU(2)行列積を保存するために必要。全`g`に対して`Quaternion.normSq(q(g))=1`と`‖q(g)‖=1`をLean4で証明。
- **真正の乗法整合性**：元の2×2 SU(2)行列積と固定Mathlib四元数の実部・3虚部の積公式を直接計算し、`q(1)=1`、`q(gh)=q(g)q(h)`をLean4無条件証明。元の特殊ユニタリ群から`Quaternion ℝ`へのモノイド準同型を構成。
- **実4次元の線形等長作用と逆**：元の`g`に対応する左乗法`x↦q(g)x`を`Quaternion ℝ →ₗ[ℝ] Quaternion ℝ`として構成。四元数の乗法的ノルムと`‖q(g)‖=1`により真正の`→ₗᵢ[ℝ]`を証明し、元`g⁻¹`の四元数左乗法を逆とする`≃ₗᵢ[ℝ]`を構成。別の有限群Haarや仮想SU(2)を導入しない。
- **残る独立の測度obstruction**：今回の四元数上の実線形等長作用が、ADVで証明済みの元`S³`作用`T_g(x)=Φ(g*Ψ(x))`と一致すること、および固定mathlibの`Measure.toSphere(volume)`正規化測度がその実4次元直交作用に不変であることは未証明。したがって`ν_G=σ̂`、元SU(2) Haarの無条件半径依存数値下界、全H一様強制性、連続体4D Yang–Mills質量ギャップは主張しない。

### exact-source Lean4・公理依存

- 新規4定理・`#print axioms`4件。固定Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。[exact-source CI #41385605532](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/41385605532) は **11,272/11,272 SUCCESS**、変更Lean warning/error 0/0、4件は標準3公理`propext`・`Classical.choice`・`Quot.sound`のみ、`sorryAx`なし、独立MCP completion receipt SUCCESS。
- Source/test-merge/squash Git treeは `d2faeedaa725b20119b11b21249cb52ee26b35f5` で一致。次は四元数実4次元等長変換を`EuclideanSpace ℝ (Fin 4)`上で実装し、真の球面作用との一致、標準球面測度の不変性を個別に形式化する。docs-onlyのStrict Lean再実行は不要。

---

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


## AIS（2026-11-09 JST）— 真正Ward交差評価、全有限Hで0<β≤1の半Haar下界

**CLOSED:** [AIS定理PR #6551](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6551) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AIS_verified_20261109.md)。元の作用・両端halfweight・符号付きZW源・真正Haar・AIG全余裕を保持し、AHUの混合Haar恒等式から交差二次モーメントの下界を改善した。

- 全実βで `∫Kcross_β f_H²≥exp(-βp_H)V_H`。
- β>0、f_H(B)≤0で、元transferは `T_β f₀(B)≤-D_H`、`D_H=β exp(-5βp_H/2)V_H`。
- **全有限H・0<β≤1で、元の厳密全余裕負領域の実Haar質量≥1/2**。β=1を含み、源ゼロ集合の零測度仮定は不要。
- β=1で旧比較因子>2と新半Haar性が両立する。元の固定β₀は全Hで適用可能。H≥2では `θ_H<β₀`、`δ_H<ε_H<D_H` と半Haar性が同時に成立する。
- 元の体積表示と `V_H≤p_H²/4`、`D_H≤β exp(-5βp_H/2)p_H²/4` を形式化した。

[Exact-source CI #42540948252](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42540948252/attempts/1) は11407/11407 SUCCESS、29/29標準3公理のみ、sorryAx 0、変更warning/error 0/0、独立receipt SUCCESS。定理squash `3dd12415adb88e30abbd97ab6d7d4cf7579eb38b` のtree/blobは認証sourceと一致した。

**OPEN / AIT候補:** 元の交差作用と源の追加相関評価によるβ>1の範囲、または既存の明示体積上界から新補助床の非一様性を分離する極限定理。物理対象・旧余裕・固定環境を維持し、新しい結果が得られるまで未証明として残す。体積一様の正の振幅・coercivity、負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapへの移行には別の証明が必要である。


## AIT（2026-11-09 JST）— 有理Ward transfer、体積により増大する閉半Haar上端、補助床の消失

**CLOSED:** [AIT定理PR #6554](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6554) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AIT_verified_20261109.md)。元の完全作用・両端halfweight・符号付きZW源・真正Haar・AIG全余裕を保持する。

- 源の両符号で有理二次補正を証明し、源が非正の集合 `f_H(B)≤0` 上で元transferの負値床を `Dhat_H=β/(1+βp_H/2) exp(-2βp_H)V_H` に改善。全β>0でAISの床より厳密に大きい。
- 元の一リンクHaar積分と交差分配関数の単調非増加性を証明。単位結合の既存Gaussian上界から、**全有限H・0<β≤1+6(H+1)^3で、元の全余裕厳密負領域のHaar質量≥1/2**。
- **全H共通の0<β≤7**と、**固定β>0に対する `∃N, ∀H≥N` の半Haar下界**を形式化。上端自体を含む。各固定Hで全β>0の成立や最適閾値の認証は含まない。
- 固定β>0で `Dhat_H→0`、およびこの補助床に全H共通の正の下界がないことを証明。半Haarのeventual-H結果と同時に成立する統合証明書を追加した。
- この床の消失は、実際のtransfer振幅の消失や別の評価法の不可能性を意味しない。有限体積ごとの関数・Haar・領域を、共通空間の極限へ貼り合わせたという主張も行わない。

[Exact-source CI #42554354126](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42554354126/attempts/1) は11408/11408 SUCCESS、49/49標準3公理のみ、sorryAx・Lean error・変更warning/errorは0、独立receipt SUCCESS。[定理squash](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/57cbe6241f41adbface0d8e379f9e98d81bf723a) のtree/blobは認証sourceと一致し、[統合後push #42555080816](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42555080816/attempts/1) もSUCCESS。初回の4warningと2か所だけの修正履歴を正式記録に保持する。

**OPEN / AIU候補:** 各固定有限Hで残る大きい正結合を扱う、元の真正分配関数の結合依存減衰評価。または、今回の消失する証明書を超えて、既存の正規化を保持したまま、元transferの負値振幅や正規化因子の体積依存性を制御する新しい評価。体積一様の正の余裕・coercivity、作用素の負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapには別の証明が必要である。



## AIU（2026-11-09 JST）— 実際の元transfer像の一様体積減衰と正の一様負値深さの不存在

**CLOSED:** [AIU定理PR #6557](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6557) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AIU_verified_20261109.md)。元の完全作用・両端halfweight・符号付きZW源・真正Haar・AIGの余裕と厳密負領域を保持する。

- 真正crossing kernelの左Haar積分を、元のkernel対称性と右Haar積分から導出。全β≥0・全H・全Bで、実際の元transfer像に `|T f0(B)|≤exp(-βW(B)/2)(p_H/2)Zcross≤(p_H/2)Zcross` を証明した。
- 真正分配関数の正確な率 `ρ=-log z` と明示率 `d=β exp(-2β)` を構成し、`Zcross=exp(-ρp_H)`、β>0で `0<d≤ρ` を証明。**固定β>0のもとで、全境界について一様に元transfer像が0へ近づく**。
- 元のsource-image familyの正の一様絶対振幅・負値深さは存在せず、固定した正の深さの負部分集合は十分大きいHで空になる。この対象では、別の評価法だけによって真に正の体積一様な深さを作ることもできない。正規化や源族を変えた対象への不可能性は含まない。
- 元のAIG余裕は `0<ε_H≤(β/8)p_H² exp(-2βp_H)→0`。AITのeventual半Haar下界、元の正の余裕の小ささ、全境界での実像の小ささを一つの共通cutoffで同時に証明した。
- 元のβ₀で `d(β₀)≥1/384` と `|T_β₀ f0(B)|≤12(H+1)^3 exp(-(H+1)^3/16)`。AITの補助床消失と区別して、実際の元transfer像の上界から得た結果である。

[Exact-source CI #42559591642](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42559591642/attempts/1) と [統合後push CI #42560361781](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42560361781/attempts/1) は11409/11409 SUCCESS、35/35標準3公理のみ、sorryAx・全Lean error・変更warning/errorは0、独立receipt SUCCESS。[定理squash](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/ac30f9db7932c94f5a2cb82fd6d1998102cf0c4e) のtree/blob/全文は認証sourceと一致する。初回CIで認証され、統合後pushも同じ監査条件を満たした。

**OPEN / AIV候補:** 元の真正分配関数・正規化因子との相対評価、または各固定Hで残る大きい正結合における元の全余裕負領域の追加評価。今回証明した非正規化source-imageの減衰を保持し、その対象に正の一様振幅があるかのように扱わない。正規化後のtransferや別の源族、共通の極限作用素、coercivity、負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapには、それぞれ別の形式証明が必要である。



## AIV（2026-11-09 JST）— 元作用素ノルムの体積減衰と既存正規化尺度の発散

**CLOSED:** [AIV定理PR #6560](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6560) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AIV_verified_20261109.md)。元の完全作用・両端halfweight・真正Haar・符号付きZW源・AIGの余裕と厳密負領域を保持する。以下のノルム評価は全H・β≥0、体積極限は固定β>0である。

- 元のkernelの二乗と真正pair-Haar積分から `‖P_H,β‖≤‖R_H,β‖≤√Zcross_H(2β)` を証明。literal kernelと既存L²代表のa.e.橋、既存ambient作用素と物理制限の関係を明示した。
- 両端halfweightを保った行積分評価と、既存の正値連続物理top eigenvectorのコンパクト最大・最小から `exp(-2βp_H)Zcross_H(β)≤‖P_H,β‖≤Zcross_H(β)`。正規化された代替作用素やH一様のvacuum正値下限を仮定しない。
- **固定β>0でambient・物理作用素ノルムは0へ収束し、ambient L²単位球全体に共通の小ささのcutoffがある**。元の物理ノルムに正の体積一様下限は存在しない。AIUの単一源の点ごとの評価に、異なる型の全単位球L²評価を追加した。
- 既存の正規化尺度は `exp(ρp_H)≤‖P‖⁻¹≤exp((2β+ρ)p_H)`、固定β>0で+∞へ発散する。rawノルムの正値性と減衰、逆ノルムの増大、既存正規化作用素ノルム1を一つの共通cutoffで同時に記述した。
- 元のβ₀で `‖P_H,β₀‖≤exp(-(H+1)^3/16)` と逆ノルムの対応する指数下界を得た。`λ_H~Zcross_H` という漸近同値や正確な物理ノルム指数率は主張しない。

Exact-source CI [#42567459390](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42567459390/attempts/1) と 統合後push CI [#42568082026](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42568082026/attempts/1) は全workflow・必須Lean step・独立receiptがSUCCESS。依存閉包はそれぞれ 11410/11410、11410/11410 SUCCESS、38定理＋0定義、38/38実公理出力が標準3公理のみ、この最終認証2 runのsorryAx・全Lean error・変更warning/errorは0。認証source・実test-merge・[定理squash](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/33cb9e84a415ac46275cc8a118c54b5e4336aa3a) のtreeは `52191ac4df018b4b7307825c09fd67ffb09ec371` で一致し、Lean全文とblobも一致した。初回・2回目の実CI失敗 [#42564655886](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42564655886/attempts/1)、[#42566323927](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42566323927/attempts/1) は、実ログ・artifact・failure receiptの照合結果と識別情報を正式記録に保存した。初回の35定理の署名を維持して構造補題3件を追加し、2回目の38定理の全署名も最終sourceと一致する。元の物理定理への仮定追加、固定heartbeatの増加、元対象の変更はない。

**OPEN / AIW候補:** 既存正規化作用素の相対評価と、真正のスペクトル・coercivityへの接続条件。既存のノルム1をgap証明と扱わず、今回示した正規化尺度の体積依存性を保持する。異なるHの共通Hilbert空間、正規化励起gap、各固定Hで任意正結合の元の全余裕半Haar性、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapには、それぞれ対応する別の形式証明が必要である。



## AIW（2026-11-09 JST）— 真正空間平均による正規化相対評価と元の余裕の正規化

**CLOSED:** [AIW定理PR #6563](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6563) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AIW_verified_20261109.md)。元の完全作用・両端halfweight・真正Haar・物理源・AIG余裕と厳密負領域・既存正規化を保持する。

- 全H・β≥0で、∫W_H dμ_H=p_Hと両crossing周辺積分から、exp(-βp_H)Zcross≤Q≤λ=‖P‖≤Zcrossを証明。Qは元の自由境界one-slab pair-Haar積分で、物理定数単位ベクトルの行列要素。指数関数の接線不等式の一次項を厳密平均で相殺する。端点の独立性を仮定しない。
- 相対尺度をexp(-βp_H)≤λ/Zcross≤1、1≤Zcross/λ≤exp(βp_H)で挟み、逆ノルム上界をexp((2β+ρ)p_H)からexp((β+ρ)p_H)へ改善した。λとZcrossの漸近同値は未証明。
- 元の積分像T f0/λと、既存正規化物理作用素N=P/‖P‖の出力とのHaar-a.e.橋を構成した。任意のL²代表に点ごとの等式を付与せず、元の指定積分代表を明示する。
- 同じ正のλで元の余裕δを割ったm=δ/λについて、(βV_H/2)exp(-2βp_H)≤m≤(βV_H/2)exp(-βp_H)≤(β/8)p_H²exp(-βp_H)。固定β>0ではm→0だが、各有限Hではm>0。
- 正規化strict sublevelは元のAIG負領域と正確に一致する。AITのeventual半Haar性、任意η>0で0<m<η、‖N‖=1を同じcutoffで同時に証明した。元の固定β₀ではm≤72β₀(H+1)^6 exp(-(H+1)^3/8)。

Exact-source CI [42574638690](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42574638690/attempts/1) と統合後自動push CI [42575438682](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42575438682/attempts/1) は、全workflow・必須Lean step・独立receiptがSUCCESS。依存閉包は両runとも11411/11411、30定理＋2定義、全32実公理出力は標準3公理のみ。この最終認証2 runのsorryAx・全Lean error・変更warning/errorは0。認証source・実test-merge・[定理squash](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/bd7357e21e0ab24de11d7f957d0000e503f95851) のtreeは `a0315279084e58d44de4daafc4645168f1bc494f` で一致し、Lean全文とblobも一致した。初回失敗run [42573651318](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42573651318/attempts/1) の2件のelaboration errorと回復用sorryAx出力は正式記録に保持する。点ごとの関数形を明示する2か所の証明修正に限り、全32宣言の署名・仮定・固定環境・heartbeatを保持して再認証した。

**OPEN / AIX候補:** 元の正規化源像T f0/λの実際の振幅、または既存top直交sectorの真正相対評価。今回0へ近づくのは元のAIG証明書を正規化した余裕であり、正規化像の減衰や、より深い負領域の不存在ではない。各固定有限Hの大きい正結合での全余裕半Haar評価は別経路として残す。共通Hilbert空間・一様coercivity・励起gap・Hamiltonian spectral gap・連続体4次元Yang–Mills mass gapには、それぞれ互換条件と別の形式証明が必要である。


## P4-Q2-PZ37AIX — volume-dependent coupling の正結合window（2026-11-09、MERGED／形式認証済み）

元の既存正規化物理transferとAIG証明書を維持し、**a>0、a≤β_H≤b<∞** に制限されたすべての体積依存結合列について、`m_H(β_H)=δ_H(β_H)/‖P_H,β_H‖≤(b/8)p_H² exp(-a p_H)→0` をLean4で証明。window共通cutoff、正規化証明書の正の体積一様下限の不存在、既存正規化作用素norm=1、元AIG負領域の厳密一致、実源像の非減衰上界を別の定理として保持。新規定理7件・206行追加のみ。canonical formal定理PR [#6566](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6566)、source/test-merge/squash共通tree `28ecc5480bfde0da3625da11c18bf24c520762a4`。Exact-source [#42579467910](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42579467910) と統合後push [#42580324130](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42580324130) は各11,412/11,412・公理7/7・sorryAx0・Lean error0・新規warning0、実artifactおよびreceipt照合済み。正式記録: [AIX](docs/proofs/P4-Q2-PZ37AIX_verified_20261109.md)。

**OPEN / AIY:** 実際の正規化ZW源像のHaar-L²振幅・励起sectorへの射影とtop固有空間との関係を、元の定義・真正物理測度・依存型の接続として検証する。今回のm_Hは証明書尺度のみ。a>0や有限bがない任意のβ_H、変動結合での一様半Haar、共通Hilbert空間上のcoercivity・Hamiltonian spectral gap・連続体4D mass gapは未認証のまま保持する。append-only／tighten-only／overwrite-forbidden／same-root、固定Lean/mathlib pinとdocs-only時のStrict Lean非手動起動を継続する。


## P4-Q2-PZ37AIY — 実際の正規化ZW源像のHaar-L²非零性（2026-11-09、形式認証・統合済み）

元のSU(2) Wilson、両端halfweight、ZW物理源、真正Haar、既存ノルム正規化を一切変更せず、AIWのa.e.物理代表の橋・AITの厳密負領域半Haar下界から、**実際の正規化源像が真正物理L²クラスとして非零**であることを構成した。全有限H・`0<β≤1+p_H/4` で `0<||N_H,β f0,H||≤||f0,H||`、とくに全H共通 `0<β≤7`、任意固定β>0についてeventual非零を証明。一般のβ≥0では同じ物理normの厳密比 `||N f0||=||P f0||/||P||` と contraction を証明。新規Lean leaf 219行・定理9・削除0。PR [#6569](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6569) MERGED。

認証source `82ee5d0811b2cf4e33a85cf9e3a166235c3a4da0`、test-merge `497000b8d8171c0c82389d917926bfe397822751`、定理squash `0c3413dd7b619918fbfd9de1b51d7238f8e6c7cf` のtree一致 `e4420fa7158a3708eea9f87eb935ee8100623ab0`。修正版Exact-source [#42584457250](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42584457250) と自動push [#42585431281](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42585431281) はいずれも11,413／11,413 SUCCESS・公理9／9標準3件のみ・sorryAx0・Lean error0・変更warning0・実artifact/receipt成功。初回の冗長tactic warning1件は失敗履歴を残し、署名不変で修正した。正式記録：[AIY](docs/proofs/P4-Q2-PZ37AIY_verified_20261109.md)。

**OPEN / AIZ:** 元のLJの完全Wilson kernelの真正厳密正定値を、Gauss-law物理作用素の内積へ直接貼り合わせ、`β>0` の任意有限結合へ非零性を広げられるか検証する。AIG半Haar領域から実L²ノルムへの定量下界を型付きで構成する課題も残る。非零性は一様振幅下限を意味せず、元ZW源のtop固有空間直交性、励起gap、共通Hilbert空間上のcoercivity、Hamiltonian spectral gap、連続体4D mass gapは未認証。append-only／tighten-only／overwrite-forbidden／same-root、固定Lean v4.30.0-rc2/mathlib pinを維持する。

## P4-Q2-PZ37AIZ — 任意正結合での元の真正物理L²非零性（2026-11-09、MERGED／形式認証済み）

**CLOSED:** [定理PR #6572](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6572) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AIZ_verified_20261109.md)。AIG（全正結合・元厳密負領域の正Haar測度）→AIW（元領域と既存norm正規化積分代表の厳密一致）→AIY（a.e.代表と既存Gauss-law物理L²源像の非零橋）により、全有限H・任意β>0で `0<‖N_H,β f0,H‖≤‖f0,H‖` および `0<‖P_H,β f0,H‖` を証明。任意正結合列β_Hの各Hでも成立し、AIT結合上端を超えるβでも非零。半Haar測度の全正結合化は主張しない。

新規Lean 207行・10定理・追加定義0・削除0。修正版source `94f896b1d0cd82b78377384040b7c7e766c3355d`、test-merge `da0e340d692c7cc45ab05762593478a5405a8e0e`、squash `dc334fa6d68eee8f0d75f4c236f02be92b6f14a1` のtreeはすべて `86f6816c1139a92aee72549ce081d3377e206ae9`。Exact-source CI [#42600834308](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42600834308) と統合後push CI [#42603169982](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42603169982) は双方11,414/11,414 SUCCESS、10/10実公理出力標準3公理のみ、AIZ変更warning/error0、sorryAxなし、独立receipt SUCCESS。失敗runと修正理由は正式記録へ保存。

**OPEN / AJA（二つの別ゲート）:** (i) 既存の正規化連続積分代表、同じ元Haar負領域、元の正余裕から実際のL²源像の **H・β依存の定量下界** を証明する。厳密負集合R上の下界とその真正測度を接続する必要があり、正測度だけで一様半Haarや体積一様floorを仮定しない。(ii) 元のtop固有空間への射影と元ZW源のtop直交性／励起成分を別の命題として検証する。定量L²下界、射影、coercivity、Hamiltonian spectral gap、連続体mass gapの間の貼合条件が未証明である以上、結論を昇格しない。固定Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6、append-only／tighten-only／overwrite-forbidden／same-root。

## P4-Q2-PZ37AJA — 定量的真正Haar-L²源像下界（2026-11-09、形式認証・MERGED）

**CLOSED:** [定理PR #6575](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6575) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AJA_verified_20261109.md)。元の完全SU(2) Wilson one-slab／両端halfweight／真正Haar／ZW Gauss-law物理L²源／既存物理ノルム正規化を変更せず、全有限H・β>0で `0<m²·Measure.real μ_H(R)≤‖N f0‖²` をLean4で証明。可測な元負領域上の指定積分代表の厳密符号と、既存物理L²出力のHaar-a.e.等式から、一般の実L²積分下界を型付きで適用した。新規168行・3定理・定義0・削除0。

修正版source `a4cd620ea2c153d2cf2c5dbc5b93d9e2f89b1f9b`、test-merge `e40341db30e8cf0c2ac61f93a11688ff492485ef`、定理squash `e5beaef8120445c216753125ec31cd8c86a852ed` の共通Git tree `28b728a8dd9f387ff053f21db03f6ec80e7296fe`。Exact-source CI [#42608468069](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42608468069) とsquash後push CI [#42609883742](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42609883742) とも11,415/11,415 SUCCESS、3/3公理標準3件のみ、変更warning/error0、AJA sorryAxなし、独立receipt SUCCESS。初回CI #42607467139の型推論失敗と修正を消さず正式記録に保持。

**OPEN／AJB（二つの別課題）:** (1) 既存top eigenspaceの実際の直交射影と元ZW源像／元源を同じH・βの物理Hilbert空間で接続し、射影ノルムと直交成分を識別する。(2) 原証明書のH・β依存・Haar質量・余裕の量的評価を独立に調べる。いずれの未証明条件も仮定として挿入しない。真正励起sector下界、体積一様coercivity、Hamiltonian spectral gap、非自明4D連続体Yang–Mills mass gapは未認証。固定Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6、append-only／tighten-only／overwrite-forbidden／same-root。

## P4-Q2-PZ37AJB — 元ZW物理源像の全top／直交定量分解（2026-11-09、MERGED／形式認証済み）

**CLOSED:** [Lean定理PR #6578](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6578) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AJB_verified_20261109.md)。既存の全top eigenspace/orthogonal分解に、元AJAの正Haar-L²証明書を条件・型付きで接続した。全有限H・β>0で `N f0=u_top+u_⊥`、`‖N f0‖²=‖u_top‖²+‖u_⊥‖²`、`0<m²·Measure.real μ_H(R)≤‖u_top‖²+‖u_⊥‖²`。実top成分の二乗ノルムがこの証明書**未満**という追加条件の下でのみ`u_⊥≠0`を証明。元ZW源のtop直交性やその小ささを仮定として挿入していない。

新規Lean1件158行、4定理・削除0。認証source `c776a9585b0082b63b0f834ccaacb60d97b57afe`、squash `0c98fec903366eae58722fdeeb5e2ae0ae81dca7`、共通tree `96f9cccb415fcbffe90271f7ed7cca4515456426`。Exact-source [#42613066943](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42613066943)／push [#42613812145](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42613812145) とも11,416/11,416 SUCCESS、新公理4/4標準3件のみ、変更warning/error0、AJB sorryAxなし、receipt SUCCESS。初回失敗 #42612123173の構造的理由は正式記録に保存。

**OPEN／AJC:** 既存の真のtop固有ベクトル／全top eigenspaceの射影を、元ZW物理源像の内積と合わせて具体評価する。必要なtop寄与の上界が未認証なら条件付き障害を残す。各Hの非零性を全H一様振幅・励起sector非零・coercivity・Hamiltonian spectral gap・連続体4D Yang–Mills mass gapへ昇格させない。固定Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6、append-only／tighten-only／overwrite-forbidden／same-root。

## P4-Q2-PZ37AJC — 正準top射影・直交残余下界（2026-11-09、MERGED／形式認証済み）

**CLOSED:** [Lean定理PR #6581](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6581) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AJC_verified_20261109.md)。元の完全SU(2) Wilson物理transfer、真正Haar確率、符号付きZW Gauss-law物理源とnorm正規化を変更せず、**既存全top eigenspace**への正準starProjectionおよび全top直交補への射影を定義。全有限H・β>0について、元正規化源像の正準再構成と二乗ノルムのピタゴラス等式を証明した。AJA正の証明書 `C=m²*Measure.real μ(R)` に対して `0<C≤‖top‖²+‖orth‖²`、`C-‖top‖²≤‖orth‖²`、そして**実top寄与 `‖top‖²<C` が別途証明された場合に限って** `orth≠0`。後者の不等式はOPEN。

追加Lean1件186行／削除0、正準射影定義2・定理7。Exact-source CI [#42617449250](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42617449250)と統合後push [#42618394145](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42618394145)はともに11,417/11,417 SUCCESS、9/9の公理出力は標準3公理のみ、変更warning/error0、新規sorryAxなし、独立receipt SUCCESS。source `6f16501c87ff57941b9244efd0ef7b6465cf9f9c`・squash `eda6b204e5bbbae65809aa968957736ad763b62e` の共通Git tree `caefa8a12dbe42b122f559fe0a6f198e9a49b237`。初回失敗CI #42616327394は未認証として構造理由を正式記録へ保持。

**OPEN／AJD:** 既存top固有ベクトル・全top射影・元ZW物理源の真正top内積を同じH・βの物理Hilbert carrierで型付き接続する。必要な実際のtop-overlap上界が得られなければobstructionを残す。元ZW源のtop直交性を無根拠に挿入せず、H一様正L²振幅、全物理Hilbert coercivity、Hamiltonian spectral gap、非自明4D連続体Yang–Mills mass gapを主張しない。append-only／tighten-only／overwrite-forbidden／same-root、固定Lean/mathlib維持。

## P4-Q2-PZ37AJD — 元ZW源の真正top-overlap不変性（2026-11-09、MERGED／形式認証済み）

**CLOSED:** [定理PR #6584](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6584) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AJD_verified_20261109.md)。元Gauss-law物理Hilbertの既存全top部分空間で、対称な真の正規化Wilson transferがtopを固定することから、元のZW源と正規化転送後源像の全top内積・正準top射影が一致。`Π_Top(N f₀)=Π_Top f₀`。真正AJA証明書を転送**前**元源へ置き換えた残余下界 `‖u_⊥‖²≥C_H,β−‖Π_Top f₀‖²` を形式化。励起sector非零は実top射影が十分小さい**条件付き**に留まる。

新規Lean1件206行（定義1・定理6）、7/7実公理は標準3件のみ、AJD変更warning/error0、sorryAxなし。Exact-source CI [#42634322528](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42634322528)、統合後push CI [#42637270766](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42637270766)ともSUCCESS、11,418/11,418、receipt SUCCESS。source `714aec58d29953b631010cd04d431ca4ccef4ca8` とsquash `f646eb48342eac60f5e05acbbea60c5e846a33fb` のGit tree `ce3176c00891e63ed5b7adaf796113a05fec1409` 一致。

**OPEN／AJE:** 実top射影 `‖Π_Top f₀‖²` を元Wilson–Haar内積とtop部分空間の既存定義から量的評価する。証明書未満の上界、top直交性、体積一様物理gap、Hamiltonian spectral gap、連続体4D mass gapはいずれも未認証。仮定を追加して結論を作らない。固定Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6、append-only／tighten-only／overwrite-forbidden／same-root。

## P4-Q2-PZ37AJE — 真正元源全top射影の双対証明書（2026-11-10、MERGED／形式認証済み）

**CLOSED:** [Lean定理PR #6587](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6587) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AJE_verified_20261110.md)。既存真正ZW Gauss-law源・全top eigenspaceに対する厳密な双対評価：‖Q f₀‖≤b ↔ 全top vに対し |⟨f₀,v⟩|≤b‖v‖（b≥0）。さらに既存選択top単位ベクトルΩに対して |⟨f₀,Ω⟩|≤‖Q f₀‖、AJA証明書C_H,βに関し ‖Q f₀‖²<C_H,β ↔ C_H,β未満の全top一様内積予算の存在をLean4で形式化。**証拠となるbは未構成**。一本のΩと全topを同一視しない。

新規Lean1件230行・9宣言・既存削除0。初回CI #42640480799のmul_le_mul_right API型不一致は、仮定を変えず正値性を明示した背理法で修正。修正source 750b0fd38e88e85bc7965ab2ec7386a9abbdd9aa・squash 661345cdc4100c06996dbf431a84f4ee96dacb35 の共通Git tree c4321886c4420c28d3d5e7782dd4974f964a132e。Exact-source [#42641688446](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42641688446)／統合後push [#42642608623](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42642608623) SUCCESS、11,419／11,419、9／9標準公理のみ、変更warning/error0、sorryAxなし、独立receipt SUCCESS。

**OPEN／AJF:** 既存物理top全ベクトルの真正元ZW源とのWilson–Haar内積の厳密評価、およびAJA証明書未満の一様上界の**実構成**。単なる選好・同値式を励起sector非零、全H一様coercivity、Hamiltonian gap、4D連続体Yang–Mills mass gapの証明へ昇格させない。固定Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6、append-only／tighten-only／overwrite-forbidden／same-root。

## P4-Q2-PZ37AJF — 真正選択top・追加top二寄与の認証（2026-11-10、MERGED／形式認証済み）

**CLOSED:** [Lean定理PR #6590](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6590) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AJF_verified_20261110.md)。元のZW物理源f₀、既存全top射影Q、既存選択単位top固有ベクトルΩについて、r=Qf₀−⟨f₀,Ω⟩Ωはr∈全topかつ⟨r,Ω⟩=0、‖Qf₀‖²=|⟨f₀,Ω⟩|²+‖r‖²。真正AJA証明書Cから直交残余下界C−|⟨f₀,Ω⟩|²−‖r‖²≤‖u⊥‖²を証明。和がC未満の場合だけu⊥≠0。選択Ω寄与がC以上なら全top小条件を満たせない。単独Ωへの評価を全topへの評価に昇格しない。

新規Lean1件264行・11宣言・削除0。Exact-source [#42686668837](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42686668837)・統合後push [#42687789720](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42687789720)ともSUCCESS、11,420／11,420、11／11標準3公理のみ、変更warning/error0、sorryAxなし、独立receipt SUCCESS。source 144ee091cf8821c417d0b54f73ee325d852f6c11・squash 31145eea77605526aec2b57a201303387ac8f2ae、共通Git tree 49b452ae6e86781a43df75e5e0eb928b34c6a99f。

**OPEN／AJG:** (1) r=0 または‖r‖²の真正上界。(2) 元ZW源の選択top内積の厳密上界。両方を真正物理対象から導出しなければAJDの小top条件は未認証。top単純性、励起sector一様下界、全物理Hilbert coercivity、Hamiltonian gap、4D連続体mass gapはいずれもOPEN。append-only／tighten-only／overwrite-forbidden／same-root、固定Lean/mathlib不変更。

## P4-Q2-PZ37AJG — 真正ZW源中心化とtop真空偏差の証明書（2026-11-10、MERGED／形式認証済み）

**CLOSED:** [Lean定理PR #6593](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6593) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AJG_verified_20261110.md)。元ZW源f₀の真正Haar定数単位方向cに対する直交性 ⟨f₀,c⟩=0、選択単位topΩへの内積上界 |⟨f₀,Ω⟩|²≤‖f₀‖²(1−|⟨Ω,c⟩|²)、さらにAJF追加top残余rを保った**全top射影ノルム二乗の上界** ‖Qf₀‖²≤‖f₀‖²(1−|⟨Ω,c⟩|²)+‖r‖² をLean4で証明。AJA証明書C未満の両項上界が別途得られた場合のみ真正直交成分非零。Haar定数が既存top eigenvectorだとは仮定していない。

新規Lean1件255行・10宣言・削除0。初回失敗 #42689972569 のmul_nonneg暗黙項・内積スカラー倍照合・辺順不一致、再失敗 #42691058717 の内積減法rw不一致は、型付き証明項から組み立てるcalcへ修正。修正版source 9975cad37f9af393fcd40905df475341c3e89247 とsquash 76951507130749219e08c1b133eb596f633d43ca の共通tree 8bc702e4107d1af14e58d2ff9f4b080254a96068。Exact-source [#42692558676](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42692558676)／push [#42693592821](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42693592821) SUCCESS、11,421／11,421、10／10公理は標準3のみ、変更warning/error0、sorryAxなし、receipt SUCCESS。

**OPEN／AJH:** 真正真空Ωの定数方向からの定量偏差、全topの追加残余の定量上界、AJA証明書を下回る合計を元Wilson物理対象から導出する。top一次元性、励起sector一様下界、全物理Hilbert coercivity、Hamiltonian gap、4D連続体mass gapは未認証。固定Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6、append-only／tighten-only／overwrite-forbidden／same-root。

## P4-Q2-PZ37AJH — 元ZW source全topへの反復transfer上界（2026-11-10、Lean定理MERGED／CI監査済み）

**CLOSED（形式証明）:** [Lean定理PR #6596](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6596) MERGED。[正式記録](docs/proofs/P4-Q2-PZ37AJH_verified_20261110.md)。元の対称正規化Wilson transfer Sの任意の冪で全top正準射影 Q が不変：Q(Sⁿf₀)=Qf₀。全top元sourceとAJF残余は元sourceの真の反復物理ノルムにより上から抑えられる。追加top残余をゼロと置かず、top固有空間が一次元とも仮定しない。選択topの定数方向偏差について得たのは**下界 1−‖Sⁿc‖²≤D**であり、目標上界の構成とは区別する。

Exact-source CI [#42704315781](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42704315781) は11,422／11,422 SUCCESS、9／9宣言公理監査は標準3公理のみ、sorryAxなし、変更warning/error0、独立receipt SUCCESS。304行追加・既存証明改変0。認証source 55160801c2dd9b9ec728bb6b20a08cefb9fcc3b5／正式squash 76bca4c6b505dc5506696c95dbd0d71ea422fe8c／共通Git tree 82a90be5f9336bbd60af44566370d73d58271a53。統合後push CI [#42705520744](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42705520744) は完了後別途独立観測。

**OPEN／AJI:** いずれかn≥2について真正証明書 ‖Sⁿf₀‖²<C_AJA の証人を元Wilson物理から構成できるか、あるいは D上界とE上界を独立に証明して ‖f₀‖²D+E<C_AJA に到達できるかを検証する。現時点でどちらの不等式も認証されていない。top一次元性、正のH一様励起下界、全物理Hilbert coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapはいずれもOPEN。Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6、append-only／tighten-only／overwrite-forbidden／same-root。

**AJH統合後push CI受領（追記）:** [#42705520744](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42705520744) completed／SUCCESS、11,422／11,422、9宣言公理は標準3のみ、変更warning/error0、sorryAxなし、独立receipt SUCCESS。厳密AJA budgetとH一様gapは依然OPEN。

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


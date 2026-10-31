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

# MGAP4D — 4D Yang–Mills / genuine Wilson SU(2) Lean 4 formalization

## 現在の定理チェックポイント — 2026-10-31 JST · P4-Q2-PZ37ABR–ABV

**唯一のLean定理正本：** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit)。`main` は文書ミラーであり、Lean定理正本ではない。



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

全物理Hilbert coercivity、共通positive-fine区間、同一endpoint E/F、任意深さの一様評価、H1–H4、OS/Wightman再構成、非自明な4D連続体Yang–Mills構成とmass gapも **OPEN**。ABMの上限のみの結合条件に対する障害、PZ37ZAの別の補償済み二文脈量のno-go、および全ての先行定理・履歴を保持する。詳しい次の独立入力は[ROADMAP.md](ROADMAP.md)。

## 歴史的記録 — ABQ2以前の本文（原文保持）

**この見出し以降の「最新」「現行」「Current」「OPEN」とSHAは各記述時点の履歴である。** ABQ2の「現在の正本は上記ABQ2」という文言も当時の状態を示す。現在の検証済み範囲は本追補による。以下の歴史的本文は削除・改変していない。

---

**Original interacting Wilson theory · Gauss-law physical Hilbert space · Lean 4 + mathlib · Hidetoshi Itakura**

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

## Latest VERIFIED theorem checkpoint — 2026-10-29 JST · P4-Q2-PZ37ABG (#6002)

**Single Lean theorem authority:** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). Default `main` is a **documentation mirror**. The PR #6002 exact **tested source HEAD** was [`f752141618f07a5d0c2b1cfd51c5cc2e60bb34d4`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/f752141618f07a5d0c2b1cfd51c5cc2e60bb34d4); the distinct squash/authoritative theorem HEAD after [#6002 MERGED](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6002) was [`6f68bc2989b7b46b2c3ef1702d521982ed37e521`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/6f68bc2989b7b46b2c3ef1702d521982ed37e521). [Exact-head CI #40831840574](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40831840574): **11,171 / 11,171 Lean SUCCESS**, changed Lean warning/error **0/0**, 5 new public `#print axioms` standard `propext` / `Classical.choice` / `Quot.sound` only, no `sorryAx`, independent completion receipt SUCCESS. Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

**Newly recorded since ABE (theorem-bearing, MERGED):**

| Stage | Genuine original SU(2) Wilson / Gauss-law result | Limitation |
| --- | --- | --- |
| [ABF / ABF2 #6001](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6001) · [CI #40830784024](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40830784024) | The exact original full pair-Haar signed decomposition `G=K_p+Σ_(q≠p)K_q`; a genuine plaquette with `0<G/|P_H|≤K_p`; true local physical GI amplitude with **actual** transfer norm `t=||T||>0` satisfies `|t Δ_local,p|≤E_b/2`, and its full original pair-Haar L² moment `Mcomp≤(E_b/2)²`, where `E_b=exp(8b)(exp(16b)−exp(−16b))` is volume-independent. | `|P_H|` grows; no absolute signed residual bound; `t` is NOT set to 1. |
| [ABG #6002](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6002) · [CI #40831840574](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40831840574) | Genuine compact-probability pair-Haar L² Cauchy–Schwarz proves `(t K_p)²≤G Mcomp≤G(E_b/2)²`, hence `(tK_p)²/(E_b/2)²≤G` for ALL true finite volumes, couplings, links, and centered physical plaquettes. One true link/plaquette supplies a **strictly positive finite-volume** cross-derived floor. | No positive H-independent infimum for `tK_p` or `G`, and no all-physical-Hilbert coercivity or continuum mass-gap claim. |

**Priority OPEN gate (not silently discharged):** For an explicitly admissible positive bounded-above coupling family `b(H)`, derive from the **actual two interacting posterior Wilson model** an independent `κ>0` such that `∀H,∃e_H,p_H: t_(H,b(H)) K_(H,b(H),e_H,p_H)≥κ`. The ABG inequality is not a proof of this input. Genuine pair-Haar local event mass/amplitude and the entire signed negative tail (including remote variables) must be quantitatively controlled rather than replacing interacting posteriors or assuming a finite-support Perron response. With a common `E_b≤E_B`, ABG then implies `G≥4κ²/E_B²`. Common physical-Hilbert coercivity, positive-fine interval, same E/F endpoints, H1–H4, OS/Wightman reconstruction and continuum 4D Yang–Mills mass gap remain OPEN. Retain the old PZ37ZA no-go and all earlier proof/history.

*The older checkpoint below is retained as historical documentation; its former “latest” status has been superseded by ABG. This documentation-only synchronization does not establish a new Lean theorem and must not trigger Strict Lean.*

---

## Historical verified theorem checkpoint — 2026-10-29 JST · P4-Q2-PZ37ABE (#5998)

**Unique Lean theorem authority:** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). The default `main` is a **documentation mirror**, not the Lean theorem carrier. The **latest theorem-bearing squash** [`75bee4a633cb1296a47a85624cd65a0917fddc8d`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/75bee4a633cb1296a47a85624cd65a0917fddc8d) was independently verified equal to the authoritative branch HEAD immediately after [PR #5998](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5998) merged. The **PR source** SHA actually tested was [`25b6cc2bc6171603bfbb909a23918be3a25586b4`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/25b6cc2bc6171603bfbb909a23918be3a25586b4), **not** that squash SHA. [Exact-head CI #40827511993](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40827511993): **11,168 / 11,168 Lean jobs SUCCESS**, 1 changed Lean file with **0 warnings / 0 errors**, 3 public `#print axioms` requiring **`propext`, `Classical.choice`, `Quot.sound` only**, no `sorryAx`, and independent completion receipt **SUCCESS**. Pinned Lean `v4.30.0-rc2` and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` are unchanged. A subsequent docs-only merge changes the branch HEAD **without adding a new Lean theorem**.

### Genuine finite-volume Wilson evidence after AAZ2 (all MERGED)

| Lean stage | New unconditional theorem-level result | Still unresolved |
| --- | --- | --- |
| [ABA / ABA2 #5994](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5994) · [CI #40819215120](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40819215120) | From **FK's actual normalized interacting Wilson posterior density bounds** independently prove `Q_(H,b,e,z) ≤ (exp(16b)-exp(-16b))²` without importing JL's five legacy `native_decide` axioms. For each finite `H,b>0`, some genuine link has an **integrable strictly positive unweighted original GI gap-square moment** `G_(H,b,e)>0`. For `0<b(H)≤B`, a common valid **upper FX cap** `q_B=(exp(16B)-exp(-16B))²>0` is now proved. | `inf_H G_(H,b(H),e_H)>0` remains open, not rescued by qualitative positivity. |
| [ABB / ABB2 #5995](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5995) · [CI #40822230956](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40822230956) | For each finite volume, construct a **positive-original-pair-Haar-mass OPEN boundary event** with a nonzero **actual** centered GI gap and positive local amplitude. With the **true GB physical source projection** `α`, prove `c_b²∫α²dμ_H ≤ G ≤ C_b²∫α²dμ_H`, using GA's original FX lower and FK/ABA's upper bound, all standard-axiom-only. | Open regions and projection lower amplitudes may depend on `H`; their existence does not imply a fixed-support common cylinder. |
| [ABC / ABC2 #5996](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5996) · [CI #40825384594](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40825384594) | The **unchanged original centered Gauss-law Wilson GI gap** is **exactly** the finite sum of genuine centered spatial-plaquette GI contributions. For any selected actual plaquette, prove the exact single-plaquette plus **full signed residual** decomposition and reverse-triangle obstruction. At every finite `H,b>0`, one actual link and actual plaquette have **non-a.e.-zero** local source GI contribution. | The full Wilson/Perron GI response is not proven four-link local; signed residual cancellation needs direct control. |
| [ABD / ABD2 #5997](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5997) · [CI #40826544243](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40826544243) | Identify each centered plaquette contribution with the authentic two-interacting-posterior GI response of an **actual centered Gauss-law physical Hilbert plaquette source** (LO). Construct positive-mass open Haar events for local physical GI activity. More strongly, the **full** and **one genuine local physical** response have **strictly positive same-sign product** on an original pair-Haar event of positive measure. | The chosen link/plaquette/event/threshold are finite-volume-dependent. |
| [ABE #5998](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5998) · [CI #40827511993](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40827511993) | For the genuine full-vs-local **Gauss-law physical** signed pair-Haar correlation `K_(H,b,e,p)=∫Δ_full(z)Δ_local,p(z)dμ_H(z)`, prove **exactly** `Σ_(actual plaquettes p) K_(H,b,e,p)=G_(H,b,e)`. Therefore **unconditionally** every finite `H,b>0` has an actual link and actual plaquette with **`K_(H,b,e,p)>0` after integrating ALL remote original pair-Haar variables**. | `K>0` and `G>0` at each `H` do **not** supply an `H`-independent lower bound. |

**Unchanged mathematical authority:** actual finite-volume interacting SU(2) Wilson kernel; positive Perron vacuum; original Gauss-law Hilbert physical source and receiver; both distinct **interacting** conditional posterior laws; true reference SU(2) Haar and full outer boundary pair-Haar. No replacement posterior or synthetic observable is used. The historical PZ37ZA impossibility of a **different compensated two-context** uniform lower bound remains intact; it is **not** a no-go for the genuine full-link GL mass.

**Next independent proof gate:** for compatible bounded-above positive Wilson couplings, prove a **volume-uniform** positive `m` for `G_(H,b(H),e_H)`, or a sufficiently strong genuine local signed cross-response together with true nonlocal residual control. The fixed finite-volume positive global correlation from ABE is **not** yet such a bound. The FX upper cap is already independently proved by ABA under `b(H)≤B`; do not re-open JL's inherited axioms. Remaining independent gates include all-Gauss-law Hilbert coercivity, common positive-fine interval, same endpoint E/F, all-depth estimates, H1–H4, OS/Wightman reconstruction, continuum 4D existence and positive mass gap. No Clay-level theorem is claimed.

---

## Historical verified AAZ2 checkpoint (2026-10-29 JST; retained unchanged below)

**Theorem authority:** [`formal/real-hilbert-uniform-coercive-strong-limit`](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit). The repository's default `main` is **not** the theorem-bearing branch. All statements below concern the **actual finite-volume interacting SU(2) Wilson model**, two distinct normalized *interacting* conditional posterior laws, original product/pair Haar integration, the Gauss-law physical Hilbert space, and the unchanged centered physical source.

| Verified item | Exact evidence / status |
| --- | --- |
| Latest theorem-bearing PR | [#5991 — P4-Q2-PZ37AAZ / AAZ2](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5991) **MERGED** (following [#5990 AAY](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5990) and [#5989 AAX/AAX2](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5989)) |
| Exact PR **source** SHA tested | [`d769e275d016b6645e924a116acb0d7653f7e9a0`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d769e275d016b6645e924a116acb0d7653f7e9a0) |
| Exact theorem-bearing **squash** SHA | [`20f910f54791d662b687965af231842a27f093b6`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/20f910f54791d662b687965af231842a27f093b6), confirmed equal to canonical branch HEAD **immediately after #5991 merge** |
| [Exact-source-head CI #40814241452](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40814241452) | **11,159 / 11,159 Lean jobs SUCCESS**; AAZ/AAZ2 changed files warning/error **0 / 0**; eight public `#print axioms`: **`propext`, `Classical.choice`, `Quot.sound` only**; no `sorryAx`; independent MCP CI completion receipt **SUCCESS** |
| Pinned Lean / mathlib | `leanprover/lean4:v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (`lean-toolchain` / `lake-manifest.json`) |
| Interpretation | A subsequent **documentation-only** merge may advance the branch HEAD; it does **not** change the verified theorem-bearing squash checkpoint or independently certify new mathematics. Re-observe live HEAD and CI before citing a later state. |

### Exact source-normalized Rayleigh and true link observables

For each finite periodic spatial volume `H` and frozen Wilson coupling `b>0`, keep the original Gauss-law **centered physical source** `V_H` and define:

- `C_H>0`: the original centered spatial Wilson plaquette **reference-Haar covariance**, exactly `C_H=4‖V_H‖²`, **not** a substitute conditional posterior.
- `J_{H,b,e}≥0`: the **original** complete-boundary-pair-Haar integral of the squared genuine two-posterior signed GI expectation gap divided by the genuine positive FX posterior density-contrast variance, at the **actual** spatial link `e`.
- `j_{H,b,e}=4J_{H,b,e}/C_H`, `L_H`: the source-normalized link response and **actual** positive spatial-link count.
- `R_{H,b}=∑_{e}j_{H,b,e}=(4/C_H)∑_{e}J_{H,b,e}>0`: the exact full original centered-source physical GL Rayleigh **value** at each fixed finite `H,b>0`. A lower bound for this one source is **not** coercivity for every physical Hilbert vector.

The exact finite-spatial-link / spatial-plaquette counts coincide (`P_H=L_H`), and the proved original Haar covariance upper bound is `C_H≤24L_H`. The following statements are Lean-formalized **without changing the source, true posterior, receiver, or measure**:

| Stages / PRs | Proved scope | Limit |
| --- | --- | --- |
| [AAH–AAK, #5973–#5976](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5976) | Strict positivity of the actual fixed-`H,b` centered Rayleigh; exact original full-link decomposition `R=∑j_e`; one positive true posterior response link exists at every fixed volume. | `inf_H R_{H,b(H)}>0` is **not** proved. |
| [AAQ–AAU, #5982–#5986](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5986) | Original spatial Haar transport, true Wilson one-slab kernel and positive Perron vacuum translation symmetry, **both interacting posterior laws**, original GI/FX covariance; unconditional `M₂≤3R²` and participation `P≥1/3`. | Relative participation alone does not control absolute response. |
| [AAV #5987](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5987) | One **entire true spatial direction** has `j_e≥R/L_H` at every link; at least `1/3` of original links exceed the **full** mean threshold. | The threshold `R/L_H` may decay with volume. |
| [AAW #5988](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5988) | One true link with `j_e≥3c/L_H` **suffices** for `R≥c`; a uniform floor `R≥c` **requires** a (possibly different) link with `j_e≥c/L_H`. | The factor-3 sufficient and factor-1 necessary premises are distinct; no uniform witness exists by this argument alone. |
| [AAX / AAX2 #5989](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5989) | An authentic unnormalized **single** posterior response `J_e≥ε≥0` implies `R≥ε/18`, using `C_H≤24L_H`. The actual pointwise signal is `S(z)=Δ(z)²/Q(z)`, and `J_e=∫S\,dμ_H`. | A common **`ε>0`** is not constructed. |
| [AAY #5990](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5990) | On a measurable original outer pair-Haar event `E_H`, if `μ_H(E_H)≥ρ`, `|Δ|≥δ`, and `0<Q≤q`, then `J_e≥ρδ²/q`. All-volume **conditional** `R≥ρδ²/(18q)`. | Common positive `ρ,δ` and an appropriate event are unproved. |
| [AAZ / AAZ2 #5991](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5991) | **Unconditionally:** at each fixed `H,b>0` some actual link's centered GI gap `Δ` is **not zero pair-Haar-a.e.** Define the genuine **unweighted** moment `G_{H,b,e}=∫Δ²\,dμ_H`. Given a true FX cap `Q(z)≤q`, the unweighted gap square is **automatically integrable** and `G≤qJ_e`. A common moment `G≥m>0` and a common `q>0` imply **conditionally** `R≥m/(18q)`. | Neither a common positive **`m`** nor a valid common **`q`** for the intended coupling family is established by these eight new theorems. |

Here `Δ` is always the **same** original signed GI expectation gap for the centered physical Gauss-law source under two *interacting* Wilson one-link posteriors; `Q` is their original positive FX **Haar-`L²` density-contrast variance**, and `μ_H` is the original **outer pair-Haar** boundary measure. `Q` is **not** the bounded compensated two-context plaquette-minor energy `Q_GI`.

### The remaining genuine analytic obstruction

**OPEN:** construct, independently of the unknown `R_{H,b}`, a common `m>0` with one actual link per volume and `∫Δ_{H,b(H),e_H}²dμ_H≥m`, together with a compatible positive FX upper envelope `q`. Qualitative non-a.e.-zero at every finite `H` does **not** imply a positive volume-uniform second moment or event mass. The historical [JL posterior FX envelope](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5658) has the fixed-`b` volume/link/context-independent bound `Q≤(e^{16b}-e^{-16b})²`, **but** its current proof inherits five old finite-grid `native_decide` axioms; it is *not silently imported* into the AAZ/AAZ2 standard-axiom-only chain. Any varying-`b(H)` use needs a common envelope and exact dependency accounting.

Even a future positive source-specific fine-zero `R≥c` does **not** alone settle full physical-Hilbert coercivity, a **common** positive-fine interval, the same endpoint source transport (**E/F**), all-depth estimates, **H1–H4**, Osterwalder–Schrader/Wightman reconstruction, or the **continuum four-dimensional Yang–Mills mass gap**. The earlier [PZ37ZA #5935](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5935) **disproved** the distinct bounded *compensated two-context* `Q_GI/N_H` uniform floor. Do **not** confuse this genuine no-go with the original full-link/full-boundary-pair-Haar posterior GL Rayleigh studied here.

### Reproducibility and evidence

The source-level checkpoint for AAZ/AAZ2 is the exact PR head `d769e275d016b6645e924a116acb0d7653f7e9a0`, not the squash merge SHA. In a locally checked-out copy of that **exact commit**, with the repository's pinned toolchain/manifest, the changed theorem leaves are:

```text
MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapMomentCriterionV5_PZ37AAZ
MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapAutomaticIntegrabilityV5_PZ37AAZ2
```

For each changed theorem inspect the **complete source and imports**, dependent signatures, exact pinned mathlib APIs, final build, `#print axioms`, changed-file diagnostics, and independent **completed** CI receipt. Neither a queued/in-progress job nor a docs-only commit is a mathematical proof receipt.

**[Current proof gates, next analytic priorities, and historical record → ROADMAP.md](ROADMAP.md)**

---

## Historical checkpoint archive (2026-10-27; preserved)

The following sections retain prior verified finite-volume results and **historical** PR-specific source/merge SHA receipts. Their phrases such as “next PZ37ZI” and “latest/current checkpoint” were true **at the dated checkpoint only**, and are superseded as a *current status* by the 2026-10-29 section above. Historical theorems and no-go claims are retained; an old open gate later closed by a newer theorem is not silently reopened.

> **HISTORICAL VERIFIED THEOREM CHECKPOINT — 2026-10-27 JST · PZ37ZI [PR #5947](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5947) MERGED.** Only theorem authority `formal/real-hilbert-uniform-coercive-strong-limit`; genuine theorem-bearing squash [`87f187014c78222fd84e275a8d3b8bc19e6d6a36`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/87f187014c78222fd84e275a8d3b8bc19e6d6a36) matches canonical HEAD immediately after squash; exact tested source `f3a849f736334be71c6424f7ba6aa3a769249eda`. Exact-head [CI #40491398111](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40491398111): **11,107/11,107 SUCCESS**, changed Lean warnings/errors **0/0**, all four public theorem axiom reports only `propext`, `Classical.choice`, `Quot.sound`, independent MCP completion receipt **SUCCESS**. Below PZ37ZH/ZG/ZF/ZA paragraphs remain **dated historical checkpoints**, not current theorem HEAD.

### PZ37ZI: quantitative O(t²) for TRUE Wilson physical full-link GL mass

With unchanged original SU(2) Wilson normalized physical transfer `T_t`, genuine Gauss-law unit `U`, exact original interacting TWO Wilson posterior density-gap/variance full-link/full-boundary Haar mass `M_GL`, define `F_t=U-T_tU`. Let `B_H` be the **literal** original one-slab finite-H Wilson spatial-plaquette + temporal crossing global action budget, and `L_H` actual spatial-link count. For **every finite H**, **every frozen b>0** and **every nonnegative fine t**, the new Lean theorems close:

```text
‖T_t-T_0‖ ≤ 2 B_H t,
‖F_t‖ ≤ 2 B_H t,
0 ≤ M_GL(H,b;F_t) ≤ [2 L_H / exp(-16b)] (2 B_H t)².
```

In the actual sufficiently small positive-fine interval supplied by PZ37ZF/PZ37ZH, the same numerator is **strictly positive**, despite its rigorous quadratic upper decay. This improves PZ37ZE's qualitative fixed-H `M_GL(F_t)→0` to a uniform-in-fine explicit **O_H,b(t²)** budget, without ANY posterior replacement. `B_H` and `L_H` depend on volume; nothing here proves the source-normalized Rayleigh ratio tends to zero or admits a uniform positive lower bound.

**Next precise tangent gate (PZ37ZJ tentative):** use JG's proved genuine strong Haar-`L²` derivative `A_t=R_tU = U+t D_H+o(t)`, with nonconstant spatial Wilson-action profile `D_H`; use AQ's raw operator-norm continuity `‖R_t‖→1`. The candidate normalization-INVARIANT projected limit is `P_(U⊥) F_t/t → -P_(U⊥) D_H ≠ 0`: projecting perpendicular to the constant source removes the unknown derivative of the scalar operator norm. This projection and its positive slope are **not yet Lean-formalized**; do not claim `F_t/t` itself has a limit until actual operator-norm-normalizer differentiability is proved. Finite-H posterior GL Rayleigh limit, H-uniform coercivity, compatible endpoint E, arbitrary depth F, H1–H4, and continuum 4D Yang–Mills mass gap remain **OPEN**. The separately disproved PZ37ZA bounded compensated two-context `Q_GI/N_H` floor must not be reintroduced.

> **HISTORICAL VERIFIED THEOREM CHECKPOINT — 2026-10-27 JST · PZ37ZH [PR #5945](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5945) MERGED.** Only theorem-authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Verified theorem squash [`c2101b5596689ed6dd0939aad60b8c2884f6e3ee`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/c2101b5596689ed6dd0939aad60b8c2884f6e3ee); distinct tested source `8c258a37a04187cc6c708eef354e88682d7a7f5e`; exact-head [CI #40489013358](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40489013358): **11,093/11,093 SUCCESS**, changed Lean warning/error **0/0**, seven public `#print axioms` reports each restricted to `propext`, `Classical.choice`, `Quot.sound`; independent MCP completion receipt **SUCCESS**. Older PZ37ZG/ZF/ZA checkpoints below are historical, not the latest theorem HEAD.

### PZ37ZH: the TRUE Wilson physical cancellation equals literal depth-one source

At each genuine finite SU(2) spatial `H` and frozen `b>0`, take nonnegative fine `t` and the explicit real signed coefficient vector `a=(1,-1)`; keep the actual adjacent schedule `beta_0=b`, `beta_k=t` for `k>0`. The unchanged HJ Gauss-law physical Hilbert synthesis and actual norm-normalized physical Wilson transfer satisfy **in the ORIGINAL Hilbert space**

```text
S_1(1,-1) = U - T_t U = F_t,               for all t >= 0.
M_GL(H,b;F_t)=0  <->  F_t=0,              for all t >= 0.
F_t != 0  ->  0 < M_GL(H,b;F_t)/||F_t||^2
                 <= 2 |Links(H)| exp(16b).
```

The original OX all-depth source/whole-original-posterior GL kernel theorem supplies the zero-locus equality with genuine physical link and boundary contexts. PZ37ZF proves `F_t !=0` throughout a sufficiently small **positive** fine interval at each fixed `H`; thus the strictly positive **pointwise** physical-source-normalized Rayleigh bound is unconditional on that interval. The genuine two-interacting-Wilson posterior laws, their density-contrast variance, full spatial-link/full physical boundary-pair Haar integration and original Gauss-law physical source are all unchanged.

**Still OPEN:** an `H`- or fine-uniform numerical positive physical-norm coercivity constant; the fine-zero limit of the ratio; compatible endpoint E, a common positive-fine window for arbitrary depths F, H1–H4 and the continuum Yang–Mills mass gap. The physical cancellation `F_t→0` makes the coefficient-frame no-go compatible with strictly positive physical Rayleigh at each `t>0`; the PZ37ZA-disproved bounded two-context `Q_GI/N_H` lower floor must never be revived.

**Next genuine analytic gate (PZ37ZI tentative):** connect the already verified JG strong Haar-`L²` first variation of the TRUE unnormalized Wilson Haar row (with nonconstant spatial Wilson-action tangent) to the actual norm-normalized `F_t`. Separate scalar normalization and the nonconstant physical tangent; determine which fixed-`H,b` positive-fine source-norm bounds follow without silently assuming transfer-norm differentiability, posterior covariance uniformity or volume independence.

> **HISTORICAL VERIFIED THEOREM — 2026-10-27 JST · PZ37ZG [PR #5943](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5943) MERGED.** Sole theorem-authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Verified theorem-bearing squash SHA [`49467c2542e4a4b565ec480f04884f9c97c57abe`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/49467c2542e4a4b565ec480f04884f9c97c57abe); tested source SHA `77d50b0c0d6bc90aa3b8a243bdf3ae50aeef37e8`; exact-head [CI #40483971949](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40483971949): **11,092/11,092 SUCCESS**, changed-file warning/error **0/0**, all four new public `#print axioms` restricted to `propext`, `Classical.choice`, `Quot.sound`, independent MCP completion receipt **SUCCESS**. The older PZ37ZF/PZ37ZA "CURRENT" headings below are dated historical checkpoints, not the live theorem HEAD.

### PZ37ZG: original Wilson physical-source-normalized GL Rayleigh bounds

For the **unchanged genuine two-interacting-SU(2)-Wilson-posterior** full spatial-link and pair-boundary Haar GL mass, define `R(H,b;f)=M_GL(H,b;f)/‖f‖²` only as a physical Rayleigh quotient for **nonzero** Gauss-law Hilbert source `f`. At each finite `H` and frozen `b>0`,

```text
0 ≤ R(H,b;f) ≤ 2 |Links(H)| / exp(-16b),      f ≠ 0.
```

PZ37U supplies a strictly positive **model-dependent** lower `c(H,b,t,r)>0` on nonzero source vectors in each finite genuine right-Krylov physical source subspace; PZ37ZG transports it to the **ratio** while preserving the explicit upper bound independent of fine coupling/depth at fixed `H,b`. PZ37ZF supplies a genuine interval of small positive fine `t` with `F_t=U-T_t U ≠ 0`; PZ37ZG proves `0≤R(H,b;F_t)≤2|Links(H)|exp(16b)` there. The new file does **not** separately identify the specific `F_t` with the `HJ` depth-one synthesis in a named Lean theorem, and does **not** prove a fine-uniform positive lower bound or `lim_(t↓0)R(H,b;F_t)`. Unnormalized `M_GL(F_t)→0` and failure of a coefficient-ℓ² frame do **not** imply a physical norm coercivity no-go.

**Next precise gate (PZ37ZH tentative):** formalize the literal `F_t=S_1(1,-1)` bridge, derive pointwise strict normalized GL positivity from the original `OX/U` posterior kernel comparison, and determine whether the normalized direction has an analytic leading fine jet whose actual Wilson posterior covariance has a controlled positive limit. Any `H`-uniform estimate, common physical endpoint E, all-depth common window F, H1–H4 and continuum gap remain **OPEN**. PZ37ZA's disproved bounded compensated *two-context* `Q_GI/N_H` density cannot be reintroduced.

> **HISTORICAL VERIFIED THEOREM CHECKPOINT — 2026-10-27 JST · PZ37ZF [PR #5941](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5941) MERGED.** Only theorem-authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`; verified squash/HEAD: [`2d59cfc970cd358e29263577e2f8c76c688e35f9`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/2d59cfc970cd358e29263577e2f8c76c688e35f9). Exact-source CI [#40479003824](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40479003824): **11,091/11,091 SUCCESS**, changed Lean warning/error 0/0, four new public theorem axioms only `propext`, `Classical.choice`, `Quot.sound`. The earlier text below headed “Latest verified theorem checkpoint ... PZ37ZA” is the **historical #5935 checkpoint**, not the current theorem HEAD.

### Verified PZ37ZB–ZF: genuine full-link GL mass versus physical-source norm and fine scale

| Stage | Genuine original Wilson / interacting posterior result | Exact limitation |
| --- | --- | --- |
| [PZ37ZB #5937](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5937) | The true full-link three-mode GL Gram has determinant **zero at fine `t=0`** and admits no positive coefficient-ℓ² frame there. | This is a coefficient representation degeneracy, not a physical-source coercivity no-go. |
| [PZ37ZC #5938](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5938) | For **every** Gauss-law physical `f` and real spatial-link patch `S`, `M_GL(H,b;f,S) ≤ 2 exp(16b) |S| ‖f‖²`. | Upper bound; link count remains extensive. |
| [PZ37ZD #5939](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5939) | For **all finite Krylov depths** and all fine `t≥0`, the original GL coefficient Gram satisfies `B_GL ≤ (1+2 |Links(H)| exp(16b)) P_phys` in quadratic forms; the same factor controls the three-mode trace above. | Lower comparison `c_H`, small-fine radius and physical endpoint compatibility are still not volume-uniform. |
| [PZ37ZE #5940](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5940) | For the **true** normalized Wilson transfer `T_t`, `M_GL(H,b;U-T_tU) ≤ 2 |Links(H)| exp(16b) ‖T_t-T_0‖² → 0` at fixed `H,b` as `t↓0`. | Does not imply the normalized-source ratio tends to zero. |
| [PZ37ZF #5941](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5941) | For any `δ,ε>0` there is a **strictly positive** `0<t<δ` with **nonzero** original Gauss-law source `U-T_tU` and `M_GL(H,b;U-T_tU)<ε`; hence no coefficient-ℓ² lower frame **uniform over a punctured fine window** for coefficients `(1,-1)`. | `‖U-T_tU‖→0` as well: no disproof of `M_GL(f)/‖f‖²` lower control, all-link endpoint coercivity, H1–H4 or continuum mass gap. |

**Next genuine mathematical gate:** Analyze the original **physical-source-normalized** ratio `M_GL(H,b;U-T_tU)/‖U-T_tU‖²` along positive fine, actual Wilson posterior covariance and the *same endpoint source* across volumes/scales. Do not re-propose PZ37ZA's disproved compensated **two-context** `Q_GI/N_H` floor. The SU(2) Wilson kernel, the interacting posterior laws, Haar reference and Gauss-law physical Hilbert source are unchanged.

> **Latest verified theorem checkpoint, 2026-10-27 JST — PZ37ZA [PR #5935](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5935) MERGED.** The genuine SU(2) Wilson action, two original interacting Wilson posterior laws, transfer-compensated GI bounded functionals, spatial product-Haar REFERENCE Hilbert space, original Gauss-law physical sources, and frozen/fine couplings are all retained. PZ37Q–Y proved **finite-volume** physical rank 3 and original integrated posterior GL three-mode coercivity, including the exact sharp `det G_H^GL ≥ c_H³D3(H,t)>0`; this remains valid. PZ37Z separately proved an IF-AND-ONLY-IF threshold/activity criterion for the compensated TWO-CONTEXT local GI minor energy `Q_{H,b}=Σ_p d_{H,b,p}²`, divided by the actual count `N_H`. **PZ37ZA #5935 now DISPROVES the EXISTENCE side of that two-context criterion:** original Haar-centered Wilson plaquette sources have finite Gram-row bound `≤24` from genuine four-link support and product-Haar orthogonality; the true compensated two-context GI functional has norm `≤2E_b²`. Hence **`Q_{H,b}(e,e',z,z') ≤ 96 E_b⁴` for every finite H and EVERY actual pair of links/boundary contexts**, while `N_H≥2(H+1)`, so the normalized `Q/N_H` cannot admit a positive H-uniform floor at fixed frozen `b≥0`, even with H-dependent contexts. For varying `b_H`, the same no-go holds under the common genuine Harnack envelope `(4E_{b_H}²)²≤K`, since `Q_H≤6K`. This is a no-go for **only this bounded TWO-ROW COMPENSATED sufficient criterion**, NOT for the genuine all-link/all-context integrated posterior GL norm, compatible endpoint physical sources, any continuum Yang–Mills mass gap or Yang–Mills existence. Their uniform coercivity, endpoint E, arbitrary-depth positive-fine F and H1–H4 remain OPEN. PZ37Z's equivalence stays mathematically valid, while its fixed-b witness-existence side has been proved false.

**日本語要約（2026-10-27 PZ37ZA統合時点）：** 原SU(2) Wilson・二相互作用posterior・Gauss-law物理Hilbert・参照積Haarを変更せず、PZ37ZA #5935では本物の四リンク支持から中心化Wilsonプラケット源のGram行和 `≤24`、元の補償済み二文脈GI汎関数ノルム `≤2E_b²` をLean4証明した。したがって**全有限H・任意の実Wilsonリンクと境界文脈**について **`Q_{H,b}=Σ_p d_{H,b,p}²≤96E_b⁴`**。本物のプラケット数 `N_H≥2(H+1)` と合わせ、固定 `b≥0` に対する文脈選択型の**二文脈補償済み `Q_H/N_H` の一様正下界は不可能**と証明した。変動結合 `b_H` でも `(4E_{b_H}²)²≤K` を共通に満たせば `Q_H≤6K` により同じ結論。PZ37Zの必要十分条件は維持されるが、この量化では実在側が否定された。**全リンク・全文脈で積分する元のGL質量、PZ37Yの有限3モードGL Gram、真のendpoint source transport、U0に代わる一様物理評価、E/F/H1–H4・連続体質量ギャップの不可能性を主張しない**。

**[Acceptance gates and next proofs → ROADMAP.md](ROADMAP.md)**

## 1. Archived 2026-10-27 theorem authority, pinned environment, and verified checkpoint

| Item | Verified value |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| **Latest verified theorem-bearing merge checkpoint (PZ37ZA)** | [`56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300) (PZ37ZA #5935 squash merge) |
| Latest verified theorem PR at this checkpoint | [#5935 PZ37ZA](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5935), after [#5933 PZ37Z](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5933), [#5931 PZ37Y](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5931) and earlier PZ37Q–X. |
| Exact **tested source** SHA (distinct from squash SHA) | PZ37ZA source `780ad873a0e678b5a70cd5d8235682436ea28b7c`; PZ37ZA squash `56e3ee8b7bda5454f8cc2adc51abe14b5dcd7300`. |
| [PZ37ZA exact-head CI #40455326601](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/40455326601) | SUCCESS, **11092/11092** Lean, all **13** new `#print axioms` restricted to `propext`/`Classical.choice`/`Quot.sound`; FIVE changed Lean files error/warning **0/0**; no `sorryAx` or new axiom; MCP exact-head completion receipt SUCCESS. |
| Pinned Lean | `leanprover/lean4:v4.30.0-rc2` (see `lean-toolchain`) |
| Pinned mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (see `lake-manifest.json`) |
| Live branch | [re-observe the current theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) |

The checkpoint is deliberately **a dated theorem-bearing merge**, not a claim that the branch HEAD cannot advance when these documents or subsequent theorems merge. A documentation-only commit does **not** prove new mathematics. Order of evidence: **fresh authoritative HEAD → exact Lean declarations and their imports → CI at the exact source SHA and `#print axioms` → README/ROADMAP → historical discussions**. The repository's default `main` is **not** the theorem carrier.

## 1A. Historical post-PC evidence (PD–PN; superseded checkpoint)

The following archived PD–PN results describe their original proof-time status. Any older claim here that `D3>0` or physical three-mode rank 3 remains OPEN is superseded by PZ37Q–W above. These historical proofs used the original physical Wilson kernel and the actual spatial product-Haar reference; the two interacting posteriors were never replaced by independent Haar posteriors.

| Stage | Proved in Lean 4 | Not proved by this stage |
| --- | --- | --- |
| PD–PE | Third Schur orthogonality, `‖R₂‖² = Δ₂ D₃`; genuine signed GI and finite Krylov GL mass implications under nonzero residual | `R₂ ≠ 0` unconditionally |
| PF–PH | Continuous spatial representatives; `D₃ > 0 ↔` nonzero genuine 3-configuration determinant when `Δ₂>0` | Existence of the required spatial triple |
| PI–PJ | Exact normalization scaling; original one-slab and **two-slab literal double-Haar complete Wilson kernel**; positive third Hankel iff nonzero literal 3-point minor under rank-two gate | A nonzero original literal minor |
| PK–PM | Complete original two-slab action `S(X,A)+S(A,B)`, spatial-Wilson-weighted Haar Ward identity, mixed second action-moment affine relation, **formal cubic minor coefficient identically zero** | Degree-two *formal jets* are not automatically full Taylor jets of the actual integral |
| PN #5839 | Pinned mathlib exponential `n=3` bound; actual complete one/two-slab kernel residuals are `O(t³)` with the finite-volume original budget and true literal double-Haar remainder bound | Equality of integrated polynomial coefficients with PK moments, actual minor `O(t⁴)`, nonzero quartic/higher witness |

The explicit finite-volume remainder is

```text
Q(X,A,B) := S(X,A) + S(A,B) ≤ 2 M_H
R_H(t,B) := ∫ dμ_H(A) ∫ dμ_H(X)
              [K_t(A,B) K_t(X,A) - (1 - t Q + t² Q²/2)]
‖R_H(t,B)‖ ≤ ‖2 t M_H‖³, when ‖2 t M_H‖ ≤ 1.
```

The bound is **finite-volume**, not H-uniform; it does not imply `U0`, an endpoint scale transport, or any continuum mass gap. To obtain the actual `O(t⁴)` 3-point determinant, next identify the literal integrated degree-two coefficients with PK/PM moment data, then transport the uniform cubic remainders through the pointwise determinant.

## 2. Actual model: do not conflate these objects

1. **Original physical Wilson model.** The genuine interacting SU(2) spatial Wilson action, one-slab kernel, normalized joint ground-state/Perron transfer, and Gauss-law-invariant physical Haar-`L²` sources. Frozen `b = β_n` and fine `t = β_{n+1}` are distinct couplings.
2. **Two actual interacting posterior laws.** `p_{0,b}` and `p_{π,b}` are not independent Haar laws. SU(2) Haar is a reference measure for the actual densities, and pair-Haar integrations over genuine full boundary contexts are another operation.
3. **Actual signed source response.** `G_{H,b,e,z}(f)` is the original signed expectation/physical response of the true receiver under those two interacting posteriors. It retains joint half-density, transfer normalization and physical link insertion.
4. **Different operators and proof gates.** The original unnormalized Wilson Haar-reference `A_W`, normalized physical conditional-projection Dirichlet operator `D₁₂`, original signed GL/GI detector, finite-dimensional physical source Gram, and limiting physical time evolution are **different mathematical objects**. Restricted finite-volume positivity of one does not provide an absolute continuum mass gap for another.

In particular, **two different quantities historically called `Q` must be kept distinct**:

- `Q_post(b,e,z) = ∫(p_{0,b}-p_{π,b})² dν`: a *posterior density-contrast* norm in the earlier genuine GI bound.
- `Q_GI(H,b,e,e',z,z') = Σ_{p∈P_H} d_p²`: the *transfer-compensated original local GI-minor square energy* of LY onward. `Q_GI` in the equations below **never** denotes posterior contrast.

The compensation is purely scalar, not a change of physical law:
`d_p = ||T_{H,b}||² Δ_p`, where `Δ_p` is the actual original two-context local Wilson GI determinant. Its true underlying physical source remains `xU+yW_{H,p}U`.

## 3. What is proved: authentic Wilson source detection

The original **spatial** static two-context Wilson determinant is
$$
\Delta_W(z,z')=G_{e,z}(1)\,G_{e',z'}(W_H)-G_{e,z}(W_H)\,G_{e',z'}(1).
$$

- [JI–JK, #5656–#5657](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5657): actual spatial minor definition, anchored centering, exact Haar-moment obstruction, and original fine-coupling derivative `M'_0=-Δ_W/2`.
- **[LM, original nonzero two-context minor](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoContextSpatialGIMinorNonzeroV5_LM.lean)**: for every fixed finite H, **b>0**, pair of actual physical links and prescribed initial boundaries, **some two genuine original interacting-Wilson contexts** yield `Δ_W≠0`. The former README/ROADMAP statement “original spatial nonzero GI minor OPEN” is **obsolete**. See `p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts`.
- **[LN–LP, true physical and local witness](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalPlaquetteGIWitnessV5_LO.lean)**: original constant-unit and Wilson spatial physical source planes, genuine local-plaquette GI minors, quantitative original physical two-source Frobenius coercivity and a real plaquette witness.
- [LS–LX, genuine transfer/Harnack estimates](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTransferNormalizationCompensatedCoercivityV5_LW.lean): original posterior/receiver norm, physical one-link joint-density Harnack and contrast envelope. The positive original contrast scale is
  $$
  E_b=e^{8b}(e^{16b}-e^{-16b})>0 \quad(b>0).
  $$
  Bounds on the compensated receiver are volume-independent *at fixed b*, but the resulting positive **coercivity floor** is not thereby uniform in H.

LM **closes the finite-volume spatial nonzero witness**, *not* all higher-Krylov source injectivity or continuum dynamics. A conditional small-positive-fine derivative consequence has to preserve its specific context, fine-coupling window and source; it does not extend automatically to all depths.

## 4. Quantitative genuine GI energy and physical spatial frame (LY–MK)

Fix a genuine finite H, `b>0`, physical links `e,e'`, and actual interacting-Wilson contexts `z,z'`. Define

$$
N_H=|\mathcal P_H|,\qquad
Q_{\rm GI}=\sum_{p\in\mathcal P_H}d_p^2,\qquad
k_{H,b}=\frac{Q_{\rm GI}/N_H}{10E_b^2}.
$$

These are computed from the **original finite plaquette carrier** and the **original two posterior GI determinants**. Let

$$
R_p(x,y)=G_{e,z}(xU+yW_{H,p}U)^2+
           G_{e',z'}(xU+yW_{H,p}U)^2.
$$

The true source is **p-dependent**: an average of these responses is not a single p-independent endpoint source.

| Stage / verified PR | Exact proved scope |
| --- | --- |
| **[LY, local square energy](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalGICompensatedSquareEnergyV5_LY.lean)** | Cancellation-free `Q_GI`; authentic positive-energy witness contexts; local max attaining `d_p² ≥ Q_GI/N_H` and original physical `κ_p ≥ Q_GI/(10N_HE_b²)`. This **mean-plaquette mechanism already occurs in LY**. |
| [LZ–MA, variance and original local ceiling](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCompensatedGIUniformLocalMomentBoundV5_MA.lean) | Exact mean/variance decomposition and `d_p² ≤ (4E_b²)²=16E_b^4` on every true plaquette; upper moment/variance bounds, **not** a uniform positive energy-density lower bound. |
| [MB #5729](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5729) | True energy-active original plaquettes `A={p : d_p² ≥ Q_GI/(2N_H)}` and their finite-H density floor. Duplicate exact-source CI recovery [#5730](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5730) added no new mathematical content. |
| [MC #5731](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5731) | Every actual active p has true positive original physical coercivity; verification-only [#5732](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5732) was closed **unmerged**. |
| [MD #5733](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5733), [ME #5734](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5734) | Active-to-full genuine spatial response `R_p` lower bounds; initial full response bound quadratic in `Q_GI/N_H`. |
| **[MF #5735](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5735)** | Eliminates the half-mean activity truncation: **linear** finite-H full original spatial response bound `k_{H,b}` via a pointwise original physical source inequality and exact finite sums. |
| [MG #5736](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5736), [MH #5737](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5737) | Exact physical 2×2 spatial-response Gram via polarization; Gram positivity and `det G≥kA≥k²>0` at real positive-energy contexts. |
| [MI #5738](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5738), [MJ #5739](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5739) | Constructive adjugate inverse; uniqueness, squared inverse stability, exact additivity/homogeneity and **two-input Lipschitz** bound for arbitrary real Gram dual coordinates at fixed original contexts. |
| **[MK #5740](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5740)** | Separate reusable theorems selecting **one actual p** with `d_p²≥Q_GI/N_H`, genuine `κ_p≥k` and `k(x²+y²)≤R_p(x,y)` for all real x,y at the same genuine contexts; refines/organizes LY's existing maximum-witness result, without a new physical assumption. |

Two particularly useful **already checked** finite-H inequalities are
$$
\boxed{\quad
k_{H,b}(x^2+y^2)\leq
\frac{1}{N_H}\sum_{p\in\mathcal P_H}R_p(x,y),\qquad
\exists p\in\mathcal P_H:\ k_{H,b}(x^2+y^2)\leq R_p(x,y).
\quad}
$$
When genuine `Q_GI>0`, `k_{H,b}>0`. The existential plaquette/witness may depend on H, b and the original contexts.

For the **same actual spatial response**, set
$$
A=\tfrac1{N_H}\sum_pR_p(1,0),\quad
C=\tfrac1{N_H}\sum_pR_p(0,1),\quad
B=\tfrac1{2N_H}\sum_p[R_p(1,1)-R_p(1,0)-R_p(0,1)].
$$
Then the exactly polarized original spatial Gram `G=[[A,B],[B,C]]` satisfies
$$
\frac1{N_H}\sum_pR_p(x,y)=Ax^2+2Bxy+Cy^2,\qquad
G\succeq k_{H,b}I,\qquad
AC-B^2\geq k_{H,b}A\geq k_{H,b}^2>0.
$$
MI/MJ give a **fixed-context inverse** with
$$
G^{-1}(s,t)=
\left(\frac{Cs-Bt}{AC-B^2},\,\frac{At-Bs}{AC-B^2}\right),\qquad
k_{H,b}^{\,2}\|G^{-1}v-G^{-1}w\|_2^2\leq\|v-w\|_2^2.
$$

**Critical interpretation:** this is an original Wilson **spatial two-coordinate response frame**, with original `p`-dependent physical sources. It does **not** prove invertibility of the full physical transfer operator or positivity for all original physical Krylov sources; it is not a one-source endpoint theorem.

## 5. Original Wilson Gaussian, depth-two physical obstruction and all-depth quadratic branch: NT–OR

For the **unchanged original SU(2) temporal Wilson section** on true holonomies `x,g ∈ SU(2)`, with the already-proved real-eight feature `J`,

$
K_b(x,g)=\exp(b\chi(x^{-1}g))
=e^b\exp\bigl(-\tfrac b4\|J(x)-J(g)\|^2\bigr),\qquad b>0.
$

| Verified stage | Exact theorem-bearing content |
| --- | --- |
| [NT–NX, #5776–#5780](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5780) | Genuine signed Wilson–Perron coordinate moments, all-degree character Gram expansion, finite double-action energy identities, bounded Banach double signed functional and convergent exponential. |
| **[NY #5781](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedGaussianStrictV5_NY.lean)** | For **every** nonzero continuous real linear functional `L` on `C(SU(2),ℝ)`, the **complete** Gaussian double signed energy `T_L(K_b)>0` for all `b>0`. This specializes to strict positivity of the **original Wilson–Perron signed receiver's local Haar variance**; **not** to an arbitrary physical GI covariance. |
| **[NZ #5782](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianKernelSpanDenseV5_NZ.lean)** | By Hahn–Banach, `closure(span_ℝ {K_b(x,·) : x∈SU(2)}) = C(SU(2),ℝ)` for each fixed `b>0`; linear **span**, not merely a generated algebra. |
| **[OA #5783](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianAllFiniteStrictGramV5_OA.lean)** | For every finite *injective* family of genuine SU(2) holonomies and every nonzero real coefficient vector, `Σᵢⱼ aᵢ aⱼ K_b(xᵢ,xⱼ)>0`; finite point selectors establish nonzero signed evaluation, without rank assumptions. |
| **[OB #5784](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianMatrixPosDefV5_OB.lean)** | Literal original Gram is `Matrix.PosDef`, `IsUnit`, has nonzero determinant, and has `PosDef` inverse in the pinned mathlib. |
| **[OC #5785](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianFiniteInterpolationV5_OC.lean)** | At any finite set of distinct original SU(2) points and for any target vector `v`, coefficients `c=v ᵥ* M⁻¹` give `f(g)=Σⱼ cⱼK_b(xⱼ,g)` with **exactly** `f(xᵢ)=vᵢ`. Finite sections are linearly independent. |
| **[OD #5787](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoPosteriorGaussianSeparationV5_OD.lean)** | The original two interacting Wilson posterior conditional density contrast `D=p₀−pπ` defines a **nonzero** real bounded signed functional `L_D(v)=∫v(g)D(g) dμ_Haar`. Its self-pairing is the **exact original** posterior squared Haar distance (GA/FX lower bound); NY gives positive complete signed Gaussian energy and an original Wilson temporal kernel section distinguishing the two posterior laws. **Exact original physical GI compatibility:** `Δ_GI(f;e,z) = L_{D(H,b,z.right,e)}(R_f(z,·))` for every actual Gauss-law physical Hilbert source `f`, with `R_f` the **unchanged FF signed receiver fiber**. Its general nonzero evaluation for physical `f` is NOT proved. |
| **[OE #5789](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSignedReceiverNonannihilationV5_OE.lean)** | Exact original FF receiver two-row signed functional square equals the genuine MD physical GI square on the same Gauss-law source xU+yW_pU. The previously proved LO two-context minor gives a positive two-row coefficient frame; MF/MK original Q_GI/N_H floor transports without changing any posterior. At selected true contexts the constant physical unit U itself satisfies (Q_GI/N_H)/(10 E_b²) ≤ L_D(R_U)²+L_Dprime(R_U)²; U is p-independent. No context- or H-uniform positivity asserted. |
| **[OF #5790](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalKrylovZeroSelectorSignedDensityFloorV5_OF.lean)** | Actual all-finite-depth right-Krylov zero-selector at scale n has true physical source exactly U for every nonnegative fine coupling beta(n+1), by GX. Therefore the same selected-context physical U floor is transferred exactly into the true signed receiver representation of that genuine right-Krylov coefficient source. Fixed frozen beta(n)>0; selected contexts and Q_GI/N_H coefficient may vary in scale/volume. |
| **[OG #5791](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalZeroSelectorAllDepthSameContextGIFrameV5_OG.lean)** | The genuine HF modal GI detector on each actual zero-selector coefficient is EXACTLY the same OD signed p0−pπ receiver functional on the unmodified physical U at fixed n; its output is identical across any pair of depths r,s. More strongly, for each fixed n with frozen beta(n)>0 and given actual links and initial boundary data, ONE pair of genuine interacting-Wilson contexts z,zprime can be chosen **before and independently of ALL r**, carrying the same positive original Q_GI/N_H coefficient in a two-row modal-square floor for every finite r. Arbitrary coefficient-source injectivity and cross-scale endpoint compatibility remain OPEN. |
| **[OH #5793](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOneRowAllDepthModalRankOpenV5_OH.lean)** | One of OG's TWO genuine original signed GI receiver rows can be selected ONCE at a fixed scale n and genuine Wilson context; its physical zero-selector detector squared value is at least HALF the actual (Q_GI/N_H)/(10 E_b²) floor for EVERY finite Krylov depth r. That **same real scalar HF modal map** has exact coefficient kernel finrank r; at each r there is a positive-radius detected coefficient ball around a0_r. For r>0 the rank-r coefficient kernel is not asserted to synthesize a nonzero physical source. No all-source rank assumption or volume-uniform floor. |
| **[OI #5794](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalKrylovModalKernelSplitV5_OI.lean)** | For the real original HF modal GI receiver row, define a coefficient remainder `k_r(a) = a - t_r(a) a0_r`, `t_r(a) = Φ_r(a)/Φ_r(a0_r)` using OH's **proved nonzero** denominator. OI proves `Φ_r(k_r(a))=0`, exact coefficient split, and the original HJ physical Hilbert source identity `S_{n,r}(a)=S_{n,r}(k_r(a))+t_r(a)U`. It also proves, by the original HF/OD signed GI equality, that the true two-posterior FF receiver of `S_{n,r}(k_r(a))` vanishes at the SAME selected real link/context, for any a and every finite r. This is a ONE-context null, not a global invisible nonzero physical source claim. |
| **[OJ #5796](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCrossContextPhysicalResidualMinorV5_OJ.lean)** | For *two actual* original interacting-Wilson HF modal GI detector rows `Phi_0=Phi(e,z)` and `Phi_1=Phi(e',z')`, the genuine cross-minor `M_01(a)=Phi_0(a0)Phi_1(a)-Phi_0(a)Phi_1(a0)` equals `Phi_0(a0)Phi_1(k_r(a))` and, using the original OD signed FF physical fiber, `Phi_0(a0)L_{D_1}(R_{S(k_r(a))})`. Given OH's **proved nonzero** anchor, all genuine link/context minors vanish **iff** the explicit OI residual lies in HJ's entire continuous GI detector kernel. Furthermore `ker S <= ker Phi_all <= ker Phi_0`; a **nonzero actual minor, if established**, would force a nonzero detectable Gauss-law physical residual. Any OH anchor-square floor controls the normalized U-direction coefficient; **at the historical OJ checkpoint the nonzero minor was not yet established; OM and ON subsequently close its depth-one small-positive-fine case**. |
| **[OK #5799](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFineEigenlineAllDepthCrossMinorObstructionV5_OK.lean)** | On the ORIGINAL normalized fine SU(2) Wilson physical transfer (at beta(n+1)), **if** the actual unit U is an eigenvector `T_fine U=cU`, all genuine right-Krylov modes are `c^j U` and every HJ physical source is `(Σ a_j c^j) U` for every finite depth. The original HF signed detector factors through this true one-dimensional physical source; therefore every OJ genuine two-context minor vanishes. Using OH's independently proved original frozen-beta nonzero anchor, at fixed n and frozen beta(n)>0 the all-depth equality `ker S_r = ker Phi_all,r` follows **in this physical eigenline branch only**. Conversely any truly nonzero minor forces `r>0`, `beta(n+1)>0` and `T_fine U` NOT to lie in the U eigenline. At actual fine beta=0 and r=0 the minors vanish unconditionally. Non-eigenline or a nonzero positive-fine minor has NOT been established. |
| **[OL #5801](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonSmallPositiveFineUnitNonEigenlineV5_OL.lean)** | IX gives the **actual original** SU(2) Wilson one-slab Haar-row difference derivative at fine beta=0 as half the *genuine spatial plaquette action difference*. The explicit IY identity and SU(2) central-twist boundaries satisfy W(B0)=0 and W(B1)>=2, so the derivative is >=1 while both row values equal 1 at beta=0. Mathlib calculus rigorously yields a positive volume-dependent interval `(0,delta_H)` on which `F_t(B0)>F_t(B1)`. IV transfers this literal pointwise nonconstancy to **physical non-eigenline `T_t U ∉ ℝU` for ALL t in that interval**, using the unmodified normalized fine Wilson transfer, Haar L² Gauss-law source and full Haar support. Under separate frozen beta(n)>0, IS/IU produce a NONZERO actual depth-one Krylov physical pivot with ZERO original GI response at one genuinely chosen context. **At OL's checkpoint, nonzero cross-context OJ minor/global visibility and arbitrary positive fine remain OPEN.** |
| **[OM #5803](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFineKrylovTwoContextMinorV5_OM.lean)** | **Actual nonzero original two-context minor** of `(U,T_tU)`: LM supplies authentic frozen spatial Wilson witness; JI provides the exact positive-fine derivative; OM proves equality with OJ's true zero/first right-Krylov HF modal GI cross-minor and detects the SAME nonzero physical depth-one pivot at a second genuine GI context. At each finite H and frozen `b>0`, both contexts are chosen before `t`; a fixed positive window `(0,δ_H)` works. No assumed rank or surrogate receiver. |
| **[ON #5804](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFineDepthOneGIPhysicalSourceInjectiveV5_ON.lean)** | From OM's genuine **nonzero 2×2 minor**, proves for **every** real depth-one coefficient pair `(a₀,a₁)`: both actual HJ all-context GI detector and genuine physical Gauss-law source synthesis have trivial kernel. Equivalently `U` and `T_tU` are independent in the actual physical Hilbert source space throughout OM's small-positive-fine interval. No statement for `T_t²U`, all positive fine or uniform quantitative bounds. |
| **[OO #5806](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDepthTwoKrylovSchurResidualV5_OO.lean)** | True depth-two coefficient selectors synthesize **exactly** `U,T_tU,T_t²U` in the original physical Gauss-law Hilbert space, and their HF modal evaluations match the same genuine two-Wilson-posterior GI gaps. OM's nonzero leading 2×2 minor persists at genuine depth two. An explicit **nonzero coefficient** Schur residual `R₂` is killed by the first two true GI rows; its synthesized physical source and third original signed GI response are computed exactly, but **not proved nonzero**. |
| **[OP #5807](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDepthTwoExactGIKernelV5_OP.lean)** | For the actual OO two GI rows with their proved nonzero leading minor, the **entire common coefficient kernel equals `ℝ·R₂`**. Actual `ker S₂ ⊆ ker Φ_all,2 ⊆ ℝ·R₂`. Moreover physical synthesis is injective **iff `S₂(R₂)≠0`**, and the full continuous genuine Wilson GI detector is injective **iff some third genuine link/context evaluates `R₂` nontrivially**. These are exact equivalences, **not an unconditional third-row or depth-two injectivity proof**. |
| **[OQ #5809](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFineQuadraticCollapseAllDepthV5_OQ.lean)** | From the EXACT OO Schur PHYSICAL source equation `S₂(R₂)=0` and OM's genuine positive-fine nonzero leading minor, derive the TRUE normalized Wilson quadratic relation `T_t²U=αU+γT_tU`. Prove every actual power and full right-Krylov physical source at **every finite depth** lies in the same two-mode physical plane. ON's already-proved actual two interacting-posterior receiver rows then show **`ker S_r=ker Φ_all,r` for ALL finite r** on this physical-collapse branch. Unconditionally at each finite H and small positive fine, **either** all-depth kernel equality holds **or** `S₂(R₂)≠0` in the true Gauss-law Hilbert space. No rank-3/third-GI response assumed. |
| **[OR #5810](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFineQuadraticAllDepthGLMassV5_OR.lean)** | Using the unchanged original two interacting Wilson posterior signed expectation-gap-square divided by genuine positive posterior density-contrast variance (GL/FX), prove the original full spatial GI/GL mass is NONNEGATIVE. On OQ's true quadratic physical-collapse branch, **at every finite Krylov depth**, `M_GL(S_r a)=0 ⇔ S_r a=0` and `S_r a≠0 ⇒ M_GL(S_r a)>0`. The unconditional small-fine dichotomy gives all-depth qualitative strict mass positivity OR an actual nonzero depth-two physical Schur source. No uniform numerical floor or genuine third-context detection follows. |
| **[OS #5812](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFinePhysicalNormCoercivityV5_OS.lean)** | ON's unconditionally proved true depth-one physical and all-context GI injectivity, combined with mathlib finite-dimensional inverse-Lipschitz theory, yields **strictly positive finite-volume and coupling-dependent coefficient-to-physical-Hilbert norm controls** and corresponding original GI norm controls throughout the small-positive-fine regime. If the actual OO depth-two Schur physical source is nonzero, OP upgrades this to full three-coefficient physical norm control at depth two. Together with OR, this proves a genuine unconditional small-fine disjunction: all finite-depth physically nonzero Wilson Krylov sources have positive original GL mass, **or** a positive depth-two physical coefficient norm-control constant exists. Neither the Schur nonzero branch nor a third true GI response is proved; no H-, fine-, depth-uniform constant or continuum gap is asserted. Exact-head [CI #39774820731](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39774820731): Lean 10880/10880 SUCCESS, 4/4 axioms, 0/0 changed warnings/errors, MCP receipt SUCCESS; [squash #5812](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/daf1c714f08ed57d42d9e5c3b92e12601bc61478). |
| **[OT #5814](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonContinuousPhysicalGIDetectionV5_OT.lean)** | LJ's positive **complete original Wilson** one-slab spatial Haar quadratic, LK's true SU(2) spatial gauge-fiber normalization, and LC's unmodified signed two-interacting-posterior receiver prove: every nonzero genuine Gauss-law physical source with a continuous pointwise gauge-invariant Haar-L² representative is detected by an actual Wilson GI context at positive frozen coupling. Original Schur detection follows conditionally on its nonzero physical source and regularity, with neither assumed. [PR #5814](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5814), exact-head [CI #39779364146](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39779364146), Lean 10881/10881, public axioms 5/5, no sorryAx. |
| **[OU #5815](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPhysicalTransferContinuousRangeV5_OU.lean)** | The unchanged full physical one-slab operator's actual A_phys† A_phys factorization and genuine continuous Moore–Aronszajn feature synthesis give a continuous Haar-L² representative to EVERY original (raw and normalized) Wilson transfer output of ANY Gauss-law L² input, at nonnegative fine coupling. Pointwise gauge invariance addressed separately by OV. [PR #5815](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5815), [CI #39781160365](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39781160365), Lean 10882/10882, axioms 3/3. |
| **[OV #5816](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPhysicalGaugeContinuousRangeV5_OV.lean)** | Original finite spatial SU(2) product Haar full support plus mathlib's continuous-to-L² injectivity upgrades true Gauss-law a.e. invariance of OU's continuous representative to pointwise gauge invariance. Hence every nonzero original normalized fine physical Wilson transfer output is detected by an actual original signed GI context (without assuming it is nonzero). [PR #5816](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5816), [CI #39791923530](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39791923530), Lean 10883/10883, axioms 4/4. |
| **[OW #5817](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllDepthGIKernelFaithfulnessV5_OW.lean)** | Actual right-Krylov sources U,T_fine U,T_fine²U,... have continuous gauge-invariant Haar-L² representatives at ALL finite depths and ALL nonnegative fine couplings, by true constant-unit representative + OU/OV. OT therefore proves UNCONDITIONALLY at every finite H and frozen b>0: **ker S_r = ker Φ_all,r for every r and fine t≥0**. A nonzero true Schur physical source is detected by a genuine third GI context, but physical Schur nonzero is still OPEN; no physical coefficient injectivity is asserted. [PR #5817](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5817), [CI #39852361096](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39852361096), Lean 10884/10884, axioms 5/5. |
| **[OX #5818](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllFineUnconditionalGLMassV5_OX.lean)** | Combining OW's unconditional physical/entire-original-GI kernel equality with OR's actual two-interacting-Wilson-posterior signed-gap-square GL mass positivity removes BOTH the historical quadratic-collapse assumption and small-positive-fine restriction: at all finite H, b_frozen>0, fine t≥0, finite r, **M_GL(S_r a)=0 ⇔ S_r a=0; S_r a≠0 ⇒ M_GL(S_r a)>0**. These are qualitative strictly finite-volume facts, NOT U0 or source rank-3. [PR #5818](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5818), exact-head [CI #39854681185](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39854681185), Lean 10885/10885, axioms 2/2, warning/error 0/0, MCP receipt SUCCESS; theorem-bearing squash [c73ea9f](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/c73ea9f21c28b60080f793383b344d0c78c4ca4a). |
| **[OY #5819](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPositiveFinePhysicalKrylovShiftV5_OY.lean)** | LJ's STRICT original complete one-slab SU(2) Wilson Haar quadratic positivity is identified with the true original Gauss-law physical Hilbert quadratic using genuine product Haar and both actual boundary halfweights (no independent-Haar surrogate). OW's continuous physical Krylov representatives imply at **every strictly positive fine t, finite H and finite r**: nonzero true physical source f=S_r a has **⟨T_raw(t)f,f⟩>0** and is not annihilated by the actual normalized fine Wilson transfer. The one-step shifted Krylov physical coefficient kernel is **exactly preserved**: `Σ a_j T_t^(j+1)U=0 ⇔ Σ a_j T_t^jU=0`. This does **NOT** prove the third physical mode independent, the full source map injective or uniform U0. [PR #5819](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5819), exact-head [CI #39856189021](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39856189021), Lean 10886/10886, six public axioms all standard-only, warning/error 0/0 and MCP receipt SUCCESS, squash [7569fcf](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/7569fcf984e8040c314bbe723f56393d1faf524b). |
| **[OZ #5821](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllIteratedFineKrylovNonzeroV5_OZ.lean)** | Extend OY's STRICT original complete positive-fine Wilson physical quadratic to EVERY actual transfer iterate: OU/OV preserve continuous pointwise Gauss-law representative under each normalized fine transfer; since the real initial right-Krylov S_r a is regular by OW, **S_r a≠0 implies T_t^k(S_r a)≠0 for EVERY k∈ℕ and t>0**. Combine ON's real original depth-one small-positive-fine physical source injectivity with this preservation to prove independent adjacent shifted two-mode physical sources for every k, WITHOUT claiming rank-3 of U,TU,T²U, any uniform quantitative lower bound U0, endpoint or continuum gap. [PR #5821](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5821), [exact-head scoped CI #39857992320](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39857992320): 10886/10886, four public `#print axioms`, no sorryAx or changed warning/error, independent MCP receipt SUCCESS; [squash feac7e9](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/feac7e92d3e56f5301d1f8ecbc66dceb4d74c011). |
| **[PA #5823](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllShiftTwoModePhysicalGramV5_PA.lean)** | ON/OZ genuine physical source injectivity persists at every shift k in one small-positive-fine interval; actual 2×2 Gauss-law Hilbert Gram PosDef, det>0, finite-dimensional norm control K_(H,b,t,k)>0 (not uniform). [#5823](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5823), squash `afd42dd8f`. |
| **[PB #5824](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPhysicalKrylovHankelMomentsV5_PB.lean)** | Original normalized self-adjoint Wilson transfer: `<T^i U,T^j U>=m_(i+j)` for every finite H, t>=0 and i,j; all finite Krylov physical Gram matrices equal the actual scalar moment Hankel matrices and are PSD. No three-mode positivity implied. [#5824](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5824), squash `c9e896755`. |
| **[PC #5825](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonStrictShiftedHankelMomentsV5_PC.lean)** | Actual all-shift rank-2 scalar Hankel strictly PosDef; `m_(2k)m_(2k+2)-m_(2k+1)^2>0` for every k in ON's one small-positive-fine interval. **NOT rank3.** [#5825](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5825), [CI #39869958440](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39869958440) 10889/10889, 3/3 axioms with inherited `native_decide` disclosed, squash `104e0008d`. |

**Remaining obstruction after verified OD–PC.** The sole explicit depth-two physical obstruction is still the original Schur source `S₂(R₂)` and its true signed GI evaluations. OQ proves that **if** that physical source vanishes, the actual Wilson unit orbit closes quadratically and all finite-depth physical and full-GI kernels agree; **otherwise** one has the nonzero genuine physical Schur source. OR proves the original GL square/contrast mass is strictly positive for EVERY physically nonzero source in the collapse branch, and the corresponding unconditional disjunction. OW NOW excludes any physically nonzero true finite Krylov source invisible at ALL genuine original GI contexts. OX NOW proves strict original GL mass for every nonzero physical finite Krylov source at arbitrary nonnegative fine coupling. Neither result proves `S₂(R₂)≠0`, coefficient-source injectivity at depth two or a volume-/depth-/fine-uniform floor. OS supplies norm constants for the genuine depth-one coefficient space and, only on the physically nonzero Schur branch, at depth two; those constants are not an absolute or volume-uniform GL mass floor. OY proves STRICT true one-slab Wilson physical quadratic energy on nonzero finite Krylov sources at positive fine coupling and one-step coefficient kernel conservation. OZ extends physical nonannihilation to arbitrary iteration k. PA/PB/PC identify the shifted rank-2 Hilbert Gram with original Wilson scalar moments and prove strict 2×2 shifted Hankel determinants; even a two-point positive spectrum already satisfies these inequalities, so a third spectral support point and rank3 still require new original-Wilson analysis. These analytic facts still do not decide whether U,T_tU,T_t²U are linearly independent. The next physical analysis must derive from the actual original Wilson kernel either (i) the specific depth-two physical Schur image and its higher fine variation, (ii) a genuinely nonzero third two-posterior receiver response, or (iii) quantitative estimates compatible across H/scale and the same endpoint. Distinguish these independent gates.

Moreover, `M\succ0` for each finite point set does **not** provide a uniform lower bound on `λ_min(M)`, nor `inf_H Q_GI(H)/N_H>0`. OC's interpolation inverse may deteriorate with point geometry and H. These are separate, open quantitative gates.

## 6. Distinct earlier finite-volume results

- The original Wilson Haar-reference `A_W` and normalized physical Dirichlet `D₁₂` have distinct finite-volume Riesz/Loewner/restricted-spectrum results: [#5440](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5440), [#5472](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472), [#5485](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5485).
- [#5514, ES–ET](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5514): the actual color count `L_c(H)=4(H+1)^3` and an H-dependent **relative** operator coefficient obstruction, not an absolute continuum-gap no-go.
- [#5574, GI–GL](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5574): original two-interacting-posterior signed physical response lower certificate with *the genuine `Q_post`* in its denominator. Never substitute `Q_GI` for this different quantity.
- [#5601–#5639, HI–IR](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5639): actual physical signed-source detectors, physical invisible subspace `I_phys=S(ker Φ)` and restricted visible quotient. Full signed-source positivity is conditional on eliminating this invisible sector. The zero-fine/all-depth and zero-depth/all-nonnegative-fine boundary cases are proved [#5621](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5621).
- [#5661–#5665, JO–JS](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665): genuine temporal-Wilson posterior contrast detection, original physical receiver covariance remainder and a conditional receiver-span obstruction. They remain useful **separate** theorems; the once-open *spatial* nonzero-witness gate was subsequently closed by LM rather than by silently assuming receiver-span membership.

## 7. Explicitly OPEN — the actual continuum proof obligations

1. **Uniform authentic signed-source information.** Even though a witness with `Q_GI>0` exists at each finite H, **no** positive uniform lower bound for `Q_GI/N_H` across H/spacing/scales and physically compatible contexts is proved. `E_b` and the coupling schedule also require control.
2. **Full physical source coverage and endpoint transport.** Neither a p-dependent two-source Gram nor its stable inverse proves the required source separation for **arbitrary positive fine coupling and every Krylov depth**. The zero-invisible-sector condition and the transfer of actual local source estimates to the **same genuine endpoint physical source family** are open.
3. **Spatial/scale summability.** Genuine interacting-Wilson receiver covariance and spatial tails must have appropriate localization and summable, volume-compatible constants; no Dobrushin substitute or independent-Haar conditional model may be silently introduced.
4. **H1-C1/C2/C3 strong limit**, including genuine coarse/fine compatibility and a single natural-time physical operator; physical-time semigroup, OS/Wightman reconstruction and full nontrivial continuum **4D Yang–Mills mass gap** are subsequent, separate open gates.

No single fixed-volume rank/Gram witness, positive finite-lattice spectral band, or `sorry`-free theorem resolves those continuum obligations. See the precise **[ROADMAP](ROADMAP.md)**.

## 8. Reproducing source and auditing proof integrity

Work from the **verified theorem-bearing OZ checkpoint**, not default `main` or a docs-only SHA:

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch --detach feac7e92d3e56f5301d1f8ecbc66dceb4d74c011
cat lean-toolchain
# Optional when a compatible pinned cache is available:
lake exe cache get
# Historical dependency-aware build example (PZ37PC checkpoint, not the latest leaf):
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllIteratedFineKrylovNonzeroV5_OZ
# Full repository build is a separate, more expensive check:
# lake build
```

The OZ module has four public `#print axioms` reports in exact-head scoped CI #39857992320 (10886/10886 dependency-reachable Lean targets, sorryAx absent, changed warnings/errors 0/0, independent MCP receipt SUCCESS; three reports rely only on the standard three Lean axioms and the fourth also inherits existing finite-lattice native_decide). The OY module has six public `#print axioms` reports at exact source HEAD in CI #39856189021 (Lean 10886/10886 SUCCESS, all six with only standard three Lean axioms, no sorryAx, changed warnings/errors 0/0, MCP receipt SUCCESS). The OX module has two public `#print axioms` reports in exact-head CI #39854681185 (Lean 10885/10885, no sorryAx, no changed warnings/errors, MCP receipt SUCCESS; both inherit only the original finite-lattice native_decide and the three standard Lean axioms). The OS module has four public `#print axioms` reports at exact source HEAD in CI #39774820731: Lean 10880/10880 SUCCESS, `sorryAx` absent, changed warnings/errors 0/0 and MCP receipt SUCCESS; two depend only on the standard three Lean axioms and two inherit the existing finite-lattice `native_decide` axioms. The OR module has seven public `#print axioms` reports at exact source HEAD in CI #39769721363: Lean 10879/10879 SUCCESS, `sorryAx` absent, changed warnings/errors 0/0, MCP receipt SUCCESS; two depend on standard `propext`, `Classical.choice`, `Quot.sound` only and five inherit existing finite-lattice `native_decide` axioms. OQ #39767540710 similarly has 7/7, 10878/10878 SUCCESS (6 standard-only, 1 inherited native_decide). No new unproved axiom, and docs-only SHA changes do not establish new mathematics.

For a future theorem: inspect current canonical SHA, the **complete Lean file and its physical prerequisites**, the exact changed-source-head CI and public axioms; fix errors/warnings in changed files, verify the independent MCP CI completion receipt, then merge and re-observe the new canonical SHA. The PR Lean Fast Check workflow is path-filtered to Lean sources, configuration, and scripts; a README/ROADMAP-only PR does **not** trigger the Lean workflow. Review Markdown and source links directly instead of rebuilding thousands of unchanged theorem modules.


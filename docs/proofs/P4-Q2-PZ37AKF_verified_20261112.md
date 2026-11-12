# P4-Q2-PZ37AKF — 抽象二成分列によるAJA証人推論の障害

2026年11月12日 JST。固定Lean4形式検証の説明記録。この文書自体はLeanカーネルによる証明ではない。AKFの対象は抽象的な実数列であり、真正SU(2) Wilson模型の不存在定理とは区別する。

## 1. Canonical source and mechanical receipts

- Repository: `itakura-hidetoshi/4d-mass-gap`; theorem canonical branch: `formal/real-hilbert-uniform-coercive-strong-limit`. `main`は別の文書公開ミラー。
- [定理PR #6672](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6672) MERGED。初回修正後source `dd1509bf3f25ea4db87b4eca817ebb0f79ce2da5`、[CI #43119494287](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43119494287) completed/SUCCESS。
- AKG・AKH・AKIの統合済みformalへ同期した最終source HEAD `09b3f601682889eda8dacd83007e92f7e2cfbf71`。[Exact-source CI #43152268848](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43152268848)はworkflow、changed-Lean job、Lean step、後続キャッシュ処理、独立completion receiptまでcompleted/SUCCESS。
- 正式formal squash HEAD `2b8b15f8317d8e2b449b5c047a2f9b0e447a5175`。[独立formal push CI #43152945449](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43152945449)はevent=push、exact squash HEADでworkflow/job/Lean step/receiptすべてcompleted/SUCCESS。Lean job `130966189008`、receipt job `130968345437`。
- 両最終CIのLean依存閉包は**11,445/11,445**。新規9宣言（定義1、定理8）の公理監査9/9は`propext`、`Classical.choice`、`Quot.sound`のみ。変更AKF warning/error 0/0、新規`sorryAx`なし、禁止トークン監査は`sorry/admit/axiom/constant`各0。
- 独立status `chatgpt-ci-receipt/PR Lean Fast Check`：source receipt `58696936470`、formal push receipt `58697284512`、ともにSUCCESS。receiptは完了通知であり、Lean実ログの代用にはしていない。
- PR jobが実際にcheckoutしたのはtest-mergeであり、sourceそのもののcheckoutを主張していない。以下のGit tree一致によりsource内容との一致を確認した。
- Source、実際のPR test-merge `2acaff1663bb359f113f66edc89d3db79b1dde24`、正式squashのGit treeはすべて`803f6b61d4e85e8bf9cb883d28793d2df2823aed`。
- 新規leaf：[RealHilbertAJAAbstractTwoSectorPowerBudgetCountermodelV5_PZ37AKF.lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2b8b15f8317d8e2b449b5c047a2f9b0e447a5175/MGAP4D/MathlibAnalytic/RealHilbertAJAAbstractTwoSectorPowerBudgetCountermodelV5_PZ37AKF.lean)、162行追加、既存Lean変更・削除0。leaf blob `805325364331f5c2bc669b689dd0ed8c94b7510f`は同期前後で不変。
- Direct imports: original AKE leaf and `Mathlib.Tactic`。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`を維持。
- 本記録の起点として再観測した最新formal HEADは、後続AKJを含む`2403229c6db3ba3e7702cc014a875fa9f91493d6`。AKFの認証squashと、現在の正本HEADを混同しない。

## 2. Kernel-checked abstract sequence

AKFで定義された実数列と予算は

```text
a_n = 1/4 + (3/4)*(1/4)^n,   V = a_0 = 1,   B = 1/32.
```

認証された内容は次のとおり。

1. `a_0=1`、`a_1=7/16`。
2. 全自然数nで隣接log-convex性 `a_(n+1)^2 ≤ a_n*a_(n+2)`。
3. 全自然数nで厳密減衰 `a_(n+1)<a_n`。
4. `0<B`、`B≤a_1`、`B≤V/16`の同時成立。
5. AKCの一般log-convex補題を用いた全正整数冪下界 `B^(n+1)≤V^n*a_(n+1)`。
6. `¬∃n:ℕ, 0<n ∧ a_n<B`。
7. `a_n→1/4`。

定義から各nで`a_n≥1/4>1/32=B`となり、正値性も得られる。減衰成分が消えても固定成分が予算より大きいため、厳密予算証人は生じない。

**形式化の範囲:** このleafが直接定義・検証するのは実数列と上の命題である。二成分スペクトルという表現はこの列の解釈であり、このleafに新しいHilbert空間や二次元作用素の構成を追加したとは主張しない。真正Wilsonの`S,f0,Q,B`へこの抽象列を同一視する写像も構成していない。

## 3. New declarations audited 9/9

すべてnamespace `MGAP4D.MathlibAnalytic`。

1. `p4Q2PZ37AKF_twoSectorEnergy` — definition.
2. `p4Q2PZ37AKF_twoSectorEnergy_zero`.
3. `p4Q2PZ37AKF_twoSectorEnergy_one`.
4. `p4Q2PZ37AKF_twoSectorEnergy_logConvex`.
5. `p4Q2PZ37AKF_twoSectorEnergy_strict_drop`.
6. `p4Q2PZ37AKF_twoSectorHaarLikeBudget`.
7. `p4Q2PZ37AKF_twoSectorAllPositivePowerFloor`.
8. `p4Q2PZ37AKF_twoSector_no_strict_HaarLike_witness`.
9. `p4Q2PZ37AKF_twoSector_tendsto_fullTop`.

## 4. Genuine Wilson context at the observed canonical HEAD

以下はAKFの結論ではなく、別の真正Wilson定理の現行状況である。AKF source header中の旧OPEN記述は、その作成時点の記録として保持し、この追記で後続の証拠を明示する。

- [AKG #6673](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6673)、[AKH #6674](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6674)、[AKI #6675](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6675)はMERGED。AKIの真正モデル結果は全有限Hについて、`0<beta≤kappa_H=log(2)/(2*p_H)`なら元AJA厳密有限冪証人が存在しない、というもの。
- さらに[AKJ #6676](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6676)もMERGED。元ABN temporal character coefficient `r(beta)`を保持した
  `C_H(beta)=2*exp(-2*beta*p_H)+exp(-beta*p_H)*r(beta)^4`
  に対し、`beta>0`かつ`1≤C_H(beta)`なら、**全自然数冪**に元AJA厳密証人が存在しない。
- AKJは`C_H(kappa_H)>1`と係数の連続性も証明し、`beta>kappa_H`でなお元証人が存在しない結合の存在を形式化した。したがって「`beta>kappa_H`の全領域が未判定」という旧記述は現行正本には適用しない。
- AKJ exact-source [CI #43153265889](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43153265889)と独立formal push [CI #43154080548](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43154080548)はcompleted/SUCCESS。これはAKFの11,445件の認証とは別の検証である。
- 上の不存在判定の対偶として、真正AJA証人が存在するためには`C_H(beta)<1`が必要になる。この必要条件を十分条件として扱わない。AKJは全`beta>kappa_H`での不存在を証明してはいない。

## 5. Next original-model comparison and retained OPEN items

次の存在探索では、少なくとも`beta>kappa_H`かつ`C_H(beta)<1`を満たす対象について、真正full-top射影と**元の**AJA Haar予算を直接比較する。

```text
Delta_(H,beta) = B_(H,beta) - ||Q_(H,beta) f_(0,H)||^2.
```

AJI/AKEが認証した同値によれば、`Delta>0`なら真正の有限冪証人が存在し、あるN≥2以後すべての冪で予算を厳密に下回る。`Delta≤0`ならその厳密証人は存在しない。必要条件`C_H(beta)<1`だけからDeltaの符号を確定しない。

**具体的な次対象（既存定義からの算術的導出、新規Lean宣言としては未認証）:** 元の固定結合`beta0=log(3/2)/64`、`H=1`を候補にする。[ADCの固定結合](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2403229c6db3ba3e7702cc014a875fa9f91493d6/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingCertificateV5_PZ37ADC.lean)、[AIBの`p_1=192`](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2403229c6db3ba3e7702cc014a875fa9f91493d6/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuarticBudgetObstructionV5_PZ37AIB.lean)、[ABNの`0<r(beta0)≤1`](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2403229c6db3ba3e7702cc014a875fa9f91493d6/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTemporalCharacterTransmissionV5_PZ37ABN.lean)から、`q=exp(-beta0*p_1)=8/27`、`C_1(beta0)≤2*(8/27)^2+8/27=344/729<1`を得る。また`exp(2*beta0*p_1)=(3/2)^6=729/64>2`より`kappa_1<beta0`。これらは既知のAKI/AKJ不存在判定の外にある候補を選ぶための計算であり、`Delta_(1,beta0)`の符号は依然NO_DATAである。

未解決なのは、既知の不存在範囲外でのこの真正数値比較と証人の存在・不存在、top一次元性、H一様coercivity、Hamiltonian spectral gap、4D continuum Yang–Mills mass gapである。全H・全beta>0での一律の元AJA証人存在という旧目標は、真正モデルの既知の不存在範囲によって否定されており、現在の存在探索目標として復活させない。

Append-only / tighten-only / overwrite-forbidden / same-root。元Wilson/Haar/ZW/AJA定義、仮定、旧定理、root、Lean/mathlib pinは不変更。本記録とREADME/ROADMAP追記だけをmainへミラーし、formal専用Lean leafはコピーしない。docs-only変更に対するStrict Leanの手動実行は行わない。

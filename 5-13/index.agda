{-# OPTIONS --without-K --safe #-}

-- 3.2. 宇宙
-- 色々な流儀があるが、ここでは可算無限個（実質的には任意有限個）の宇宙によって階層づけを行える型理論について考える
-- つまり Type0 : Type1, Type1 : Type2,... となっているとする
-- Coq では宇宙のレベルは Coq 側が勝手に付けてくれる（矛盾なく付けられない場合はエラーを返す）
-- Agda ではユーザーが宇宙のレベルを書く必要がある（単に Set と書くと、一番下の宇宙を指していることになる）
-- 宇宙に関する面白い話題はいくつかあるが、ここでは触れない

-- ちなみに、宇宙に関して U : U を認めると矛盾する
-- 矛盾を導く議論は色々あるが、初期のものとしては Girard's paradox がある（後に Hurkens によって簡略化された）
  -- Girard's paradox は System U のような inductive type の構成に関する規則がない体系でも機能する
  -- 内容は集合論における Burali-Forti paradox と似ている
  -- 集合論における Russell's paradox よりは少し複雑
    -- Russell's paradox に似た議論を型理論で直接行うことは難しい（理由を考えると面白いかも）
    -- inductive type を認めれば、間接的に Russell's paradox に似た議論を行える


-- 3.3. 関数型

-- ℓ で universe のレベルを表す

-- 恒等関数
id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x
-- 正規形は λ x → x

-- 合成
_∘_ : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)
-- 正規形は λ g f x → g (f x)

-- id は関数型上の0項演算、_∘_ は関数型上の2項演算だと思うこともできる
-- これらの演算に関する性質をいくつか示す

-- identity type
data Id {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : {x : A} → Id x x

id-lunit : ∀ {ℓ} {A B : Set ℓ} {f : A → B} → Id f (f ∘ id)
id-lunit = refl
-- f ∘ id の正規形は λ x → f x で、f を η 展開するとこれに一致する

id-runit : ∀ {ℓ} {A B : Set ℓ} {f : A → B} → Id f (id ∘ f)
id-runit = refl

∘-assoc : ∀ {ℓ} {A B C D : Set ℓ} {f : A → B} {g : B → C} {h : C → D} → Id ((h ∘ g) ∘ f) (h ∘ (g ∘ f))
∘-assoc = refl
-- (h ∘ g) ∘ f, h ∘ (g ∘ f) の正規形はどちらも λ x → h (g (f x))


-- 4.1. inductive type

-- empty type
data ⊥ : Set where

-- 否定
¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

-- 自然数の型
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- Agda のパターンマッチは強いので、以下のようなこともパターンマッチで示せる
-- 普通に除去則を使っても示せるが、少し工夫が要る
  -- HoTT book 2.13 にある encode-decode method が一つのやり方

suc-inj : {m n : ℕ} → Id (suc m) (suc n) → Id m n
suc-inj refl = refl

suc-ne-zero : {n : ℕ} → ¬ (Id (suc n) zero)
suc-ne-zero ()
-- Id (suc n) zero の項に関するパターンマッチ
-- パターンが無いので、空のパターンマッチを行っている

-- 前者関数
pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

pred-suc : Id id (pred ∘ suc)
pred-suc = refl


-- 4.2. fibration (type family), total space

data Σ {ℓ} (B : Set ℓ) (E : B → Set ℓ) : Set ℓ where
  _,_ : (x : B) → E x → Σ B E
open Σ
-- 引数 B は implicit にしても良いが、ここでは明示することにする。

syntax Σ B (λ x → E-x) = Σ x ꞉ B , E-x
-- 大して変わらないが、informal な型理論において使われる記法に近い記法を導入した

-- Π-type に関する記法も導入しておく
Π : ∀ {ℓ} (A : Set ℓ) (B : A → Set ℓ) → Set ℓ
Π A B = (x : A) → B x

syntax Π B (λ x → E-x) = Π x ꞉ B , E-x

-- Σ-type を使った product type の定義
prod : ∀ {ℓ} (A B : Set ℓ) → Set ℓ
prod A B = Σ x ꞉ A , B

-- 直接的な product type の定義
data _×_ {ℓ} (A B : Set ℓ) : Set ℓ where
  _,_ : A → B → A × B

-- Σ-type に関わる関数
pr1 : ∀ {ℓ} {B : Set ℓ} {E : B → Set ℓ} → (Σ x ꞉ B , E x) → B
pr1 (x , y) = x

pr2 : ∀ {ℓ} {B : Set ℓ} {E : B → Set ℓ} → (p : Σ x ꞉ B , E x) → E (pr1 p)
pr2 (x , y) = y

-- （直観主義）述語論理

∀¬2¬∃ : ∀ {ℓ} {A : Set ℓ} {P : A → Set ℓ} → (Π x ꞉ A , ¬ (P x)) → ¬ (Σ x ꞉ A , P x)
∀¬2¬∃ anp (x , y) = anp x y
-- anp : (Π x ꞉ A , ¬ (P x)) と (x , y) : (Σ x ꞉ A , P x) から矛盾を導いている

¬∃2∀¬ : ∀ {ℓ} {A : Set ℓ} {P : A → Set ℓ} → ¬ (Σ x ꞉ A , P x) → (Π x ꞉ A , ¬ (P x))
¬∃2∀¬ nep x px = nep (x , px)
-- nep : ¬ (Σ x ꞉ A , P x) と x ꞉ A と px : P x から矛盾を導いている

∃¬2¬∀ : ∀ {ℓ} {A : Set ℓ} {P : A → Set ℓ} → (Σ x ꞉ A , ¬ (P x)) → ¬ (Π x ꞉ A , P x)
∃¬2¬∀ (x , npx) ap = npx (ap x)
-- (x , npx) : (Σ x ꞉ A , ¬ (P x)) と ap : (Π x ꞉ A , P x) から矛盾を導いている

-- ¬ (Π x ꞉ A , P x) → (Σ x ꞉ A , ¬ (P x)) は一般には示せない（排中律等を公理として与えれば示せる）


-- 構成的な choice（余談）

-- 一階述語論理上のZFC集合論において、選択公理 (AC) は公理として仮定されている
-- AC を仮定すると、一階述語論理で直観主義的なものを採用したとしても排中律 (LEM) と同等のことが言える (Diaconescu's theorem)
  -- 命題 P を持ってくると、P ∨ ¬ P が示せるということ
  -- 可算選択公理 (CC) や従属選択公理 (DC) から LEM と同等のことを言うことはできない
    -- 構成主義であっても、流儀によっては CC, DC を仮定する場合がある

-- 型理論の（計算の観点から見て）良い性質を保つためには、公理なしで（良い規則のみで）議論を行うべき
  -- 当然 LEM, AC を仮定すると良い性質 (canonicity) が壊れる
-- しかし、次の主張は規則のみから示すことができる

choice : ∀ {ℓ} {Λ : Set ℓ} {A : Λ → Set ℓ} {P : (x : Λ) → A x → Set ℓ} →
  (Π x ꞉ Λ , Σ a ꞉ A x , P x a) → (Σ f ꞉ ((x : Λ) → A x) , Π x ꞉ Λ , P x (f x))
choice axeapxa = (λ x → pr1 (axeapxa x)) , (λ x → pr2 (axeapxa x))
-- Λ で添え字づけられた集合族 {A_x}_{x∈Λ} があるとき、
-- 任意の x∈Λ に対して「命題 P x a が成り立つような a∈A_λ が "存在する"」なら、
-- 「任意の x∈Λ に対して命題 P x (f x) が成り立つ」ような、選択関数 f ꞉ ((x : Λ) → A x) が "存在する"

-- Π, Σ が ∀, ∃ と対応していると思うなら、これは AC と同値な主張に対応する
  -- 厳密に言えば、関数型の項と写像も対応させている
  -- 集合論において写像はグラフ（ある種の集合）としてエンコードされているので、実はこれは少し非自明な対応のさせ方
-- しかし、この choice は規則のみから導けて、この choice から LEM が導かれることはない

-- 対応が崩れているように思われる原因は「Σ が ∃ と対応している」と思う部分にある
-- Σ は集合論における ∃ よりも強い意味を持っている
  -- 感覚的には、∃ が「性質 P を満たす対象が存在する」という情報しか持っていないのに対し、
  -- Σ は「…という対象が、性質 P を満たす」という情報を持っている

-- 型理論において ∃ に対応すると思えるものはあるのだろうか
  -- MLTT には無い（無理やりエンコードできるかもしれないけれど）
  -- pCIC（Coq, Lean のベース）にはある
    -- Prop という宇宙において Σ と同様に inductive に定まる命題が ∃ と対応すると思える
  -- HoTT, cubical type theory (CTT) にはある
    -- Σ の propositional truncation（higher inductive type の一種）が ∃ と対応すると思える
  -- pCIC の ∃ と HoTT の ∃ には微妙な違いがある
    -- pCIC の ∃ は ∃ に加えて一意性が言えたとしても、一般にそこから Σ を導くことはできない
    -- HoTT の ∃ ではできる
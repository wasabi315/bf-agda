{-# OPTIONS --cubical --guardedness #-}

module Brainfuck.Optimization where

open import Cubical.Foundations.Everything hiding ( empty )
open import Cubical.Data.Bool.Base using ( True; toWitness )
open import Cubical.Data.Int as ℤ using ( ℤ; pos; negsuc )
open import Cubical.Data.NatPlusOne.Base using ( ℕ₊₁; one; 1+_; 2+_; _+₁_ )
open import Cubical.Data.NatPlusOne.Properties as ℕ using ( +₁-assoc )
open import Cubical.Data.List.Base using ( List; []; _∷_; _++_ )
open import Cubical.Data.List.Properties using ( ++-assoc )
open import Cubical.Relation.Nullary using ( Dec )

open import Brainfuck.Syntax as Cmds hiding ( NoLoops; noLoops? )
open import Brainfuck.State
import Brainfuck.SmallStep as Cmds
open import Data.InfZipper

private
  variable
    ℓ : Level
    A B : Type ℓ

--------------------------------------------------------------------------------
-- Misc.

pure : A → List A
pure x = x ∷ []

replicate : ℕ₊₁ → A → List A
replicate one x = x ∷ []
replicate (2+ n) x = x ∷ replicate (1+ n) x

merge-replicate : ∀ m n {x : A}
  → replicate m x ++ replicate n x ≡ replicate (m +₁ n) x
merge-replicate one n = refl
merge-replicate (2+ m) n = cong (_ ∷_) (merge-replicate (1+ m) n)

infix 1 begin⟨_⟩_
begin⟨_⟩_ : I → ∀ {x y} → Path A x y → A
begin⟨ i ⟩ p = p i

--------------------------------------------------------------------------------

mutual

  data Opt : Type where
    `>⟨_⟩ `<⟨_⟩ `+⟨_⟩ `-⟨_⟩ : (n : ℕ₊₁) → Opt
    `· `, : Opt
    `[_] : Opts → Opt

  data Opts : Type where
    [] : Opts
    _∷_ : (c : Opt) (cs : Opts) → Opts
    merge-addPtr : ∀ m n cs → `>⟨ m ⟩ ∷ `>⟨ n ⟩ ∷ cs ≡ `>⟨ m +₁ n ⟩ ∷ cs
    merge-subPtr : ∀ m n cs → `<⟨ m ⟩ ∷ `<⟨ n ⟩ ∷ cs ≡ `<⟨ m +₁ n ⟩ ∷ cs
    merge-addVal : ∀ m n cs → `+⟨ m ⟩ ∷ `+⟨ n ⟩ ∷ cs ≡ `+⟨ m +₁ n ⟩ ∷ cs
    merge-subVal : ∀ m n cs → `-⟨ m ⟩ ∷ `-⟨ n ⟩ ∷ cs ≡ `-⟨ m +₁ n ⟩ ∷ cs
    trunc : isSet Opts

pattern □ = []
pattern >⟨_⟩_ n cs = `>⟨ n ⟩ ∷ cs
pattern <⟨_⟩_ n cs = `<⟨ n ⟩ ∷ cs
pattern +⟨_⟩_ n cs = `+⟨ n ⟩ ∷ cs
pattern -⟨_⟩_ n cs = `-⟨ n ⟩ ∷ cs
pattern ·_ cs = `· ∷ cs
pattern ,_ cs = `, ∷ cs
pattern [_]_ cs cs₁ = `[ cs ] ∷ cs₁

infixr 5 _+++_
_+++_ : Opts → Opts → Opts
□ +++ cs₁ = cs₁
(c ∷ cs) +++ cs₁ = c ∷ cs +++ cs₁
merge-addPtr m n cs i +++ cs₁ = merge-addPtr m n (cs +++ cs₁) i
merge-subPtr m n cs i +++ cs₁ = merge-subPtr m n (cs +++ cs₁) i
merge-addVal m n cs i +++ cs₁ = merge-addVal m n (cs +++ cs₁) i
merge-subVal m n cs i +++ cs₁ = merge-subVal m n (cs +++ cs₁) i
trunc cs cs₁ p q i j +++ cs₂ =
  trunc (cs +++ cs₂) (cs₁ +++ cs₂) (cong (_+++ cs₂) p) (cong (_+++ cs₂) q) i j

--------------------------------------------------------------------------------

module Elim {P : Opts → Type ℓ}
  (□* : P □)
  (>⟨_⟩*_ : ∀ n {cs} (cs* : P cs) → P (>⟨ n ⟩ cs))
  (<⟨_⟩*_ : ∀ n {cs} (cs* : P cs) → P (<⟨ n ⟩ cs))
  (+⟨_⟩*_ : ∀ n {cs} (cs* : P cs) → P (+⟨ n ⟩ cs))
  (-⟨_⟩*_ : ∀ n {cs} (cs* : P cs) → P (-⟨ n ⟩ cs))
  (·*_ : ∀ {cs} (cs* : P cs) → P (· cs))
  (,*_ : ∀ {cs} (cs* : P cs) → P (, cs))
  ([_]*_ : ∀ {cs} (cs* : P cs) {cs₁} (cs₁* : P cs₁) → P ([ cs ] cs₁))
  (merge-addPtr* : ∀ m n {cs} (cs* : P cs)
    → PathP (λ i → P (merge-addPtr m n cs i)) (>⟨ m ⟩* >⟨ n ⟩* cs*) (>⟨ m +₁ n ⟩* cs*))
  (merge-subPtr* : ∀ m n {cs} (cs* : P cs)
    → PathP (λ i → P (merge-subPtr m n cs i)) (<⟨ m ⟩* <⟨ n ⟩* cs*) (<⟨ m +₁ n ⟩* cs*))
  (merge-addVal* : ∀ m n {cs} (cs* : P cs)
    → PathP (λ i → P (merge-addVal m n cs i)) (+⟨ m ⟩* +⟨ n ⟩* cs*) (+⟨ m +₁ n ⟩* cs*))
  (merge-subVal* : ∀ m n {cs} (cs* : P cs)
    → PathP (λ i → P (merge-subVal m n cs i)) (-⟨ m ⟩* -⟨ n ⟩* cs*) (-⟨ m +₁ n ⟩* cs*))
  (trunc* : ∀ cs → isSet (P cs))
  where

  f : (cs : Opts) → P cs
  f □ = □*
  f (>⟨ n ⟩ cs) = >⟨ n ⟩* f cs
  f (<⟨ n ⟩ cs) = <⟨ n ⟩* f cs
  f (+⟨ n ⟩ cs) = +⟨ n ⟩* f cs
  f (-⟨ n ⟩ cs) = -⟨ n ⟩* f cs
  f (· cs) = ·* f cs
  f (, cs) = ,* f cs
  f ([ cs ] cs₁) = [ f cs ]* f cs₁
  f (merge-addPtr m n cs i) = merge-addPtr* m n (f cs) i
  f (merge-subPtr m n cs i) = merge-subPtr* m n (f cs) i
  f (merge-addVal m n cs i) = merge-addVal* m n (f cs) i
  f (merge-subVal m n cs i) = merge-subVal* m n (f cs) i
  f (trunc cs cs₁ p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*
    (f cs)
    (f cs₁)
    (cong f p)
    (cong f q)
    (trunc cs cs₁ p q)
    i j

module ElimProp {P : Opts → Type ℓ} (PProp : ∀ {cs} → isProp (P cs))
  (□* : P □)
  (>⟨_⟩*_ : ∀ n {cs} (cs* : P cs) → P (>⟨ n ⟩ cs))
  (<⟨_⟩*_ : ∀ n {cs} (cs* : P cs) → P (<⟨ n ⟩ cs))
  (+⟨_⟩*_ : ∀ n {cs} (cs* : P cs) → P (+⟨ n ⟩ cs))
  (-⟨_⟩*_ : ∀ n {cs} (cs* : P cs) → P (-⟨ n ⟩ cs))
  (·*_ : ∀ {cs} (cs* : P cs) → P (· cs))
  (,*_ : ∀ {cs} (cs* : P cs) → P (, cs))
  ([_]*_ : ∀ {cs} (cs* : P cs) {cs₁} (cs₁* : P cs₁) → P ([ cs ] cs₁))
  where

  f : (cs : Opts) → P cs
  f = Elim.f □* >⟨_⟩*_ <⟨_⟩*_ +⟨_⟩*_ -⟨_⟩*_ ·*_ ,*_ [_]*_
    (λ m n {cs} cs* → toPathP
      (PProp
        (transport (λ i → P (merge-addPtr m n cs i)) (>⟨ m ⟩* >⟨ n ⟩* cs*))
        (>⟨ m +₁ n ⟩* cs*)))
    (λ m n {cs} cs* → toPathP
      (PProp
        (transport (λ i → P (merge-subPtr m n cs i)) (<⟨ m ⟩* <⟨ n ⟩* cs*))
        (<⟨ m +₁ n ⟩* cs*)))
    (λ m n {cs} cs* → toPathP
      (PProp
        (transport (λ i → P (merge-addVal m n cs i)) (+⟨ m ⟩* +⟨ n ⟩* cs*))
        (+⟨ m +₁ n ⟩* cs*)))
    (λ m n {cs} cs* → toPathP
      (PProp
        (transport (λ i → P (merge-subVal m n cs i)) (-⟨ m ⟩* -⟨ n ⟩* cs*))
        (-⟨ m +₁ n ⟩* cs*)))
    (λ _ → isProp→isSet PProp)

module Rec (AType : isSet A)
  (□* : A)
  (>⟨_⟩*_ <⟨_⟩*_ +⟨_⟩*_ -⟨_⟩*_ : ℕ₊₁ → A → A)
  (·*_ ,*_ : A → A)
  ([_]*_ : A → A → A)
  (merge-addPtr* : ∀ m n cs*
    → >⟨ m ⟩* >⟨ n ⟩* cs* ≡ >⟨ m +₁ n ⟩* cs*)
  (merge-subPtr* : ∀ m n cs*
    → <⟨ m ⟩* <⟨ n ⟩* cs* ≡ <⟨ m +₁ n ⟩* cs*)
  (merge-addVal* : ∀ m n cs*
    → +⟨ m ⟩* +⟨ n ⟩* cs* ≡ +⟨ m +₁ n ⟩* cs*)
  (merge-subVal* : ∀ m n cs*
    → -⟨ m ⟩* -⟨ n ⟩* cs* ≡ -⟨ m +₁ n ⟩* cs*)
  where

  f : Opts → A
  f = Elim.f
    □*
    (λ n cs* → >⟨ n ⟩* cs*)
    (λ n cs* → <⟨ n ⟩* cs*)
    (λ n cs* → +⟨ n ⟩* cs*)
    (λ n cs* → -⟨ n ⟩* cs*)
    (λ cs* → ·* cs*)
    (λ cs* → ,* cs*)
    (λ cs* cs₁* → [ cs* ]* cs₁*)
    (λ m n cs* → merge-addPtr* m n cs*)
    (λ m n cs* → merge-subPtr* m n cs*)
    (λ m n cs* → merge-addVal* m n cs*)
    (λ m n cs* → merge-subVal* m n cs*)
    (const AType)

--------------------------------------------------------------------------------

Cmds→Opts : Cmds → Opts
Cmds→Opts □ = □
Cmds→Opts (> cs) = >⟨ one ⟩ Cmds→Opts cs
Cmds→Opts (< cs) = <⟨ one ⟩ Cmds→Opts cs
Cmds→Opts (+ cs) = +⟨ one ⟩ Cmds→Opts cs
Cmds→Opts (- cs) = -⟨ one ⟩ Cmds→Opts cs
Cmds→Opts (· cs) = · Cmds→Opts cs
Cmds→Opts (, cs) = , Cmds→Opts cs
Cmds→Opts ([ cs ] cs₁) = [ Cmds→Opts cs ] Cmds→Opts cs₁

Opts→Cmds : Opts → Cmds
Opts→Cmds = Rec.f isSetCmds
  □
  (λ n → replicate n `> ++_)
  (λ n → replicate n `< ++_)
  (λ n → replicate n `+ ++_)
  (λ n → replicate n `- ++_)
  ·_
  ,_
  [_]_
  (λ m n cs →
      replicate m `> ++ replicate n `> ++ cs
    ≡⟨ sym (++-assoc (replicate m `>) (replicate n `>) cs) ⟩
      (replicate m `> ++ replicate n `>) ++ cs
    ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
      replicate (m +₁ n) `> ++ cs
    ∎)
  (λ m n cs →
      replicate m `< ++ replicate n `< ++ cs
    ≡⟨ sym (++-assoc (replicate m `<) (replicate n `<) cs) ⟩
      (replicate m `< ++ replicate n `<) ++ cs
    ≡⟨ cong (_++ cs) (merge-replicate m n) ⟩
      replicate (m +₁ n) `< ++ cs
    ∎)
  (λ m n cs →
      replicate m `+ ++ replicate n `+ ++ cs
    ≡⟨ sym (++-assoc (replicate m `+) (replicate n `+) cs) ⟩
      (replicate m `+ ++ replicate n `+) ++ cs
    ≡⟨ cong (_++ cs) (merge-replicate m n) ⟩
      replicate (m +₁ n) `+ ++ cs
    ∎)
  (λ m n cs →
      replicate m `- ++ replicate n `- ++ cs
    ≡⟨ sym (++-assoc (replicate m `-) (replicate n `-) cs) ⟩
      (replicate m `- ++ replicate n `-) ++ cs
    ≡⟨ cong (_++ cs) (merge-replicate m n) ⟩
      replicate (m +₁ n) `- ++ cs
    ∎)

Cmds→Opts-replicate-incPtr : ∀ n → Cmds→Opts (replicate n `>) ≡ >⟨ n ⟩ □
Cmds→Opts-replicate-incPtr one = refl
Cmds→Opts-replicate-incPtr (2+ n) =
    >⟨ one ⟩ Cmds→Opts (replicate (1+ n) `>)
  ≡⟨ cong >⟨ one ⟩_ (Cmds→Opts-replicate-incPtr (1+ n)) ⟩
    >⟨ one ⟩ >⟨ 1+ n ⟩ □
  ≡⟨ merge-addPtr one (1+ n) □ ⟩
    >⟨ 2+ n ⟩ □
  ∎

Cmds→Opts-replicate-decPtr : ∀ n → Cmds→Opts (replicate n `<) ≡ <⟨ n ⟩ □
Cmds→Opts-replicate-decPtr one = refl
Cmds→Opts-replicate-decPtr (2+ n) =
    <⟨ one ⟩ Cmds→Opts (replicate (1+ n) `<)
  ≡⟨ cong <⟨ one ⟩_ (Cmds→Opts-replicate-decPtr (1+ n)) ⟩
    <⟨ one ⟩ <⟨ 1+ n ⟩ □
  ≡⟨ merge-subPtr one (1+ n) □ ⟩
    <⟨ 2+ n ⟩ □
  ∎

Cmds→Opts-replicate-incVal : ∀ n → Cmds→Opts (replicate n `+) ≡ +⟨ n ⟩ □
Cmds→Opts-replicate-incVal one = refl
Cmds→Opts-replicate-incVal (2+ n) =
    +⟨ one ⟩ Cmds→Opts (replicate (1+ n) `+)
  ≡⟨ cong +⟨ one ⟩_ (Cmds→Opts-replicate-incVal (1+ n)) ⟩
    +⟨ one ⟩ +⟨ 1+ n ⟩ □
  ≡⟨ merge-addVal one (1+ n) □ ⟩
    +⟨ 2+ n ⟩ □
  ∎

Cmds→Opts-replicate-decVal : ∀ n → Cmds→Opts (replicate n `-) ≡ -⟨ n ⟩ □
Cmds→Opts-replicate-decVal one = refl
Cmds→Opts-replicate-decVal (2+ n) =
    -⟨ one ⟩ Cmds→Opts (replicate (1+ n) `-)
  ≡⟨ cong -⟨ one ⟩_ (Cmds→Opts-replicate-decVal (1+ n)) ⟩
    -⟨ one ⟩ -⟨ 1+ n ⟩ □
  ≡⟨ merge-subVal one (1+ n) □ ⟩
    -⟨ 2+ n ⟩ □
  ∎

Cmds→Opts-++ : ∀ cs cs₁ → Cmds→Opts (cs ++ cs₁) ≡ Cmds→Opts cs +++ Cmds→Opts cs₁
Cmds→Opts-++ □ cs₁ = refl
Cmds→Opts-++ (> cs) cs₁ = cong >⟨ one ⟩_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ (< cs) cs₁ = cong <⟨ one ⟩_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ (+ cs) cs₁ = cong +⟨ one ⟩_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ (- cs) cs₁ = cong -⟨ one ⟩_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ (· cs) cs₁ = cong ·_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ (, cs) cs₁ = cong ,_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ ([ cs ] cs₁) cs₂ = cong [ Cmds→Opts cs ]_ (Cmds→Opts-++ cs₁ cs₂)

sect : section Cmds→Opts Opts→Cmds
sect = ElimProp.f (λ {cs} → trunc (Cmds→Opts (Opts→Cmds cs)) cs)
  refl
  (λ n {cs} p →
      Cmds→Opts (Opts→Cmds (>⟨ n ⟩ cs))
    ≡⟨⟩
      Cmds→Opts (replicate n `> ++ Opts→Cmds cs)
    ≡⟨ Cmds→Opts-++ (replicate n `>) (Opts→Cmds cs) ⟩
      Cmds→Opts (replicate n `>) +++ Cmds→Opts (Opts→Cmds cs)
    ≡⟨ cong (_+++ Cmds→Opts (Opts→Cmds cs)) (Cmds→Opts-replicate-incPtr n) ⟩
      >⟨ n ⟩ Cmds→Opts (Opts→Cmds cs)
    ≡⟨ cong >⟨ n ⟩_ p ⟩
      >⟨ n ⟩ cs
    ∎)
  (λ n {cs} p →
      Cmds→Opts (Opts→Cmds (<⟨ n ⟩ cs))
    ≡⟨⟩
      Cmds→Opts (replicate n `< ++ Opts→Cmds cs)
    ≡⟨ Cmds→Opts-++ (replicate n `<) (Opts→Cmds cs) ⟩
      Cmds→Opts (replicate n `<) +++ Cmds→Opts (Opts→Cmds cs)
    ≡⟨ cong (_+++ Cmds→Opts (Opts→Cmds cs)) (Cmds→Opts-replicate-decPtr n) ⟩
      <⟨ n ⟩ Cmds→Opts (Opts→Cmds cs)
    ≡⟨ cong <⟨ n ⟩_ p ⟩
      <⟨ n ⟩ cs
    ∎)
  (λ n {cs} p →
      Cmds→Opts (Opts→Cmds (+⟨ n ⟩ cs))
    ≡⟨⟩
      Cmds→Opts (replicate n `+ ++ Opts→Cmds cs)
    ≡⟨ Cmds→Opts-++ (replicate n `+) (Opts→Cmds cs) ⟩
      Cmds→Opts (replicate n `+) +++ Cmds→Opts (Opts→Cmds cs)
    ≡⟨ cong (_+++ Cmds→Opts (Opts→Cmds cs)) (Cmds→Opts-replicate-incVal n) ⟩
      +⟨ n ⟩ Cmds→Opts (Opts→Cmds cs)
    ≡⟨ cong +⟨ n ⟩_ p ⟩
      +⟨ n ⟩ cs
    ∎)
  (λ n {cs} p →
      Cmds→Opts (Opts→Cmds (-⟨ n ⟩ cs))
    ≡⟨⟩
      Cmds→Opts (replicate n `- ++ Opts→Cmds cs)
    ≡⟨ Cmds→Opts-++ (replicate n `-) (Opts→Cmds cs) ⟩
      Cmds→Opts (replicate n `-) +++ Cmds→Opts (Opts→Cmds cs)
    ≡⟨ cong (_+++ Cmds→Opts (Opts→Cmds cs)) (Cmds→Opts-replicate-decVal n) ⟩
      -⟨ n ⟩ Cmds→Opts (Opts→Cmds cs)
    ≡⟨ cong -⟨ n ⟩_ p ⟩
      -⟨ n ⟩ cs
    ∎)
  (λ p → cong ·_ p)
  (λ p → cong ,_ p)
  (λ p q → cong₂ [_]_ p q)

retr : retract Cmds→Opts Opts→Cmds
retr □ = refl
retr (> cs) = cong >_ (retr cs)
retr (< cs) = cong <_ (retr cs)
retr (+ cs) = cong +_ (retr cs)
retr (- cs) = cong -_ (retr cs)
retr (· cs) = cong ·_ (retr cs)
retr (, cs) = cong ,_ (retr cs)
retr ([ cs ] cs₁) = cong₂ [_]_ (retr cs) (retr cs₁)

CmdsIsoOpts : Iso Cmds Opts
CmdsIsoOpts = iso Cmds→Opts Opts→Cmds sect retr

Cmds≃Opts : Cmds ≃ Opts
Cmds≃Opts = isoToEquiv CmdsIsoOpts

Cmds≡Opts : Cmds ≡ Opts
Cmds≡Opts = isoToPath CmdsIsoOpts

--------------------------------------------------------------------------------
-- Optimization

mutual

  optimize : Opts → Opts
  optimize □ = □
  optimize (>⟨ n ⟩ cs) = optimize-addPtr n cs
  optimize (<⟨ n ⟩ cs) = optimize-subPtr n cs
  optimize (+⟨ n ⟩ cs) = optimize-addVal n cs
  optimize (-⟨ n ⟩ cs) = optimize-subVal n cs
  optimize (· cs) = · optimize cs
  optimize (, cs) = , optimize cs
  optimize ([ cs ] cs₁) = [ optimize cs ] optimize cs₁
  optimize (merge-addPtr m n cs i) = optimize-addPtr (m +₁ n) cs
  optimize (merge-subPtr m n cs i) = optimize-subPtr (m +₁ n) cs
  optimize (merge-addVal m n cs i) = optimize-addVal (m +₁ n) cs
  optimize (merge-subVal m n cs i) = optimize-subVal (m +₁ n) cs
  optimize (trunc cs cs₁ p q i j) =
    trunc _ _ (cong optimize p) (cong optimize q) i j

  optimize-addPtr : ℕ₊₁ → Opts → Opts
  optimize-addPtr n □ = >⟨ n ⟩ □
  optimize-addPtr n (>⟨ m ⟩ cs) = optimize-addPtr (n +₁ m) cs
  optimize-addPtr n cs@(_ ∷ _) = >⟨ n ⟩ optimize cs
  optimize-addPtr n (merge-addPtr m o cs i) = optimize-addPtr (+₁-assoc n m o (~ i)) cs
  optimize-addPtr n (merge-subPtr m o cs i) = >⟨ n ⟩ optimize-subPtr (m +₁ o) cs
  optimize-addPtr n (merge-addVal m o cs i) = >⟨ n ⟩ optimize-addVal (m +₁ o) cs
  optimize-addPtr n (merge-subVal m o cs i) = >⟨ n ⟩ optimize-subVal (m +₁ o) cs
  optimize-addPtr n (trunc cs cs₁ p q i j) =
    trunc _ _ (cong (optimize-addPtr n) p) (cong (optimize-addPtr n) q) i j

  optimize-subPtr : ℕ₊₁ → Opts → Opts
  optimize-subPtr n □ = <⟨ n ⟩ □
  optimize-subPtr n (<⟨ m ⟩ cs) = optimize-subPtr (n +₁ m) cs
  optimize-subPtr n cs@(_ ∷ _) = <⟨ n ⟩ optimize cs
  optimize-subPtr n (merge-addPtr m o cs i) = <⟨ n ⟩ optimize-addPtr (m +₁ o) cs
  optimize-subPtr n (merge-subPtr m o cs i) = optimize-subPtr (+₁-assoc n m o (~ i)) cs
  optimize-subPtr n (merge-addVal m o cs i) = <⟨ n ⟩ optimize-addVal (m +₁ o) cs
  optimize-subPtr n (merge-subVal m o cs i) = <⟨ n ⟩ optimize-subVal (m +₁ o) cs
  optimize-subPtr n (trunc cs cs₁ p q i j) =
    trunc _ _ (cong (optimize-subPtr n) p) (cong (optimize-subPtr n) q) i j

  optimize-addVal : ℕ₊₁ → Opts → Opts
  optimize-addVal n □ = +⟨ n ⟩ □
  optimize-addVal n (+⟨ m ⟩ cs) = optimize-addVal (n +₁ m) cs
  optimize-addVal n cs@(_ ∷ _) = +⟨ n ⟩ optimize cs
  optimize-addVal n (merge-addPtr m o cs i) = +⟨ n ⟩ optimize-addPtr (m +₁ o) cs
  optimize-addVal n (merge-subPtr m o cs i) = +⟨ n ⟩ optimize-subPtr (m +₁ o) cs
  optimize-addVal n (merge-addVal m o cs i) = optimize-addVal (+₁-assoc n m o (~ i)) cs
  optimize-addVal n (merge-subVal m o cs i) = +⟨ n ⟩ optimize-subVal (m +₁ o) cs
  optimize-addVal n (trunc cs cs₁ p q i j) =
    trunc _ _ (cong (optimize-addVal n) p) (cong (optimize-addVal n) q) i j

  optimize-subVal : ℕ₊₁ → Opts → Opts
  optimize-subVal n □ = -⟨ n ⟩ □
  optimize-subVal n (-⟨ m ⟩ cs) = optimize-subVal (n +₁ m) cs
  optimize-subVal n cs@(_ ∷ _) = -⟨ n ⟩ optimize cs
  optimize-subVal n (merge-addPtr m o cs i) = -⟨ n ⟩ optimize-addPtr (m +₁ o) cs
  optimize-subVal n (merge-subPtr m o cs i) = -⟨ n ⟩ optimize-subPtr (m +₁ o) cs
  optimize-subVal n (merge-addVal m o cs i) = -⟨ n ⟩ optimize-addVal (m +₁ o) cs
  optimize-subVal n (merge-subVal m o cs i) = optimize-subVal (+₁-assoc n m o (~ i)) cs
  optimize-subVal n (trunc cs cs₁ p q i j) =
    trunc _ _ (cong (optimize-subVal n) p) (cong (optimize-subVal n) q) i j

mutual

  optimize≡id : ∀ cs → optimize cs ≡ cs
  optimize≡id □ = refl
  optimize≡id (>⟨ n ⟩ cs) = optimize-addPtr≡>⟨-⟩ n cs
  optimize≡id (<⟨ n ⟩ cs) = optimize-subPtr≡<⟨-⟩ n cs
  optimize≡id (+⟨ n ⟩ cs) = optimize-addVal≡+⟨-⟩ n cs
  optimize≡id (-⟨ n ⟩ cs) = optimize-subVal≡-⟨-⟩ n cs
  optimize≡id (· cs) = cong ·_ (optimize≡id cs)
  optimize≡id (, cs) = cong ,_ (optimize≡id cs)
  optimize≡id ([ cs ] cs₁) = cong₂ [_]_ (optimize≡id cs) (optimize≡id cs₁)
  optimize≡id (merge-addPtr m n cs i) = isSet→isSet' trunc
    (optimize-addPtr≡>⟨-⟩ (m +₁ n) cs ∙ sym (merge-addPtr m n cs))
    (optimize-addPtr≡>⟨-⟩ (m +₁ n) cs)
    (cong optimize (merge-addPtr m n cs))
    (merge-addPtr m n cs)
    i
  optimize≡id (merge-subPtr m n cs i) = isSet→isSet' trunc
    (optimize-subPtr≡<⟨-⟩ (m +₁ n) cs ∙ sym (merge-subPtr m n cs))
    (optimize-subPtr≡<⟨-⟩ (m +₁ n) cs)
    (cong optimize (merge-subPtr m n cs))
    (merge-subPtr m n cs)
    i
  optimize≡id (merge-addVal m n cs i) = isSet→isSet' trunc
    (optimize-addVal≡+⟨-⟩ (m +₁ n) cs ∙ sym (merge-addVal m n cs))
    (optimize-addVal≡+⟨-⟩ (m +₁ n) cs)
    (cong optimize (merge-addVal m n cs))
    (merge-addVal m n cs)
    i
  optimize≡id (merge-subVal m n cs i) = isSet→isSet' trunc
    (optimize-subVal≡-⟨-⟩ (m +₁ n) cs ∙ sym (merge-subVal m n cs))
    (optimize-subVal≡-⟨-⟩ (m +₁ n) cs)
    (cong optimize (merge-subVal m n cs))
    (merge-subVal m n cs)
    i
  optimize≡id (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (cong optimize≡id p)
    (cong optimize≡id q)
    (λ k → optimize≡id cs)
    (λ k → optimize≡id cs₁)
    (λ k l → optimize (trunc cs cs₁ p q k l))
    (trunc cs cs₁ p q)
    i j

  optimize-addPtr≡>⟨-⟩ : ∀ n cs → optimize-addPtr n cs ≡ >⟨ n ⟩ cs
  optimize-addPtr≡>⟨-⟩ n □ = refl
  optimize-addPtr≡>⟨-⟩ n (>⟨ m ⟩ cs) = optimize-addPtr≡>⟨-⟩ (n +₁ m) cs ∙ sym (merge-addPtr n m cs)
  optimize-addPtr≡>⟨-⟩ n (<⟨ m ⟩ cs) = cong >⟨ n ⟩_ (optimize-subPtr≡<⟨-⟩ m cs)
  optimize-addPtr≡>⟨-⟩ n (+⟨ m ⟩ cs) = cong >⟨ n ⟩_ (optimize-addVal≡+⟨-⟩ m cs)
  optimize-addPtr≡>⟨-⟩ n (-⟨ m ⟩ cs) = cong >⟨ n ⟩_ (optimize-subVal≡-⟨-⟩ m cs)
  optimize-addPtr≡>⟨-⟩ n (· cs) = cong (λ cs → >⟨ n ⟩ · cs) (optimize≡id cs)
  optimize-addPtr≡>⟨-⟩ n (, cs) = cong (λ cs → >⟨ n ⟩ , cs) (optimize≡id cs)
  optimize-addPtr≡>⟨-⟩ n ([ cs ] cs₁) = cong₂ (λ cs cs₁ → >⟨ n ⟩ [ cs ] cs₁) (optimize≡id cs) (optimize≡id cs₁)
  optimize-addPtr≡>⟨-⟩ n (merge-addPtr m o cs i) = isSet→isSet' trunc
    ((optimize-addPtr≡>⟨-⟩ ((n +₁ m) +₁ o) cs ∙ sym (merge-addPtr (n +₁ m) o cs)) ∙ sym (merge-addPtr n m (>⟨ o ⟩ cs)))
    (optimize-addPtr≡>⟨-⟩ (n +₁ (m +₁ o)) cs ∙ sym (merge-addPtr n (m +₁ o) cs))
    (cong (optimize-addPtr n) (merge-addPtr m o cs))
    (cong >⟨ n ⟩_ (merge-addPtr m o cs))
    i
  optimize-addPtr≡>⟨-⟩ n (merge-subPtr m o cs i) = isSet→isSet' trunc
    (λ j → >⟨ n ⟩ (optimize-subPtr≡<⟨-⟩ (m +₁ o) cs ∙ sym (merge-subPtr m o cs)) j)
    (cong >⟨ n ⟩_ (optimize-subPtr≡<⟨-⟩ (m +₁ o) cs))
    (cong (optimize-addPtr n) (merge-subPtr m o cs))
    (cong >⟨ n ⟩_ (merge-subPtr m o cs))
    i
  optimize-addPtr≡>⟨-⟩ n (merge-addVal m o cs i) = isSet→isSet' trunc
    (λ j → >⟨ n ⟩ (optimize-addVal≡+⟨-⟩ (m +₁ o) cs ∙ sym (merge-addVal m o cs)) j)
    (cong >⟨ n ⟩_ (optimize-addVal≡+⟨-⟩ (m +₁ o) cs))
    (cong (optimize-addPtr n) (merge-addVal m o cs))
    (cong >⟨ n ⟩_ (merge-addVal m o cs))
    i
  optimize-addPtr≡>⟨-⟩ n (merge-subVal m o cs i) = isSet→isSet' trunc
    (λ j → >⟨ n ⟩ (optimize-subVal≡-⟨-⟩ (m +₁ o) cs ∙ sym (merge-subVal m o cs)) j)
    (cong >⟨ n ⟩_ (optimize-subVal≡-⟨-⟩ (m +₁ o) cs))
    (cong (optimize-addPtr n) (merge-subVal m o cs))
    (cong >⟨ n ⟩_ (merge-subVal m o cs))
    i
  optimize-addPtr≡>⟨-⟩ n (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (cong (optimize-addPtr≡>⟨-⟩ n) p)
    (cong (optimize-addPtr≡>⟨-⟩ n) q)
    (λ k → optimize-addPtr≡>⟨-⟩ n cs)
    (λ k → optimize-addPtr≡>⟨-⟩ n cs₁)
    (λ k l → optimize-addPtr n (trunc cs cs₁ p q k l))
    (λ k l → >⟨ n ⟩ trunc cs cs₁ p q k l)
    i j

  optimize-subPtr≡<⟨-⟩ : ∀ n cs → optimize-subPtr n cs ≡ <⟨ n ⟩ cs
  optimize-subPtr≡<⟨-⟩ n □ = refl
  optimize-subPtr≡<⟨-⟩ n (>⟨ m ⟩ cs) = cong <⟨ n ⟩_ (optimize-addPtr≡>⟨-⟩ m cs)
  optimize-subPtr≡<⟨-⟩ n (<⟨ m ⟩ cs) = optimize-subPtr≡<⟨-⟩ (n +₁ m) cs ∙ sym (merge-subPtr n m cs)
  optimize-subPtr≡<⟨-⟩ n (+⟨ m ⟩ cs) = cong <⟨ n ⟩_ (optimize-addVal≡+⟨-⟩ m cs)
  optimize-subPtr≡<⟨-⟩ n (-⟨ m ⟩ cs) = cong <⟨ n ⟩_ (optimize-subVal≡-⟨-⟩ m cs)
  optimize-subPtr≡<⟨-⟩ n (· cs) = cong (λ cs → <⟨ n ⟩ · cs) (optimize≡id cs)
  optimize-subPtr≡<⟨-⟩ n (, cs) = cong (λ cs → <⟨ n ⟩ , cs) (optimize≡id cs)
  optimize-subPtr≡<⟨-⟩ n ([ cs ] cs₁) = cong₂ (λ cs cs₁ → <⟨ n ⟩ [ cs ] cs₁) (optimize≡id cs) (optimize≡id cs₁)
  optimize-subPtr≡<⟨-⟩ n (merge-addPtr m o cs i) = isSet→isSet' trunc
    (λ j → <⟨ n ⟩ (optimize-addPtr≡>⟨-⟩ (m +₁ o) cs ∙ sym (merge-addPtr m o cs)) j)
    (cong <⟨ n ⟩_ (optimize-addPtr≡>⟨-⟩ (m +₁ o) cs))
    (cong (optimize-subPtr n) (merge-addPtr m o cs))
    (cong <⟨ n ⟩_ (merge-addPtr m o cs))
    i
  optimize-subPtr≡<⟨-⟩ n (merge-subPtr m o cs i) = isSet→isSet' trunc
    ((optimize-subPtr≡<⟨-⟩ ((n +₁ m) +₁ o) cs ∙ sym (merge-subPtr (n +₁ m) o cs)) ∙ sym (merge-subPtr n m (<⟨ o ⟩ cs)))
    (optimize-subPtr≡<⟨-⟩ (n +₁ (m +₁ o)) cs ∙ sym (merge-subPtr n (m +₁ o) cs))
    (cong (optimize-subPtr n) (merge-subPtr m o cs))
    (cong <⟨ n ⟩_ (merge-subPtr m o cs))
    i
  optimize-subPtr≡<⟨-⟩ n (merge-addVal m o cs i) = isSet→isSet' trunc
    (λ j → <⟨ n ⟩ (optimize-addVal≡+⟨-⟩ (m +₁ o) cs ∙ sym (merge-addVal m o cs)) j)
    (cong <⟨ n ⟩_ (optimize-addVal≡+⟨-⟩ (m +₁ o) cs))
    (cong (optimize-subPtr n) (merge-addVal m o cs))
    (cong <⟨ n ⟩_ (merge-addVal m o cs))
    i
  optimize-subPtr≡<⟨-⟩ n (merge-subVal m o cs i) = isSet→isSet' trunc
    (λ j → <⟨ n ⟩ (optimize-subVal≡-⟨-⟩ (m +₁ o) cs ∙ sym (merge-subVal m o cs)) j)
    (cong <⟨ n ⟩_ (optimize-subVal≡-⟨-⟩ (m +₁ o) cs))
    (cong (optimize-subPtr n) (merge-subVal m o cs))
    (cong <⟨ n ⟩_ (merge-subVal m o cs))
    i
  optimize-subPtr≡<⟨-⟩ n (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (cong (optimize-subPtr≡<⟨-⟩ n) p)
    (cong (optimize-subPtr≡<⟨-⟩ n) q)
    (λ k → optimize-subPtr≡<⟨-⟩ n cs)
    (λ k → optimize-subPtr≡<⟨-⟩ n cs₁)
    (λ k l → optimize-subPtr n (trunc cs cs₁ p q k l))
    (λ k l → <⟨ n ⟩ trunc cs cs₁ p q k l)
    i j

  optimize-addVal≡+⟨-⟩ : ∀ n cs → optimize-addVal n cs ≡ +⟨ n ⟩ cs
  optimize-addVal≡+⟨-⟩ n □ = refl
  optimize-addVal≡+⟨-⟩ n (>⟨ m ⟩ cs) = cong +⟨ n ⟩_ (optimize-addPtr≡>⟨-⟩ m cs)
  optimize-addVal≡+⟨-⟩ n (<⟨ m ⟩ cs) = cong +⟨ n ⟩_ (optimize-subPtr≡<⟨-⟩ m cs)
  optimize-addVal≡+⟨-⟩ n (+⟨ m ⟩ cs) = optimize-addVal≡+⟨-⟩ (n +₁ m) cs ∙ sym (merge-addVal n m cs)
  optimize-addVal≡+⟨-⟩ n (-⟨ m ⟩ cs) = cong +⟨ n ⟩_ (optimize-subVal≡-⟨-⟩ m cs)
  optimize-addVal≡+⟨-⟩ n (· cs) = cong (λ cs → +⟨ n ⟩ · cs) (optimize≡id cs)
  optimize-addVal≡+⟨-⟩ n (, cs) = cong (λ cs → +⟨ n ⟩ , cs) (optimize≡id cs)
  optimize-addVal≡+⟨-⟩ n ([ cs ] cs₁) = cong₂ (λ cs cs₁ → +⟨ n ⟩ [ cs ] cs₁) (optimize≡id cs) (optimize≡id cs₁)
  optimize-addVal≡+⟨-⟩ n (merge-addPtr m o cs i) = isSet→isSet' trunc
    (λ j → +⟨ n ⟩ (optimize-addPtr≡>⟨-⟩ (m +₁ o) cs ∙ sym (merge-addPtr m o cs)) j)
    (cong +⟨ n ⟩_ (optimize-addPtr≡>⟨-⟩ (m +₁ o) cs))
    (cong (optimize-addVal n) (merge-addPtr m o cs))
    (cong +⟨ n ⟩_ (merge-addPtr m o cs))
    i
  optimize-addVal≡+⟨-⟩ n (merge-subPtr m o cs i) = isSet→isSet' trunc
    (λ j → +⟨ n ⟩ (optimize-subPtr≡<⟨-⟩ (m +₁ o) cs ∙ sym (merge-subPtr m o cs)) j)
    (cong +⟨ n ⟩_ (optimize-subPtr≡<⟨-⟩ (m +₁ o) cs))
    (cong (optimize-addVal n) (merge-subPtr m o cs))
    (cong +⟨ n ⟩_ (merge-subPtr m o cs))
    i
  optimize-addVal≡+⟨-⟩ n (merge-addVal m o cs i) = isSet→isSet' trunc
    ((optimize-addVal≡+⟨-⟩ ((n +₁ m) +₁ o) cs ∙ sym (merge-addVal (n +₁ m) o cs)) ∙ sym (merge-addVal n m (+⟨ o ⟩ cs)))
    (optimize-addVal≡+⟨-⟩ (n +₁ (m +₁ o)) cs ∙ sym (merge-addVal n (m +₁ o) cs))
    (cong (optimize-addVal n) (merge-addVal m o cs))
    (cong +⟨ n ⟩_ (merge-addVal m o cs))
    i
  optimize-addVal≡+⟨-⟩ n (merge-subVal m o cs i) = isSet→isSet' trunc
    (λ j → +⟨ n ⟩ (optimize-subVal≡-⟨-⟩ (m +₁ o) cs ∙ sym (merge-subVal m o cs)) j)
    (cong +⟨ n ⟩_ (optimize-subVal≡-⟨-⟩ (m +₁ o) cs))
    (cong (optimize-addVal n) (merge-subVal m o cs))
    (cong +⟨ n ⟩_ (merge-subVal m o cs))
    i
  optimize-addVal≡+⟨-⟩ n (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (cong (optimize-addVal≡+⟨-⟩ n) p)
    (cong (optimize-addVal≡+⟨-⟩ n) q)
    (λ k → optimize-addVal≡+⟨-⟩ n cs)
    (λ k → optimize-addVal≡+⟨-⟩ n cs₁)
    (λ k l → optimize-addVal n (trunc cs cs₁ p q k l))
    (λ k l → +⟨ n ⟩ trunc cs cs₁ p q k l)
    i j

  optimize-subVal≡-⟨-⟩ : ∀ n cs → optimize-subVal n cs ≡ -⟨ n ⟩ cs
  optimize-subVal≡-⟨-⟩ n □ = refl
  optimize-subVal≡-⟨-⟩ n (>⟨ m ⟩ cs) = cong -⟨ n ⟩_ (optimize-addPtr≡>⟨-⟩ m cs)
  optimize-subVal≡-⟨-⟩ n (<⟨ m ⟩ cs) = cong -⟨ n ⟩_ (optimize-subPtr≡<⟨-⟩ m cs)
  optimize-subVal≡-⟨-⟩ n (+⟨ m ⟩ cs) = cong -⟨ n ⟩_ (optimize-addVal≡+⟨-⟩ m cs)
  optimize-subVal≡-⟨-⟩ n (-⟨ m ⟩ cs) = optimize-subVal≡-⟨-⟩ (n +₁ m) cs ∙ sym (merge-subVal n m cs)
  optimize-subVal≡-⟨-⟩ n (· cs) = cong (λ cs → -⟨ n ⟩ · cs) (optimize≡id cs)
  optimize-subVal≡-⟨-⟩ n (, cs) = cong (λ cs → -⟨ n ⟩ , cs) (optimize≡id cs)
  optimize-subVal≡-⟨-⟩ n ([ cs ] cs₁) = cong₂ (λ cs cs₁ → -⟨ n ⟩ [ cs ] cs₁) (optimize≡id cs) (optimize≡id cs₁)
  optimize-subVal≡-⟨-⟩ n (merge-addPtr m o cs i) = isSet→isSet' trunc
    (λ j → -⟨ n ⟩ (optimize-addPtr≡>⟨-⟩ (m +₁ o) cs ∙ sym (merge-addPtr m o cs)) j)
    (cong -⟨ n ⟩_ (optimize-addPtr≡>⟨-⟩ (m +₁ o) cs))
    (cong (optimize-subVal n) (merge-addPtr m o cs))
    (cong -⟨ n ⟩_ (merge-addPtr m o cs))
    i
  optimize-subVal≡-⟨-⟩ n (merge-subPtr m o cs i) = isSet→isSet' trunc
    (λ j → -⟨ n ⟩ (optimize-subPtr≡<⟨-⟩ (m +₁ o) cs ∙ sym (merge-subPtr m o cs)) j)
    (cong -⟨ n ⟩_ (optimize-subPtr≡<⟨-⟩ (m +₁ o) cs))
    (cong (optimize-subVal n) (merge-subPtr m o cs))
    (cong -⟨ n ⟩_ (merge-subPtr m o cs))
    i
  optimize-subVal≡-⟨-⟩ n (merge-addVal m o cs i) = isSet→isSet' trunc
    (λ j → -⟨ n ⟩ (optimize-addVal≡+⟨-⟩ (m +₁ o) cs ∙ sym (merge-addVal m o cs)) j)
    (cong -⟨ n ⟩_ (optimize-addVal≡+⟨-⟩ (m +₁ o) cs))
    (cong (optimize-subVal n) (merge-addVal m o cs))
    (cong -⟨ n ⟩_ (merge-addVal m o cs))
    i
  optimize-subVal≡-⟨-⟩ n (merge-subVal m o cs i) = isSet→isSet' trunc
    ((optimize-subVal≡-⟨-⟩ ((n +₁ m) +₁ o) cs ∙ sym (merge-subVal (n +₁ m) o cs)) ∙ sym (merge-subVal n m (-⟨ o ⟩ cs)))
    (optimize-subVal≡-⟨-⟩ (n +₁ (m +₁ o)) cs ∙ sym (merge-subVal n (m +₁ o) cs))
    (cong (optimize-subVal n) (merge-subVal m o cs))
    (cong -⟨ n ⟩_ (merge-subVal m o cs))
    i
  optimize-subVal≡-⟨-⟩ n (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (cong (optimize-subVal≡-⟨-⟩ n) p)
    (cong (optimize-subVal≡-⟨-⟩ n) q)
    (λ k → optimize-subVal≡-⟨-⟩ n cs)
    (λ k → optimize-subVal≡-⟨-⟩ n cs₁)
    (λ k l → optimize-subVal n (trunc cs cs₁ p q k l))
    (λ k l → -⟨ n ⟩ trunc cs cs₁ p q k l)
    i j

helloWorld′ : Opts
helloWorld′ = optimize (transport Cmds≡Opts helloWorld)

_ : helloWorld′ ≡
    +⟨ 1+ 71 ⟩ ·    -- "H"
    +⟨ 1+ 28 ⟩ ·    -- "e"
    +⟨ 1+ 6  ⟩ · ·  -- "ll"
    +⟨ 1+ 2  ⟩ ·    -- "o"
    -⟨ 1+ 66 ⟩ ·    -- ","
    -⟨ 1+ 11 ⟩ ·    -- " "
    +⟨ 1+ 86 ⟩ ·    -- "w"
    -⟨ 1+ 7  ⟩ ·    -- "o"
    +⟨ 1+ 2  ⟩ ·    -- "r"
    -⟨ 1+ 5  ⟩ ·    -- "l"
    -⟨ 1+ 7  ⟩ ·    -- "d"
    -⟨ 1+ 66 ⟩ ·    -- "!"
    □
_ = refl

_ : transport (sym Cmds≡Opts) helloWorld′ ≡ helloWorld
_ = refl

--------------------------------------------------------------------------------
-- Slow semantics: unoptimize before running

⟨_,_⟩⇒⟨_,_⟩ : Opts → State → Opts → State → Type
⟨_,_⟩⇒⟨_,_⟩ =
  transport
    (λ i → Cmds≡Opts i → State → Cmds≡Opts i → State → Type)
    Cmds.⟨_,_⟩⇒⟨_,_⟩

⟨_,_⟩⇒*⟨_,_⟩ : Opts → State → Opts → State → Type
⟨_,_⟩⇒*⟨_,_⟩ =
  transport
    (λ i → Cmds≡Opts i → State → Cmds≡Opts i → State → Type)
    Cmds.⟨_,_⟩⇒*⟨_,_⟩

_=⟦_⟧⇒*_ : State → Opts → State → Type
_=⟦_⟧⇒*_ =
  transport
    (λ i → State → Cmds≡Opts i → State → Type)
    Cmds._=⟦_⟧⇒*_

NoLoops : Opts → Type
NoLoops = transport (λ i → Cmds≡Opts i → Type) Cmds.NoLoops

NoLoops-filler : PathP (λ i → Cmds≡Opts i → Type) Cmds.NoLoops NoLoops
NoLoops-filler = transport-filler (λ i → Cmds≡Opts i → Type) Cmds.NoLoops

noLoops? : ∀ cs → Dec (NoLoops cs)
noLoops? =
  transport
    (λ i → ∀ (cs : Cmds≡Opts i) → Dec (NoLoops-filler i cs))
    Cmds.noLoops?

noLoops?-filler :
  PathP
    (λ i → (cs : Cmds≡Opts i) → Dec (NoLoops-filler i cs))
    Cmds.noLoops?
    noLoops?
noLoops?-filler =
  transport-filler
    (λ i → (cs : Cmds≡Opts i) → Dec (NoLoops-filler i cs))
    Cmds.noLoops?

⟦_⟧*! : ∀ cs {{_ : True (noLoops? cs)}} → State → State
⟦_⟧*! =
  transport
    (λ i → (cs : Cmds≡Opts i) {{_ : True (noLoops?-filler i cs)}} → State → State)
    Cmds.⟦_⟧*!

_ : getOutput (⟦ helloWorld′ ⟧*! default) ≡ "Hello, world!"
_ = refl

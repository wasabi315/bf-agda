{-# OPTIONS --cubical --guardedness #-}

module Brainfuck.Optimization where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool.Base using ( True; toWitness )
open import Cubical.Data.NatPlusOne.Base using ( ℕ₊₁; one; 1+_; 2+_; _+₁_ )
open import Cubical.Data.NatPlusOne.Properties as ℕ using ( +₁-assoc )
open import Cubical.Data.List.Base using ( List; []; _∷_; _++_ )
open import Cubical.Data.List.Properties using ( ++-assoc )
open import Cubical.Relation.Nullary using ( Dec )

open import Brainfuck.Syntax as Cmds hiding ( NoLoops; noLoops? )
open import Brainfuck.State
import Brainfuck.SmallStep as Cmds

private
  variable
    ℓ : Level
    A B : Type

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
    merge-`> : ∀ m n cs → `>⟨ m ⟩ ∷ `>⟨ n ⟩ ∷ cs ≡ `>⟨ m +₁ n ⟩ ∷ cs
    merge-`< : ∀ m n cs → `<⟨ m ⟩ ∷ `<⟨ n ⟩ ∷ cs ≡ `<⟨ m +₁ n ⟩ ∷ cs
    merge-`+ : ∀ m n cs → `+⟨ m ⟩ ∷ `+⟨ n ⟩ ∷ cs ≡ `+⟨ m +₁ n ⟩ ∷ cs
    merge-`- : ∀ m n cs → `-⟨ m ⟩ ∷ `-⟨ n ⟩ ∷ cs ≡ `-⟨ m +₁ n ⟩ ∷ cs
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
merge-`> m n cs i +++ cs₁ = merge-`> m n (cs +++ cs₁) i
merge-`< m n cs i +++ cs₁ = merge-`< m n (cs +++ cs₁) i
merge-`+ m n cs i +++ cs₁ = merge-`+ m n (cs +++ cs₁) i
merge-`- m n cs i +++ cs₁ = merge-`- m n (cs +++ cs₁) i
trunc cs cs₁ p q i j +++ cs₂ =
  trunc (cs +++ cs₂) (cs₁ +++ cs₂) (cong (_+++ cs₂) p) (cong (_+++ cs₂) q) i j

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
Opts→Cmds □ = □
Opts→Cmds (>⟨ n ⟩ cs) = replicate n `> ++ Opts→Cmds cs
Opts→Cmds (<⟨ n ⟩ cs) = replicate n `< ++ Opts→Cmds cs
Opts→Cmds (+⟨ n ⟩ cs) = replicate n `+ ++ Opts→Cmds cs
Opts→Cmds (-⟨ n ⟩ cs) = replicate n `- ++ Opts→Cmds cs
Opts→Cmds (· cs) = · Opts→Cmds cs
Opts→Cmds (, cs) = , Opts→Cmds cs
Opts→Cmds ([ cs ] cs₁) = [ Opts→Cmds cs ] Opts→Cmds cs₁
Opts→Cmds (merge-`> m n cs i) =
  begin⟨ i ⟩
    replicate m `> ++ replicate n `> ++ Opts→Cmds cs
  ≡⟨ sym (++-assoc (replicate m `>) (replicate n `>) _) ⟩
    (replicate m `> ++ replicate n `>) ++ Opts→Cmds cs
  ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
    replicate (m +₁ n) `> ++ Opts→Cmds cs
  ∎
Opts→Cmds (merge-`< m n cs i) =
  begin⟨ i ⟩
    replicate m `< ++ replicate n `< ++ Opts→Cmds cs
  ≡⟨ sym (++-assoc (replicate m `<) (replicate n `<) _) ⟩
    (replicate m `< ++ replicate n `<) ++ Opts→Cmds cs
  ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
    replicate (m +₁ n) `< ++ Opts→Cmds cs
  ∎
Opts→Cmds (merge-`+ m n cs i) =
  begin⟨ i ⟩
    replicate m `+ ++ replicate n `+ ++ Opts→Cmds cs
  ≡⟨ sym (++-assoc (replicate m `+) (replicate n `+) _) ⟩
    (replicate m `+ ++ replicate n `+) ++ Opts→Cmds cs
  ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
    replicate (m +₁ n) `+ ++ Opts→Cmds cs
  ∎
Opts→Cmds (merge-`- m n cs i) =
  begin⟨ i ⟩
    replicate m `- ++ replicate n `- ++ Opts→Cmds cs
  ≡⟨ sym (++-assoc (replicate m `-) (replicate n `-) _) ⟩
    (replicate m `- ++ replicate n `-) ++ Opts→Cmds cs
  ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
    replicate (m +₁ n) `- ++ Opts→Cmds cs
  ∎
Opts→Cmds (trunc cs cs₁ p q i j) =
  isSetCmds (Opts→Cmds cs) (Opts→Cmds cs₁) (cong Opts→Cmds p) (cong Opts→Cmds q) i j

Cmds→Opts-replicate-`> : ∀ n → Cmds→Opts (replicate n `>) ≡ >⟨ n ⟩ □
Cmds→Opts-replicate-`> one = refl
Cmds→Opts-replicate-`> (2+ n) =
    >⟨ one ⟩ Cmds→Opts (replicate (1+ n) `>)
  ≡⟨ cong >⟨ one ⟩_ (Cmds→Opts-replicate-`> (1+ n)) ⟩
    >⟨ one ⟩ >⟨ 1+ n ⟩ □
  ≡⟨ merge-`> one (1+ n) □ ⟩
    >⟨ 2+ n ⟩ □
  ∎

Cmds→Opts-replicate-`< : ∀ n → Cmds→Opts (replicate n `<) ≡ <⟨ n ⟩ □
Cmds→Opts-replicate-`< one = refl
Cmds→Opts-replicate-`< (2+ n) =
    <⟨ one ⟩ Cmds→Opts (replicate (1+ n) `<)
  ≡⟨ cong <⟨ one ⟩_ (Cmds→Opts-replicate-`< (1+ n)) ⟩
    <⟨ one ⟩ <⟨ 1+ n ⟩ □
  ≡⟨ merge-`< one (1+ n) □ ⟩
    <⟨ 2+ n ⟩ □
  ∎

Cmds→Opts-replicate-`+ : ∀ n → Cmds→Opts (replicate n `+) ≡ +⟨ n ⟩ □
Cmds→Opts-replicate-`+ one = refl
Cmds→Opts-replicate-`+ (2+ n) =
    +⟨ one ⟩ Cmds→Opts (replicate (1+ n) `+)
  ≡⟨ cong +⟨ one ⟩_ (Cmds→Opts-replicate-`+ (1+ n)) ⟩
    +⟨ one ⟩ +⟨ 1+ n ⟩ □
  ≡⟨ merge-`+ one (1+ n) □ ⟩
    +⟨ 2+ n ⟩ □
  ∎

Cmds→Opts-replicate-`- : ∀ n → Cmds→Opts (replicate n `-) ≡ -⟨ n ⟩ □
Cmds→Opts-replicate-`- one = refl
Cmds→Opts-replicate-`- (2+ n) =
    -⟨ one ⟩ Cmds→Opts (replicate (1+ n) `-)
  ≡⟨ cong -⟨ one ⟩_ (Cmds→Opts-replicate-`- (1+ n)) ⟩
    -⟨ one ⟩ -⟨ 1+ n ⟩ □
  ≡⟨ merge-`- one (1+ n) □ ⟩
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

{-# TERMINATING #-}
sect : ∀ (cs : Opts) → Cmds→Opts (Opts→Cmds cs) ≡ cs
sect □ = refl
sect (>⟨ n ⟩ cs) =
    Cmds→Opts (replicate n `> ++ Opts→Cmds cs)
  ≡⟨ Cmds→Opts-++ (replicate n `>) (Opts→Cmds cs) ⟩
    Cmds→Opts (replicate n `>) +++ Cmds→Opts (Opts→Cmds cs)
  ≡⟨ cong (_+++ Cmds→Opts (Opts→Cmds cs)) (Cmds→Opts-replicate-`> n) ⟩
    >⟨ n ⟩ Cmds→Opts (Opts→Cmds cs)
  ≡⟨ cong >⟨ n ⟩_ (sect cs) ⟩
    >⟨ n ⟩ cs
  ∎
sect (<⟨ n ⟩ cs) =
    Cmds→Opts (replicate n `< ++ Opts→Cmds cs)
  ≡⟨ Cmds→Opts-++ (replicate n `<) (Opts→Cmds cs) ⟩
    Cmds→Opts (replicate n `<) +++ Cmds→Opts (Opts→Cmds cs)
  ≡⟨ cong (_+++ Cmds→Opts (Opts→Cmds cs)) (Cmds→Opts-replicate-`< n) ⟩
    <⟨ n ⟩ Cmds→Opts (Opts→Cmds cs)
  ≡⟨ cong <⟨ n ⟩_ (sect cs) ⟩
    <⟨ n ⟩ cs
  ∎
sect (+⟨ n ⟩ cs) =
    Cmds→Opts (replicate n `+ ++ Opts→Cmds cs)
  ≡⟨ Cmds→Opts-++ (replicate n `+) (Opts→Cmds cs) ⟩
    Cmds→Opts (replicate n `+) +++ Cmds→Opts (Opts→Cmds cs)
  ≡⟨ cong (_+++ Cmds→Opts (Opts→Cmds cs)) (Cmds→Opts-replicate-`+ n) ⟩
    +⟨ n ⟩ Cmds→Opts (Opts→Cmds cs)
  ≡⟨ cong +⟨ n ⟩_ (sect cs) ⟩
    +⟨ n ⟩ cs
  ∎
sect (-⟨ n ⟩ cs) =
    Cmds→Opts (replicate n `- ++ Opts→Cmds cs)
  ≡⟨ Cmds→Opts-++ (replicate n `-) (Opts→Cmds cs) ⟩
    Cmds→Opts (replicate n `-) +++ Cmds→Opts (Opts→Cmds cs)
  ≡⟨ cong (_+++ Cmds→Opts (Opts→Cmds cs)) (Cmds→Opts-replicate-`- n) ⟩
    -⟨ n ⟩ Cmds→Opts (Opts→Cmds cs)
  ≡⟨ cong -⟨ n ⟩_ (sect cs) ⟩
    -⟨ n ⟩ cs
  ∎
sect (· cs) = cong ·_ (sect cs)
sect (, cs) = cong ,_ (sect cs)
sect ([ cs ] cs₁) = cong₂ [_]_ (sect cs) (sect cs₁)
sect (merge-`> m n cs i) = isSet→isSet' trunc
  (sect (>⟨ m ⟩ >⟨ n ⟩ cs))
  (sect (>⟨ m +₁ n ⟩ cs))
  (λ j → Cmds→Opts (Opts→Cmds (merge-`> m n cs j)))
  (λ j → merge-`> m n cs j)
  i
sect (merge-`< m n cs i) = isSet→isSet' trunc
  (sect (<⟨ m ⟩ <⟨ n ⟩ cs))
  (sect (<⟨ m +₁ n ⟩ cs))
  (λ j → Cmds→Opts (Opts→Cmds (merge-`< m n cs j)))
  (λ j → merge-`< m n cs j)
  i
sect (merge-`+ m n cs i) = isSet→isSet' trunc
  (sect (+⟨ m ⟩ +⟨ n ⟩ cs))
  (sect (+⟨ m +₁ n ⟩ cs))
  (λ j → Cmds→Opts (Opts→Cmds (merge-`+ m n cs j)))
  (λ j → merge-`+ m n cs j)
  i
sect (merge-`- m n cs i) = isSet→isSet' trunc
  (sect (-⟨ m ⟩ -⟨ n ⟩ cs))
  (sect (-⟨ m +₁ n ⟩ cs))
  (λ j → Cmds→Opts (Opts→Cmds (merge-`- m n cs j)))
  (λ j → merge-`- m n cs j)
  i
sect (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
  (λ k → sect (p k))
  (λ k → sect (q k))
  (λ k → sect cs)
  (λ k → sect cs₁)
  (λ k l → Cmds→Opts (Opts→Cmds (trunc cs cs₁ p q k l)))
  (λ k l → trunc cs cs₁ p q k l)
  i j

retr : ∀ (cs : Cmds) → Opts→Cmds (Cmds→Opts cs) ≡ cs
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

  {-# TERMINATING #-}
  optimize : Opts → Opts
  optimize □ = □
  optimize (>⟨ n ⟩ cs) = optimize-`> n cs
  optimize (<⟨ n ⟩ cs) = optimize-`< n cs
  optimize (+⟨ n ⟩ cs) = optimize-`+ n cs
  optimize (-⟨ n ⟩ cs) = optimize-`- n cs
  optimize (· cs) = · optimize cs
  optimize (, cs) = , optimize cs
  optimize ([ cs ] cs₁) = [ optimize cs ] optimize cs₁
  optimize (merge-`> m n cs i) = optimize-`> (m +₁ n) cs
  optimize (merge-`< m n cs i) = optimize-`< (m +₁ n) cs
  optimize (merge-`+ m n cs i) = optimize-`+ (m +₁ n) cs
  optimize (merge-`- m n cs i) = optimize-`- (m +₁ n) cs
  optimize (trunc cs cs₁ p q i j) =
    trunc _ _ (cong optimize p) (cong optimize q) i j

  optimize-`> : ℕ₊₁ → Opts → Opts
  optimize-`> n □ = >⟨ n ⟩ □
  optimize-`> n (>⟨ m ⟩ cs) = optimize-`> (n +₁ m) cs
  optimize-`> n cs@(_ ∷ _) = >⟨ n ⟩ optimize cs
  optimize-`> n (merge-`> m o cs i) = optimize-`> (+₁-assoc n m o (~ i)) cs
  optimize-`> n (merge-`< m o cs i) = >⟨ n ⟩ optimize-`< (m +₁ o) cs
  optimize-`> n (merge-`+ m o cs i) = >⟨ n ⟩ optimize-`+ (m +₁ o) cs
  optimize-`> n (merge-`- m o cs i) = >⟨ n ⟩ optimize-`- (m +₁ o) cs
  optimize-`> n (trunc cs cs₁ p q i j) =
    trunc _ _ (cong (optimize-`> n) p) (cong (optimize-`> n) q) i j

  optimize-`< : ℕ₊₁ → Opts → Opts
  optimize-`< n □ = <⟨ n ⟩ □
  optimize-`< n (<⟨ m ⟩ cs) = optimize-`< (n +₁ m) cs
  optimize-`< n cs@(_ ∷ _) = <⟨ n ⟩ optimize cs
  optimize-`< n (merge-`> m o cs i) = <⟨ n ⟩ optimize-`> (m +₁ o) cs
  optimize-`< n (merge-`< m o cs i) = optimize-`< (+₁-assoc n m o (~ i)) cs
  optimize-`< n (merge-`+ m o cs i) = <⟨ n ⟩ optimize-`+ (m +₁ o) cs
  optimize-`< n (merge-`- m o cs i) = <⟨ n ⟩ optimize-`- (m +₁ o) cs
  optimize-`< n (trunc cs cs₁ p q i j) =
    trunc _ _ (cong (optimize-`< n) p) (cong (optimize-`< n) q) i j

  optimize-`+ : ℕ₊₁ → Opts → Opts
  optimize-`+ n □ = +⟨ n ⟩ □
  optimize-`+ n (+⟨ m ⟩ cs) = optimize-`+ (n +₁ m) cs
  optimize-`+ n cs@(_ ∷ _) = +⟨ n ⟩ optimize cs
  optimize-`+ n (merge-`> m o cs i) = +⟨ n ⟩ optimize-`> (m +₁ o) cs
  optimize-`+ n (merge-`< m o cs i) = +⟨ n ⟩ optimize-`< (m +₁ o) cs
  optimize-`+ n (merge-`+ m o cs i) = optimize-`+ (+₁-assoc n m o (~ i)) cs
  optimize-`+ n (merge-`- m o cs i) = +⟨ n ⟩ optimize-`- (m +₁ o) cs
  optimize-`+ n (trunc cs cs₁ p q i j) =
    trunc _ _ (cong (optimize-`+ n) p) (cong (optimize-`+ n) q) i j

  optimize-`- : ℕ₊₁ → Opts → Opts
  optimize-`- n □ = -⟨ n ⟩ □
  optimize-`- n (-⟨ m ⟩ cs) = optimize-`- (n +₁ m) cs
  optimize-`- n cs@(_ ∷ _) = -⟨ n ⟩ optimize cs
  optimize-`- n (merge-`> m o cs i) = -⟨ n ⟩ optimize-`> (m +₁ o) cs
  optimize-`- n (merge-`< m o cs i) = -⟨ n ⟩ optimize-`< (m +₁ o) cs
  optimize-`- n (merge-`+ m o cs i) = -⟨ n ⟩ optimize-`+ (m +₁ o) cs
  optimize-`- n (merge-`- m o cs i) = optimize-`- (+₁-assoc n m o (~ i)) cs
  optimize-`- n (trunc cs cs₁ p q i j) =
    trunc _ _ (cong (optimize-`- n) p) (cong (optimize-`- n) q) i j

  optimize≡id : ∀ cs → optimize cs ≡ cs
  optimize≡id □ = refl
  optimize≡id (>⟨ n ⟩ cs) = optimize-`>≡>⟨-⟩ n cs
  optimize≡id (<⟨ n ⟩ cs) = optimize-`<≡<⟨-⟩ n cs
  optimize≡id (+⟨ n ⟩ cs) = optimize-`+≡+⟨-⟩ n cs
  optimize≡id (-⟨ n ⟩ cs) = optimize-`-≡-⟨-⟩ n cs
  optimize≡id (· cs) = cong ·_ (optimize≡id cs)
  optimize≡id (, cs) = cong ,_ (optimize≡id cs)
  optimize≡id ([ cs ] cs₁) = cong₂ [_]_ (optimize≡id cs) (optimize≡id cs₁)
  optimize≡id (merge-`> m n cs i) = isSet→isSet' trunc
    (optimize≡id (>⟨ m ⟩ (>⟨ n ⟩ cs)))
    (optimize≡id (>⟨ m +₁ n ⟩ cs))
    (λ j → optimize (merge-`> m n cs j))
    (λ j → merge-`> m n cs j)
    i
  optimize≡id (merge-`< m n cs i) = isSet→isSet' trunc
    (optimize≡id (<⟨ m ⟩ (<⟨ n ⟩ cs)))
    (optimize≡id (<⟨ m +₁ n ⟩ cs))
    (λ j → optimize (merge-`< m n cs j))
    (λ j → merge-`< m n cs j)
    i
  optimize≡id (merge-`+ m n cs i) = isSet→isSet' trunc
    (optimize≡id (+⟨ m ⟩ (+⟨ n ⟩ cs)))
    (optimize≡id (+⟨ m +₁ n ⟩ cs))
    (λ j → optimize (merge-`+ m n cs j))
    (λ j → merge-`+ m n cs j)
    i
  optimize≡id (merge-`- m n cs i) = isSet→isSet' trunc
    (optimize≡id (-⟨ m ⟩ (-⟨ n ⟩ cs)))
    (optimize≡id (-⟨ m +₁ n ⟩ cs))
    (λ j → optimize (merge-`- m n cs j))
    (λ j → merge-`- m n cs j)
    i
  optimize≡id (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (λ k → optimize≡id (p k))
    (λ k → optimize≡id (q k))
    (λ k → optimize≡id cs)
    (λ k → optimize≡id cs₁)
    (λ k l → optimize (trunc cs cs₁ p q k l))
    (λ k l → trunc cs cs₁ p q k l)
    i j

  optimize-`>≡>⟨-⟩ : ∀ n cs → optimize-`> n cs ≡ >⟨ n ⟩ cs
  optimize-`>≡>⟨-⟩ n □ = refl
  optimize-`>≡>⟨-⟩ n (>⟨ m ⟩ cs) =
      optimize-`> (n +₁ m) cs
    ≡⟨ optimize-`>≡>⟨-⟩ (n +₁ m) cs ⟩
      >⟨ n +₁ m ⟩ cs
    ≡⟨ sym (merge-`> n m cs) ⟩
      >⟨ n ⟩ >⟨ m ⟩ cs
    ∎
  optimize-`>≡>⟨-⟩ n (<⟨ m ⟩ cs) = cong >⟨ n ⟩_ (optimize-`<≡<⟨-⟩ m cs)
  optimize-`>≡>⟨-⟩ n (+⟨ m ⟩ cs) = cong >⟨ n ⟩_ (optimize-`+≡+⟨-⟩ m cs)
  optimize-`>≡>⟨-⟩ n (-⟨ m ⟩ cs) = cong >⟨ n ⟩_ (optimize-`-≡-⟨-⟩ m cs)
  optimize-`>≡>⟨-⟩ n (· cs) = cong (λ cs → >⟨ n ⟩ · cs) (optimize≡id cs)
  optimize-`>≡>⟨-⟩ n (, cs) = cong (λ cs → >⟨ n ⟩ , cs) (optimize≡id cs)
  optimize-`>≡>⟨-⟩ n ([ cs ] cs₁) = cong₂ (λ cs cs₁ → >⟨ n ⟩ [ cs ] cs₁) (optimize≡id cs) (optimize≡id cs₁)
  optimize-`>≡>⟨-⟩ n (merge-`> m o cs i) = isSet→isSet' trunc
    (optimize-`>≡>⟨-⟩ n (>⟨ m ⟩ (>⟨ o ⟩ cs)))
    (optimize-`>≡>⟨-⟩ n (>⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`> n (merge-`> m o cs j))
    (λ j → >⟨ n ⟩ merge-`> m o cs j)
    i
  optimize-`>≡>⟨-⟩ n (merge-`< m o cs i) = isSet→isSet' trunc
    (optimize-`>≡>⟨-⟩ n (<⟨ m ⟩ (<⟨ o ⟩ cs)))
    (optimize-`>≡>⟨-⟩ n (<⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`> n (merge-`< m o cs j))
    (λ j → >⟨ n ⟩ merge-`< m o cs j)
    i
  optimize-`>≡>⟨-⟩ n (merge-`+ m o cs i) = isSet→isSet' trunc
    (optimize-`>≡>⟨-⟩ n (+⟨ m ⟩ (+⟨ o ⟩ cs)))
    (optimize-`>≡>⟨-⟩ n (+⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`> n (merge-`+ m o cs j))
    (λ j → >⟨ n ⟩ merge-`+ m o cs j)
    i
  optimize-`>≡>⟨-⟩ n (merge-`- m o cs i) = isSet→isSet' trunc
    (optimize-`>≡>⟨-⟩ n (-⟨ m ⟩ (-⟨ o ⟩ cs)))
    (optimize-`>≡>⟨-⟩ n (-⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`> n (merge-`- m o cs j))
    (λ j → >⟨ n ⟩ merge-`- m o cs j)
    i
  optimize-`>≡>⟨-⟩ n (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (λ k → optimize-`>≡>⟨-⟩ n (p k))
    (λ k → optimize-`>≡>⟨-⟩ n (q k))
    (λ k → optimize-`>≡>⟨-⟩ n cs)
    (λ k → optimize-`>≡>⟨-⟩ n cs₁)
    (λ k l → optimize-`> n (trunc cs cs₁ p q k l))
    (λ k l → >⟨ n ⟩ trunc cs cs₁ p q k l)
    i j

  optimize-`<≡<⟨-⟩ : ∀ n cs → optimize-`< n cs ≡ <⟨ n ⟩ cs
  optimize-`<≡<⟨-⟩ n □ = refl
  optimize-`<≡<⟨-⟩ n (>⟨ m ⟩ cs) = cong <⟨ n ⟩_ (optimize-`>≡>⟨-⟩ m cs)
  optimize-`<≡<⟨-⟩ n (<⟨ m ⟩ cs) =
      optimize-`< (n +₁ m) cs
    ≡⟨ optimize-`<≡<⟨-⟩ (n +₁ m) cs ⟩
      <⟨ n +₁ m ⟩ cs
    ≡⟨ sym (merge-`< n m cs) ⟩
      <⟨ n ⟩ <⟨ m ⟩ cs
    ∎
  optimize-`<≡<⟨-⟩ n (+⟨ m ⟩ cs) = cong <⟨ n ⟩_ (optimize-`+≡+⟨-⟩ m cs)
  optimize-`<≡<⟨-⟩ n (-⟨ m ⟩ cs) = cong <⟨ n ⟩_ (optimize-`-≡-⟨-⟩ m cs)
  optimize-`<≡<⟨-⟩ n (· cs) = cong (λ cs → <⟨ n ⟩ · cs) (optimize≡id cs)
  optimize-`<≡<⟨-⟩ n (, cs) = cong (λ cs → <⟨ n ⟩ , cs) (optimize≡id cs)
  optimize-`<≡<⟨-⟩ n ([ cs ] cs₁) = cong₂ (λ cs cs₁ → <⟨ n ⟩ [ cs ] cs₁) (optimize≡id cs) (optimize≡id cs₁)
  optimize-`<≡<⟨-⟩ n (merge-`> m o cs i) = isSet→isSet' trunc
    (optimize-`<≡<⟨-⟩ n (>⟨ m ⟩ (>⟨ o ⟩ cs)))
    (optimize-`<≡<⟨-⟩ n (>⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`< n (merge-`> m o cs j))
    (λ j → <⟨ n ⟩ merge-`> m o cs j)
    i
  optimize-`<≡<⟨-⟩ n (merge-`< m o cs i) = isSet→isSet' trunc
    (optimize-`<≡<⟨-⟩ n (<⟨ m ⟩ (<⟨ o ⟩ cs)))
    (optimize-`<≡<⟨-⟩ n (<⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`< n (merge-`< m o cs j))
    (λ j → <⟨ n ⟩ merge-`< m o cs j)
    i
  optimize-`<≡<⟨-⟩ n (merge-`+ m o cs i) = isSet→isSet' trunc
    (optimize-`<≡<⟨-⟩ n (+⟨ m ⟩ (+⟨ o ⟩ cs)))
    (optimize-`<≡<⟨-⟩ n (+⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`< n (merge-`+ m o cs j))
    (λ j → <⟨ n ⟩ merge-`+ m o cs j)
    i
  optimize-`<≡<⟨-⟩ n (merge-`- m o cs i) = isSet→isSet' trunc
    (optimize-`<≡<⟨-⟩ n (-⟨ m ⟩ (-⟨ o ⟩ cs)))
    (optimize-`<≡<⟨-⟩ n (-⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`< n (merge-`- m o cs j))
    (λ j → <⟨ n ⟩ merge-`- m o cs j)
    i
  optimize-`<≡<⟨-⟩ n (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (λ k → optimize-`<≡<⟨-⟩ n (p k))
    (λ k → optimize-`<≡<⟨-⟩ n (q k))
    (λ k → optimize-`<≡<⟨-⟩ n cs)
    (λ k → optimize-`<≡<⟨-⟩ n cs₁)
    (λ k l → optimize-`< n (trunc cs cs₁ p q k l))
    (λ k l → <⟨ n ⟩ trunc cs cs₁ p q k l)
    i j

  optimize-`+≡+⟨-⟩ : ∀ n cs → optimize-`+ n cs ≡ +⟨ n ⟩ cs
  optimize-`+≡+⟨-⟩ n □ = refl
  optimize-`+≡+⟨-⟩ n (>⟨ m ⟩ cs) = cong +⟨ n ⟩_ (optimize-`>≡>⟨-⟩ m cs)
  optimize-`+≡+⟨-⟩ n (<⟨ m ⟩ cs) = cong +⟨ n ⟩_ (optimize-`<≡<⟨-⟩ m cs)
  optimize-`+≡+⟨-⟩ n (+⟨ m ⟩ cs) =
      optimize-`+ (n +₁ m) cs
    ≡⟨ optimize-`+≡+⟨-⟩ (n +₁ m) cs ⟩
      +⟨ n +₁ m ⟩ cs
    ≡⟨ sym (merge-`+ n m cs) ⟩
      +⟨ n ⟩ +⟨ m ⟩ cs
    ∎
  optimize-`+≡+⟨-⟩ n (-⟨ m ⟩ cs) = cong +⟨ n ⟩_ (optimize-`-≡-⟨-⟩ m cs)
  optimize-`+≡+⟨-⟩ n (· cs) = cong (λ cs → +⟨ n ⟩ · cs) (optimize≡id cs)
  optimize-`+≡+⟨-⟩ n (, cs) = cong (λ cs → +⟨ n ⟩ , cs) (optimize≡id cs)
  optimize-`+≡+⟨-⟩ n ([ cs ] cs₁) = cong₂ (λ cs cs₁ → +⟨ n ⟩ [ cs ] cs₁) (optimize≡id cs) (optimize≡id cs₁)
  optimize-`+≡+⟨-⟩ n (merge-`> m o cs i) = isSet→isSet' trunc
    (optimize-`+≡+⟨-⟩ n (>⟨ m ⟩ (>⟨ o ⟩ cs)))
    (optimize-`+≡+⟨-⟩ n (>⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`+ n (merge-`> m o cs j))
    (λ j → +⟨ n ⟩ merge-`> m o cs j)
    i
  optimize-`+≡+⟨-⟩ n (merge-`< m o cs i) = isSet→isSet' trunc
    (optimize-`+≡+⟨-⟩ n (<⟨ m ⟩ (<⟨ o ⟩ cs)))
    (optimize-`+≡+⟨-⟩ n (<⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`+ n (merge-`< m o cs j))
    (λ j → +⟨ n ⟩ merge-`< m o cs j)
    i
  optimize-`+≡+⟨-⟩ n (merge-`+ m o cs i) = isSet→isSet' trunc
    (optimize-`+≡+⟨-⟩ n (+⟨ m ⟩ (+⟨ o ⟩ cs)))
    (optimize-`+≡+⟨-⟩ n (+⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`+ n (merge-`+ m o cs j))
    (λ j → +⟨ n ⟩ merge-`+ m o cs j)
    i
  optimize-`+≡+⟨-⟩ n (merge-`- m o cs i) = isSet→isSet' trunc
    (optimize-`+≡+⟨-⟩ n (-⟨ m ⟩ (-⟨ o ⟩ cs)))
    (optimize-`+≡+⟨-⟩ n (-⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`+ n (merge-`- m o cs j))
    (λ j → +⟨ n ⟩ merge-`- m o cs j)
    i
  optimize-`+≡+⟨-⟩ n (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (λ k → optimize-`+≡+⟨-⟩ n (p k))
    (λ k → optimize-`+≡+⟨-⟩ n (q k))
    (λ k → optimize-`+≡+⟨-⟩ n cs)
    (λ k → optimize-`+≡+⟨-⟩ n cs₁)
    (λ k l → optimize-`+ n (trunc cs cs₁ p q k l))
    (λ k l → +⟨ n ⟩ trunc cs cs₁ p q k l)
    i j

  optimize-`-≡-⟨-⟩ : ∀ n cs → optimize-`- n cs ≡ -⟨ n ⟩ cs
  optimize-`-≡-⟨-⟩ n □ = refl
  optimize-`-≡-⟨-⟩ n (>⟨ m ⟩ cs) = cong -⟨ n ⟩_ (optimize-`>≡>⟨-⟩ m cs)
  optimize-`-≡-⟨-⟩ n (<⟨ m ⟩ cs) = cong -⟨ n ⟩_ (optimize-`<≡<⟨-⟩ m cs)
  optimize-`-≡-⟨-⟩ n (+⟨ m ⟩ cs) = cong -⟨ n ⟩_ (optimize-`+≡+⟨-⟩ m cs)
  optimize-`-≡-⟨-⟩ n (-⟨ m ⟩ cs) =
      optimize-`- (n +₁ m) cs
    ≡⟨ optimize-`-≡-⟨-⟩ (n +₁ m) cs ⟩
      -⟨ n +₁ m ⟩ cs
    ≡⟨ sym (merge-`- n m cs) ⟩
      -⟨ n ⟩ -⟨ m ⟩ cs
    ∎
  optimize-`-≡-⟨-⟩ n (· cs) = cong (λ cs → -⟨ n ⟩ · cs) (optimize≡id cs)
  optimize-`-≡-⟨-⟩ n (, cs) = cong (λ cs → -⟨ n ⟩ , cs) (optimize≡id cs)
  optimize-`-≡-⟨-⟩ n ([ cs ] cs₁) = cong₂ (λ cs cs₁ → -⟨ n ⟩ [ cs ] cs₁) (optimize≡id cs) (optimize≡id cs₁)
  optimize-`-≡-⟨-⟩ n (merge-`> m o cs i) = isSet→isSet' trunc
    (optimize-`-≡-⟨-⟩ n (>⟨ m ⟩ (>⟨ o ⟩ cs)))
    (optimize-`-≡-⟨-⟩ n (>⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`- n (merge-`> m o cs j))
    (λ j → -⟨ n ⟩ merge-`> m o cs j)
    i
  optimize-`-≡-⟨-⟩ n (merge-`< m o cs i) = isSet→isSet' trunc
    (optimize-`-≡-⟨-⟩ n (<⟨ m ⟩ (<⟨ o ⟩ cs)))
    (optimize-`-≡-⟨-⟩ n (<⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`- n (merge-`< m o cs j))
    (λ j → -⟨ n ⟩ merge-`< m o cs j)
    i
  optimize-`-≡-⟨-⟩ n (merge-`+ m o cs i) = isSet→isSet' trunc
    (optimize-`-≡-⟨-⟩ n (+⟨ m ⟩ (+⟨ o ⟩ cs)))
    (optimize-`-≡-⟨-⟩ n (+⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`- n (merge-`+ m o cs j))
    (λ j → -⟨ n ⟩ merge-`+ m o cs j)
    i
  optimize-`-≡-⟨-⟩ n (merge-`- m o cs i) = isSet→isSet' trunc
    (optimize-`-≡-⟨-⟩ n (-⟨ m ⟩ (-⟨ o ⟩ cs)))
    (optimize-`-≡-⟨-⟩ n (-⟨ m +₁ o ⟩ cs))
    (λ j → optimize-`- n (merge-`- m o cs j))
    (λ j → -⟨ n ⟩ merge-`- m o cs j)
    i
  optimize-`-≡-⟨-⟩ n (trunc cs cs₁ p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (λ k → optimize-`-≡-⟨-⟩ n (p k))
    (λ k → optimize-`-≡-⟨-⟩ n (q k))
    (λ k → optimize-`-≡-⟨-⟩ n cs)
    (λ k → optimize-`-≡-⟨-⟩ n cs₁)
    (λ k l → optimize-`- n (trunc cs cs₁ p q k l))
    (λ k l → -⟨ n ⟩ trunc cs cs₁ p q k l)
    i j

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

_ : getOutput (⟦ optimize (transport Cmds≡Opts helloWorld) ⟧*! default) ≡ "Hello, world!"
_ = refl

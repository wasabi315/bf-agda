{-# OPTIONS --cubical --guardedness #-}

module Brainfuck.Optimization where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool.Base using ( True; toWitness )
open import Cubical.Data.Nat.Base as ℕ using ( ℕ; zero; suc )
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

replicate : ℕ → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

merge-replicate : ∀ m n {x : A}
  → replicate m x ++ replicate n x ≡ replicate (m ℕ.+ n) x
merge-replicate zero n = refl
merge-replicate (suc m) n = cong (_ ∷_) (merge-replicate m n)

infix 1 begin⟨_⟩_
begin⟨_⟩_ : I → ∀ {x y} → Path A x y → A
begin⟨ i ⟩ p = p i

--------------------------------------------------------------------------------

mutual

  data Opt : Type where
    `>⟨_⟩ `<⟨_⟩ `+⟨_⟩ `-⟨_⟩ : (n : ℕ) → Opt
    `· `, : Opt
    `[_] : Opts → Opt

  data Opts : Type where
    [] : Opts
    _∷_ : (c : Opt) (cs : Opts) → Opts
    drop-`> : ∀ cs → `>⟨ 0 ⟩ ∷ cs ≡ cs
    drop-`< : ∀ cs → `<⟨ 0 ⟩ ∷ cs ≡ cs
    drop-`+ : ∀ cs → `+⟨ 0 ⟩ ∷ cs ≡ cs
    drop-`- : ∀ cs → `-⟨ 0 ⟩ ∷ cs ≡ cs
    merge-`> : ∀ m n cs → `>⟨ m ⟩ ∷ `>⟨ n ⟩ ∷ cs ≡ `>⟨ m ℕ.+ n ⟩ ∷ cs
    merge-`< : ∀ m n cs → `<⟨ m ⟩ ∷ `<⟨ n ⟩ ∷ cs ≡ `<⟨ m ℕ.+ n ⟩ ∷ cs
    merge-`+ : ∀ m n cs → `+⟨ m ⟩ ∷ `+⟨ n ⟩ ∷ cs ≡ `+⟨ m ℕ.+ n ⟩ ∷ cs
    merge-`- : ∀ m n cs → `-⟨ m ⟩ ∷ `-⟨ n ⟩ ∷ cs ≡ `-⟨ m ℕ.+ n ⟩ ∷ cs
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
drop-`> cs i +++ cs₁ = drop-`> (cs +++ cs₁) i
drop-`< cs i +++ cs₁ = drop-`< (cs +++ cs₁) i
drop-`+ cs i +++ cs₁ = drop-`+ (cs +++ cs₁) i
drop-`- cs i +++ cs₁ = drop-`- (cs +++ cs₁) i
merge-`> m n cs i +++ cs₁ = merge-`> m n (cs +++ cs₁) i
merge-`< m n cs i +++ cs₁ = merge-`< m n (cs +++ cs₁) i
merge-`+ m n cs i +++ cs₁ = merge-`+ m n (cs +++ cs₁) i
merge-`- m n cs i +++ cs₁ = merge-`- m n (cs +++ cs₁) i
trunc cs cs₁ p q i j +++ cs₂ =
  trunc (cs +++ cs₂) (cs₁ +++ cs₂) (cong (_+++ cs₂) p) (cong (_+++ cs₂) q) i j

--------------------------------------------------------------------------------

Cmds→Opts : Cmds → Opts
Cmds→Opts □ = □
Cmds→Opts (> cs) = >⟨ 1 ⟩ Cmds→Opts cs
Cmds→Opts (< cs) = <⟨ 1 ⟩ Cmds→Opts cs
Cmds→Opts (+ cs) = +⟨ 1 ⟩ Cmds→Opts cs
Cmds→Opts (- cs) = -⟨ 1 ⟩ Cmds→Opts cs
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
Opts→Cmds (drop-`> cs i) = Opts→Cmds cs
Opts→Cmds (drop-`< cs i) = Opts→Cmds cs
Opts→Cmds (drop-`+ cs i) = Opts→Cmds cs
Opts→Cmds (drop-`- cs i) = Opts→Cmds cs
Opts→Cmds (merge-`> m n cs i) =
  begin⟨ i ⟩
    replicate m `> ++ replicate n `> ++ Opts→Cmds cs
  ≡⟨ sym (++-assoc (replicate m `>) (replicate n `>) _) ⟩
    (replicate m `> ++ replicate n `>) ++ Opts→Cmds cs
  ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
    replicate (m ℕ.+ n) `> ++ Opts→Cmds cs
  ∎
Opts→Cmds (merge-`< m n cs i) =
  begin⟨ i ⟩
    replicate m `< ++ replicate n `< ++ Opts→Cmds cs
  ≡⟨ sym (++-assoc (replicate m `<) (replicate n `<) _) ⟩
    (replicate m `< ++ replicate n `<) ++ Opts→Cmds cs
  ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
    replicate (m ℕ.+ n) `< ++ Opts→Cmds cs
  ∎
Opts→Cmds (merge-`+ m n cs i) =
  begin⟨ i ⟩
    replicate m `+ ++ replicate n `+ ++ Opts→Cmds cs
  ≡⟨ sym (++-assoc (replicate m `+) (replicate n `+) _) ⟩
    (replicate m `+ ++ replicate n `+) ++ Opts→Cmds cs
  ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
    replicate (m ℕ.+ n) `+ ++ Opts→Cmds cs
  ∎
Opts→Cmds (merge-`- m n cs i) =
  begin⟨ i ⟩
    replicate m `- ++ replicate n `- ++ Opts→Cmds cs
  ≡⟨ sym (++-assoc (replicate m `-) (replicate n `-) _) ⟩
    (replicate m `- ++ replicate n `-) ++ Opts→Cmds cs
  ≡⟨ cong (_++ _) (merge-replicate m n) ⟩
    replicate (m ℕ.+ n) `- ++ Opts→Cmds cs
  ∎
Opts→Cmds (trunc cs cs₁ p q i j) =
  isSetCmds (Opts→Cmds cs) (Opts→Cmds cs₁) (cong Opts→Cmds p) (cong Opts→Cmds q) i j

Cmds→Opts-replicate-`> : ∀ n → Cmds→Opts (replicate n `>) ≡ >⟨ n ⟩ □
Cmds→Opts-replicate-`> zero = sym (drop-`> □)
Cmds→Opts-replicate-`> (suc n) =
    >⟨ 1 ⟩ Cmds→Opts (replicate n `>)
  ≡⟨ cong >⟨ 1 ⟩_ (Cmds→Opts-replicate-`> n) ⟩
    >⟨ 1 ⟩ >⟨ n ⟩ □
  ≡⟨ merge-`> 1 n □ ⟩
    >⟨ suc n ⟩ □
  ∎

Cmds→Opts-replicate-`< : ∀ n → Cmds→Opts (replicate n `<) ≡ <⟨ n ⟩ □
Cmds→Opts-replicate-`< zero = sym (drop-`< □)
Cmds→Opts-replicate-`< (suc n) =
    <⟨ 1 ⟩ Cmds→Opts (replicate n `<)
  ≡⟨ cong <⟨ 1 ⟩_ (Cmds→Opts-replicate-`< n) ⟩
    <⟨ 1 ⟩ <⟨ n ⟩ □
  ≡⟨ merge-`< 1 n □ ⟩
    <⟨ suc n ⟩ □
  ∎

Cmds→Opts-replicate-`+ : ∀ n → Cmds→Opts (replicate n `+) ≡ +⟨ n ⟩ □
Cmds→Opts-replicate-`+ zero = sym (drop-`+ □)
Cmds→Opts-replicate-`+ (suc n) =
    +⟨ 1 ⟩ Cmds→Opts (replicate n `+)
  ≡⟨ cong +⟨ 1 ⟩_ (Cmds→Opts-replicate-`+ n) ⟩
    +⟨ 1 ⟩ +⟨ n ⟩ □
  ≡⟨ merge-`+ 1 n □ ⟩
    +⟨ suc n ⟩ □
  ∎

Cmds→Opts-replicate-`- : ∀ n → Cmds→Opts (replicate n `-) ≡ -⟨ n ⟩ □
Cmds→Opts-replicate-`- zero = sym (drop-`- □)
Cmds→Opts-replicate-`- (suc n) =
    -⟨ 1 ⟩ Cmds→Opts (replicate n `-)
  ≡⟨ cong -⟨ 1 ⟩_ (Cmds→Opts-replicate-`- n) ⟩
    -⟨ 1 ⟩ -⟨ n ⟩ □
  ≡⟨ merge-`- 1 n □ ⟩
    -⟨ suc n ⟩ □
  ∎

Cmds→Opts-++ : ∀ cs cs₁ → Cmds→Opts (cs ++ cs₁) ≡ Cmds→Opts cs +++ Cmds→Opts cs₁
Cmds→Opts-++ □ cs₁ = refl
Cmds→Opts-++ (> cs) cs₁ = cong >⟨ 1 ⟩_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ (< cs) cs₁ = cong <⟨ 1 ⟩_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ (+ cs) cs₁ = cong +⟨ 1 ⟩_ (Cmds→Opts-++ cs cs₁)
Cmds→Opts-++ (- cs) cs₁ = cong -⟨ 1 ⟩_ (Cmds→Opts-++ cs cs₁)
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
sect (drop-`> cs i) = isSet→isSet' trunc
  (sect (>⟨ 0 ⟩ cs))
  (sect cs)
  (λ j → Cmds→Opts (Opts→Cmds (drop-`> cs j)))
  (λ j → drop-`> cs j)
  i
sect (drop-`< cs i) = isSet→isSet' trunc
  (sect (<⟨ 0 ⟩ cs))
  (sect cs)
  (λ j → Cmds→Opts (Opts→Cmds (drop-`< cs j)))
  (λ j → drop-`< cs j)
  i
sect (drop-`+ cs i) = isSet→isSet' trunc
  (sect (+⟨ 0 ⟩ cs))
  (sect cs)
  (λ j → Cmds→Opts (Opts→Cmds (drop-`+ cs j)))
  (λ j → drop-`+ cs j)
  i
sect (drop-`- cs i) = isSet→isSet' trunc
  (sect (-⟨ 0 ⟩ cs))
  (sect cs)
  (λ j → Cmds→Opts (Opts→Cmds (drop-`- cs j)))
  (λ j → drop-`- cs j)
  i
sect (merge-`> m n cs i) = isSet→isSet' trunc
  (sect (>⟨ m ⟩ >⟨ n ⟩ cs))
  (sect (>⟨ m ℕ.+ n ⟩ cs))
  (λ j → Cmds→Opts (Opts→Cmds (merge-`> m n cs j)))
  (λ j → merge-`> m n cs j)
  i
sect (merge-`< m n cs i) = isSet→isSet' trunc
  (sect (<⟨ m ⟩ <⟨ n ⟩ cs))
  (sect (<⟨ m ℕ.+ n ⟩ cs))
  (λ j → Cmds→Opts (Opts→Cmds (merge-`< m n cs j)))
  (λ j → merge-`< m n cs j)
  i
sect (merge-`+ m n cs i) = isSet→isSet' trunc
  (sect (+⟨ m ⟩ +⟨ n ⟩ cs))
  (sect (+⟨ m ℕ.+ n ⟩ cs))
  (λ j → Cmds→Opts (Opts→Cmds (merge-`+ m n cs j)))
  (λ j → merge-`+ m n cs j)
  i
sect (merge-`- m n cs i) = isSet→isSet' trunc
  (sect (-⟨ m ⟩ -⟨ n ⟩ cs))
  (sect (-⟨ m ℕ.+ n ⟩ cs))
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

optimize : Opts → Opts
optimize cs = {!   !}

--------------------------------------------------------------------------------
-- Slow semantics

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

_ : getOutput (⟦ transport Cmds≡Opts helloWorld ⟧*! default) ≡ "Hello, world!"
_ = refl

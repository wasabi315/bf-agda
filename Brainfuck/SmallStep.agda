{-# OPTIONS --cubical --guardedness #-}

module Brainfuck.SmallStep where

open import Cubical.Data.Bool.Base using ( True; toWitness )
open import Cubical.Data.Empty.Base as ⊥ using ( ⊥ )
open import Cubical.Data.Equality using ( pathToEq ) renaming ( _≡_ to _≡′_; refl to refl′ )
open import Cubical.Data.List.Base using ( List; []; _∷_; _++_; rev )
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; _+_; _∸_ )
open import Cubical.Data.Nat.Order.Recursive using ( _≤_; ≤-refl )
open import Cubical.Data.Nat.Properties using ( snotz; +-assoc; +-comm; n∸n )
open import Cubical.Data.Unit.Base using ( Unit; tt )
open import Cubical.Data.Sigma.Base using ( _×_; _,_ )
open import Cubical.Foundations.Prelude hiding ( step-≡; _∎ )
open import Cubical.Foundations.Function using ( idfun; _∘_ )
open import Cubical.Relation.Nullary.Base using ( ¬_; Dec; yes; no )
open import Data.Char.Base as Char using ( Char )
open import Data.String.Base as String using ( String )

open import Brainfuck.Syntax
open import Brainfuck.State

private
  variable
    A : Type
    n : ℕ

--------------------------------------------------------------------------------
-- Small-step semantics

private
  variable
    c : Cmd
    cs cs₁ cs₂ ⋯cs : Cmds
    s s₁ s₂ : State

⟦_⟧ : ∀ c {{_ : NotLoop c}} → State → State
⟦ `> ⟧ = incPtr
⟦ `< ⟧ = decPtr
⟦ `+ ⟧ = incVal
⟦ `- ⟧ = decVal
⟦ `· ⟧ = putCh
⟦ `, ⟧ = getCh

⟨_,_⟩⇒′⟨_,_⟩ : Cmds → State → Cmds → State → Type
⟨ □ , s ⟩⇒′⟨ cs₁ , s₁ ⟩ = ⊥
⟨ > cs , s ⟩⇒′⟨ cs₁ , s₁ ⟩ = (cs₁ ≡ cs) × (s₁ ≡ incPtr s)
⟨ < cs , s ⟩⇒′⟨ cs₁ , s₁ ⟩ = (cs₁ ≡ cs) × (s₁ ≡ decPtr s)
⟨ + cs , s ⟩⇒′⟨ cs₁ , s₁ ⟩ = (cs₁ ≡ cs) × (s₁ ≡ incVal s)
⟨ - cs , s ⟩⇒′⟨ cs₁ , s₁ ⟩ = (cs₁ ≡ cs) × (s₁ ≡ decVal s)
⟨ · cs , s ⟩⇒′⟨ cs₁ , s₁ ⟩ = (cs₁ ≡ cs) × (s₁ ≡ putCh s)
⟨ , cs , s ⟩⇒′⟨ cs₁ , s₁ ⟩ = (cs₁ ≡ cs) × (s₁ ≡ getCh s)
⟨ [ cs ] cs₁ , s@record { current = zero } ⟩⇒′⟨ cs₂ , s₁ ⟩ = (cs₂ ≡ cs₁) × (s₁ ≡ s)
⟨ [ cs ] cs₁ , s@record { current = suc _ } ⟩⇒′⟨ cs₂ , s₁ ⟩ = (cs₂ ≡ cs ++ [ cs ] cs₁) × (s₁ ≡ s)

data ⟨_,_⟩⇒⟨_,_⟩ (cs : Cmds) (s : State) (cs₁ : Cmds) (s₁ : State) : Type where
  con : ⟨ cs , s ⟩⇒′⟨ cs₁ , s₁ ⟩ → ⟨ cs , s ⟩⇒⟨ cs₁ , s₁ ⟩

-- just to prevent unfolding
opaque
  ⇒-incPtr : ⟨ > cs , s ⟩⇒⟨ cs , incPtr s ⟩
  ⇒-decPtr : ⟨ < cs , s ⟩⇒⟨ cs , decPtr s ⟩
  ⇒-incVal : ⟨ + cs , s ⟩⇒⟨ cs , incVal s ⟩
  ⇒-decVal : ⟨ - cs , s ⟩⇒⟨ cs , decVal s ⟩
  ⇒-putCh : ⟨ · cs , s ⟩⇒⟨ cs , putCh s ⟩
  ⇒-getCh : ⟨ , cs , s ⟩⇒⟨ cs , getCh s ⟩
  ⇒-loopZ : {{_ : Zero (current s)}} → ⟨ [ cs ] cs₁ , s ⟩⇒⟨ cs₁ , s ⟩
  ⇒-loopS : {{_ : NonZero (current s)}} → ⟨ [ cs ] cs₁ , s ⟩⇒⟨ cs ++ [ cs ] cs₁ , s ⟩
  ⇒-incPtr = con (refl , refl)
  ⇒-decPtr = con (refl , refl)
  ⇒-incVal = con (refl , refl)
  ⇒-decVal = con (refl , refl)
  ⇒-putCh = con (refl , refl)
  ⇒-getCh = con (refl , refl)
  ⇒-loopZ {s = record { current = zero }} = con (refl , refl)
  ⇒-loopS {s = record { current = suc _ }} = con (refl , refl)

-- Better ways to define reflexive transitive closure?
data ⟨_,_⟩⇒*⟨_,_⟩ (cs : Cmds) (s : State) (cs₁ : Cmds) (s₁ : State) : Type where
  nil : cs ≡ cs₁ → s ≡ s₁ → ⟨ cs , s ⟩⇒*⟨ cs₁ , s₁ ⟩
  _∷_ :
      ⟨ cs , s ⟩⇒⟨ cs₂ , s₂ ⟩
    → ⟨ cs₂ , s₂ ⟩⇒*⟨ cs₁ , s₁ ⟩
    → ⟨ cs , s ⟩⇒*⟨ cs₁ , s₁ ⟩

_=⟦_⟧⇒*_ : State → Cmds → State → Type
s =⟦ cs ⟧⇒* s₁ = ⟨ cs , s ⟩⇒*⟨ [] , s₁ ⟩

≡-to-⇒* : s ≡ s₁ → ⟨ cs , s ⟩⇒*⟨ cs , s₁ ⟩
≡-to-⇒* = nil refl

⇒*-refl : ⟨ cs , s ⟩⇒*⟨ cs , s ⟩
⇒*-refl = ≡-to-⇒* refl

⇒*-trans :
    ⟨ cs , s ⟩⇒*⟨ cs₁ , s₁ ⟩
  → ⟨ cs₁ , s₁ ⟩⇒*⟨ cs₂ , s₂ ⟩
  → ⟨ cs , s ⟩⇒*⟨ cs₂ , s₂ ⟩
⇒*-trans (nil p p') q = subst2 ⟨_,_⟩⇒*⟨ _ , _ ⟩ (sym p) (sym p') q
⇒*-trans (x ∷ p) q = x ∷ ⇒*-trans p q

------------------------------------------------------------------------------
-- Convenient mixfix operators for reasoning

module ⇒-Reasoning where

  infixr 2 step-⇒ step-⇒* step-≡ step-≡′
  infix 3 _,_∎

  step-⇒ : ∀ cs s
    → ⟨ cs₁ , s₁ ⟩⇒*⟨ cs₂ , s₂ ⟩
    → ⟨ cs , s ⟩⇒⟨ cs₁ , s₁ ⟩
    → ⟨ cs , s ⟩⇒*⟨ cs₂ , s₂ ⟩
  step-⇒ cs s p q = q ∷ p

  syntax step-⇒ cs s p q = cs , s ⇒⟨ q ⟩ p

  step-⇒* : ∀ cs s
    → ⟨ cs₁ , s₁ ⟩⇒*⟨ cs₂ , s₂ ⟩
    → ⟨ cs , s ⟩⇒*⟨ cs₁ , s₁ ⟩
    → ⟨ cs , s ⟩⇒*⟨ cs₂ , s₂ ⟩
  step-⇒* cs s p q = ⇒*-trans q p

  syntax step-⇒* cs s p q = cs , s ⇒*⟨ q ⟩ p

  step-≡ : ∀ cs s
    → ⟨ cs , s₁ ⟩⇒*⟨ cs₁ , s₂ ⟩
    → s ≡ s₁
    → ⟨ cs , s ⟩⇒*⟨ cs₁ , s₂ ⟩
  step-≡ cs s p q = ⇒*-trans (≡-to-⇒* q) p

  syntax step-≡ cs s p q = cs , s ≡⟨ q ⟩ p

  step-≡′ : ∀ cs s
    → ⟨ cs , s₁ ⟩⇒*⟨ cs₁ , s₂ ⟩
    → s₁ ≡ s
    → ⟨ cs , s ⟩⇒*⟨ cs₁ , s₂ ⟩
  step-≡′ cs s p q = ⇒*-trans (≡-to-⇒* (sym q)) p

  syntax step-≡′ cs s p q = cs , s ≡⟨ q ⟨ p

  _,_∎ : ∀ cs s → ⟨ cs , s ⟩⇒*⟨ cs , s ⟩
  cs , s ∎ = ⇒*-refl

--------------------------------------------------------------------------------
-- Determinism

⇒*-deterministic : s =⟦ cs ⟧⇒* s₁ → s =⟦ cs ⟧⇒* s₂ → s₁ ≡ s₂
⇒*-deterministic (nil p p') (nil q q') = sym p' ∙ q'
⇒*-deterministic {cs = □} (nil p p') (con () ∷ ss)
⇒*-deterministic {cs = _ ∷ _} (nil p p') (q ∷ ss) with () ← pathToEq p
⇒*-deterministic {cs = □} (con () ∷ ss) (nil q q')
⇒*-deterministic {cs = _ ∷ _} (p ∷ ss) (nil q q') with () ← pathToEq q
⇒*-deterministic {cs = □} (con () ∷ ss) (con () ∷ ss')
⇒*-deterministic {cs = > _} (con (p , p') ∷ ss) (con (q , q') ∷ ss')
  rewrite pathToEq p | pathToEq p' | pathToEq q | pathToEq q' = ⇒*-deterministic ss ss'
⇒*-deterministic {cs = < _} (con (p , p') ∷ ss) (con (q , q') ∷ ss')
  rewrite pathToEq p | pathToEq p' | pathToEq q | pathToEq q' = ⇒*-deterministic ss ss'
⇒*-deterministic {cs = + _} (con (p , p') ∷ ss) (con (q , q') ∷ ss')
  rewrite pathToEq p | pathToEq p' | pathToEq q | pathToEq q' = ⇒*-deterministic ss ss'
⇒*-deterministic {cs = - _} (con (p , p') ∷ ss) (con (q , q') ∷ ss')
  rewrite pathToEq p | pathToEq p' | pathToEq q | pathToEq q' = ⇒*-deterministic ss ss'
⇒*-deterministic {cs = · _} (con (p , p') ∷ ss) (con (q , q') ∷ ss')
  rewrite pathToEq p | pathToEq p' | pathToEq q | pathToEq q' = ⇒*-deterministic ss ss'
⇒*-deterministic {cs = , _} (con (p , p') ∷ ss) (con (q , q') ∷ ss')
  rewrite pathToEq p | pathToEq p' | pathToEq q | pathToEq q' = ⇒*-deterministic ss ss'
⇒*-deterministic {s = record { current = zero }} {cs = [ _ ] _} (con (p , p') ∷ ss) (con (q , q') ∷ ss')
  rewrite pathToEq p | pathToEq p' | pathToEq q | pathToEq q' = ⇒*-deterministic ss ss'
⇒*-deterministic {s = record { current = suc _ }} {cs = [ _ ] _} (con (p , p') ∷ ss) (con (q , q') ∷ ss')
  rewrite pathToEq p | pathToEq p' | pathToEq q | pathToEq q' = ⇒*-deterministic ss ss'

--------------------------------------------------------------------------------
-- Infinite Loop

infLoop : {{_ : NonZero (current s)}} → ¬ s =⟦ [ □ ] cs ⟧⇒* s₁
infLoop (nil p _) with () ← pathToEq p
infLoop {s = record { current = suc _ }} (con (p , q) ∷ r)
  rewrite pathToEq p | pathToEq q = infLoop r

--------------------------------------------------------------------------------
-- No Loops

⟦_⟧* : NoLoops cs → State → State
⟦_⟧* {□} tt = idfun _
⟦_⟧* {c ∷ cs} (nl , nls) = ⟦ nls ⟧* ∘ ⟦ c ⟧ {{nl}}

⟦_⟧*! : ∀ cs {{_ : True (noLoops? cs)}} → State → State
⟦ _ ⟧*! {{nls}} = ⟦ toWitness nls ⟧*

_ : getOutput (⟦ helloWorld ⟧*! default) ≡ "Hello, world!"
_ = refl

stepsNoLoops : (nls : NoLoops cs) → ⟨ cs ++ cs₁ , s ⟩⇒*⟨ cs₁ , ⟦ nls ⟧* s ⟩
stepsNoLoops {□} tt = ⇒*-refl
stepsNoLoops {> cs} (tt , nls) = ⇒-incPtr ∷ stepsNoLoops nls
stepsNoLoops {< cs} (tt , nls) = ⇒-decPtr ∷ stepsNoLoops nls
stepsNoLoops {+ cs} (tt , nls) = ⇒-incVal ∷ stepsNoLoops nls
stepsNoLoops { - cs} (tt , nls) = ⇒-decVal ∷ stepsNoLoops nls
stepsNoLoops {· cs} (tt , nls) = ⇒-putCh ∷ stepsNoLoops nls
stepsNoLoops {, cs} (tt , nls) = ⇒-getCh ∷ stepsNoLoops nls

stepsNoLoops! : ∀ cs {{_ : True (noLoops? cs)}}
  → ⟨ cs ++ cs₁ , s ⟩⇒*⟨ cs₁ , ⟦ cs ⟧*! s ⟩
stepsNoLoops! _ {{nls}} = stepsNoLoops (toWitness nls)

--------------------------------------------------------------------------------
-- Reasoning

module _ where
  open ⇒-Reasoning

  ⇒-decPtr-incPtr : ⟨ < > cs , s ⟩⇒*⟨ cs , s ⟩
  ⇒-decPtr-incPtr {cs} {s} =
    < > cs , s                    ⇒*⟨ stepsNoLoops! _ ⟩
    cs     , (incPtr ∘ decPtr) s  ≡⟨ incPtr∘decPtr ⟩
    cs     , s                    ∎

  ⇒-incPtr-decPtr : ⟨ > < cs , s ⟩⇒*⟨ cs , s ⟩
  ⇒-incPtr-decPtr {cs} {s} =
    > < cs , s                    ⇒*⟨ stepsNoLoops! _ ⟩
    cs     , (decPtr ∘ incPtr) s  ≡⟨ decPtr∘incPtr ⟩
    cs     , s                    ∎

  ⇒-incVal-decVal : ⟨ + - cs , s ⟩⇒*⟨ cs , s ⟩
  ⇒-incVal-decVal {cs} {s} =
    + - cs , s  ⇒*⟨ stepsNoLoops! _ ⟩
    cs     , s  ∎

  ⇒-decVal-incVal : ∀ {cs} {s} {{_ : NonZero (current s)}} → ⟨ - + cs , s ⟩⇒*⟨ cs , s ⟩
  ⇒-decVal-incVal {cs} {s} =
    - + cs , s                ⇒*⟨ stepsNoLoops! _ ⟩
    cs , (incVal ∘ decVal) s  ≡⟨ incVal∘decVal ⟩
    cs , s                    ∎

  ⇒-moveR1 : ⟨ - > + < cs , s ⟩⇒*⟨ cs , moveRN 1 s ⟩
  ⇒-moveR1 {cs} {s} =
    - > + < cs , s                                      ⇒*⟨ stepsNoLoops! _ ⟩
    cs         , (decPtr ∘ incVal ∘ incPtr ∘ decVal) s  ≡⟨ decomp-moveRN {s} ⟨
    cs         , moveRN 1 s                             ∎

  ⇒-moveR : ⟨ [ - > + < □ ] cs , s ⟩⇒*⟨ cs , moveR s ⟩
  ⇒-moveR {cs} {s} =
    [ - > + < □ ] cs , s                     ⇒*⟨ helper (≤-refl (current s)) ⟩
    [ - > + < □ ] cs , moveRN (current s) s  ≡⟨ moveRNcurrent ⟩
    [ - > + < □ ] cs , moveR s               ⇒⟨ ⇒-loopZ ⟩
    cs               , moveR s               ∎
    where
      helper : ∀ {cs s m}
        → m ≤ current s
        → ⟨ [ - > + < □ ] cs , s ⟩⇒*⟨ [ - > + < □ ] cs , moveRN m s ⟩
      helper {cs} {s} {zero} tt = ≡-to-⇒* (sym moveRN0)
      helper {cs} {s@record { current = suc _ }} {suc m} m≤n =
        [ - > + < □ ] cs         , s                        ⇒⟨ ⇒-loopS ⟩
        - > + < [ - > + < □ ] cs , s                        ⇒*⟨ ⇒-moveR1 ⟩
        [ - > + < □ ] cs         , moveRN 1 s               ⇒*⟨ helper m≤n ⟩
        [ - > + < □ ] cs         , (moveRN m ∘ moveRN 1) s  ≡⟨ +-moveRN {s} ⟩
        [ - > + < □ ] cs         , moveRN (1 + m) s         ∎

{-# OPTIONS --cubical --safe --guardedness #-}

module brainfuck where

open import Cubical.Codata.Stream.Base using ( Stream ) renaming ( _,_ to _∷_ )
open import Cubical.Codata.Stream.Properties using ( Stream-η )
open import Cubical.Data.Empty using ( rec )
open import Cubical.Data.Equality using ( eqToPath )
open import Cubical.Data.List using ( List; []; _∷_; _++_ )
open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_; _∸_ )
open import Cubical.Data.Nat.Properties using ( snotz; +-assoc; +-comm; n∸n )
open import Cubical.Foundations.Prelude hiding ( _∎ )
open import Cubical.Foundations.Function using ( idfun; _∘_; _$_ )
open import Cubical.Relation.Nullary using ( ¬_ )
open import Data.Nat using ( _≤_; z≤n; s≤s )
open import Data.Nat.Properties using ( ∸-+-assoc; ≤-refl )

open Stream

--------------------------------------------------------------------------------
-- Misc

suc-pred : ∀ n → ¬ n ≡ 0 → suc (n ∸ 1) ≡ n
suc-pred zero p = rec $ p refl
suc-pred (suc n) _ = refl

mapHead : ∀ {A} → (A → A) → Stream A → Stream A
mapHead f s .head = f $ head s
mapHead f s .tail = tail s

mapHead-id : ∀ {A} s → mapHead (idfun A) s ≡ s
mapHead-id s i .head = head s
mapHead-id s i .tail = tail s

--------------------------------------------------------------------------------
-- Syntax

mutual

  Cmds : Set
  Cmds = List Cmd

  data Cmd : Set where
    `> : Cmd
    `< : Cmd
    `+ : Cmd
    `- : Cmd
    `· : Cmd
    `, : Cmd
    `[_] : Cmds → Cmd

pattern >_ xs = `> ∷ xs
pattern <_ xs = `< ∷ xs
pattern +_ xs = `+ ∷ xs
pattern -_ xs = `- ∷ xs
pattern ·_ xs = `· ∷ xs
pattern ,_ xs = `, ∷ xs
pattern [_]_ xs ys = `[ xs ] ∷ ys
pattern □ = []

--------------------------------------------------------------------------------
-- The state of the machine

record State : Set where
  constructor ⟨_,_,_,_,_⟩
  field
    left    : Stream ℕ
    current : ℕ
    right   : Stream ℕ
    input   : Stream ℕ
    output  : List ℕ

open State

incPtr decPtr incVal decVal getCh putCh : State → State
incPtr ⟨ ls , c , rs , is , os ⟩ = ⟨ c ∷ ls , head rs , tail rs , is , os ⟩
decPtr ⟨ ls , c , rs , is , os ⟩ = ⟨ tail ls , head ls , c ∷ rs , is , os ⟩
incVal ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , suc c , rs , is , os ⟩
decVal ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , c ∸ 1 , rs , is , os ⟩
putCh ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , c , rs , is , c ∷ os ⟩
getCh ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , head is , rs , tail is , os ⟩

decPtr∘incPtr : ∀ {s} → (decPtr ∘ incPtr) s ≡ s
decPtr∘incPtr {s} i =
  record s { right = Stream-η {xs = right s} (~ i) }

incPtr∘decPtr : ∀ {s} → (incPtr ∘ decPtr) s ≡ s
incPtr∘decPtr {s} i =
  record s { left = Stream-η {xs = left s} (~ i) }

incVal∘decVal : ∀ {s} → ¬ current s ≡ 0 → (incVal ∘ decVal) s ≡ s
incVal∘decVal {s} p i =
  record s { current = suc-pred (current s) p i }

--------------------------------------------------------------------------------
-- Small-step semantics

private
  variable
    cs cs₁ cs₂ : Cmds
    s s₁ s₂ : State

infix 0 ⟨_,_⟩⇒⟨_,_⟩ ⟨_,_⟩⇒*⟨_,_⟩

data ⟨_,_⟩⇒⟨_,_⟩ : Cmds → State → Cmds → State → Set where
  ⇒> : ⟨ > cs , s ⟩⇒⟨ cs , incPtr s ⟩
  ⇒< : ⟨ < cs , s ⟩⇒⟨ cs , decPtr s ⟩
  ⇒+ : ⟨ + cs , s ⟩⇒⟨ cs , incVal s ⟩
  ⇒- : ⟨ - cs , s ⟩⇒⟨ cs , decVal s ⟩
  ⇒· : ⟨ · cs , s ⟩⇒⟨ cs , putCh s ⟩
  ⇒, : ⟨ , cs , s ⟩⇒⟨ cs , getCh s ⟩
  ⇒[≡0] :
      current s ≡ 0
    → ⟨ [ cs ] cs₁ , s ⟩⇒⟨ cs₁ , s ⟩
  ⇒[≢0] :
      ¬ current s ≡ zero
    → ⟨ [ cs ] cs₁ , s ⟩⇒⟨ cs ++ [ cs ] cs₁ , s ⟩

data ⟨_,_⟩⇒*⟨_,_⟩ : Cmds → State → Cmds → State → Set where
  [] : ⟨ cs , s ⟩⇒*⟨ cs , s ⟩
  _∷_ :
      ⟨ cs , s ⟩⇒⟨ cs₁ , s₁ ⟩
    → ⟨ cs₁ , s₁ ⟩⇒*⟨ cs₂ , s₂ ⟩
    → ⟨ cs , s ⟩⇒*⟨ cs₂ , s₂ ⟩

from≡ₛ : s ≡ s₁ → ⟨ cs , s ⟩⇒*⟨ cs , s₁ ⟩
from≡ₛ eq = subst ⟨ _ , _ ⟩⇒*⟨ _ ,_⟩ eq []


--------------------------------------------------------------------------------
-- Convenient mixfix operators for reasoning

module ⇒-Reasoning where

  infix 1 begin_
  infixr 2 _,_⇒⟨_⟩_ _,_⇒*⟨_⟩_ _,_≡ₛ⟨_⟩_
  infix 3 _,_∎

  begin_ : ⟨ cs , s ⟩⇒*⟨ cs₁ , s₁ ⟩ → ⟨ cs , s ⟩⇒*⟨ cs₁ , s₁ ⟩
  begin p = p

  _,_⇒⟨_⟩_ : ∀ cs s
    → ⟨ cs , s ⟩⇒⟨ cs₁ , s₁ ⟩
    → ⟨ cs₁ , s₁ ⟩⇒*⟨ cs₂ , s₂ ⟩
    → ⟨ cs , s ⟩⇒*⟨ cs₂ , s₂ ⟩
  cs , s ⇒⟨ p ⟩ q = p ∷ q

  _,_⇒*⟨_⟩_ : ∀ cs s
    → ⟨ cs , s ⟩⇒*⟨ cs₁ , s₁ ⟩
    → ⟨ cs₁ , s₁ ⟩⇒*⟨ cs₂ , s₂ ⟩
    → ⟨ cs , s ⟩⇒*⟨ cs₂ , s₂ ⟩
  cs , s ⇒*⟨ [] ⟩ r = r
  cs , s ⇒*⟨ p ∷ q ⟩ r = p ∷ (_ , _ ⇒*⟨ q ⟩ r)

  _,_≡ₛ⟨_⟩_ : ∀ cs s
    → s ≡ s₁
    → ⟨ cs , s₁ ⟩⇒*⟨ cs₁ , s₂ ⟩
    → ⟨ cs , s ⟩⇒*⟨ cs₁ , s₂ ⟩
  cs , s ≡ₛ⟨ p ⟩ q = subst ⟨ cs ,_⟩⇒*⟨ _ , _ ⟩ (sym p) q

  _,_∎ : ∀ cs s → ⟨ cs , s ⟩⇒*⟨ cs , s ⟩
  cs , s ∎ = []

--------------------------------------------------------------------------------
-- Reasoning

⇒<> : ⟨ < > cs , s ⟩⇒*⟨ cs , s ⟩
⇒<> {s = s} =
  begin
    < > _ , s
  ⇒*⟨ ⇒< ∷ ⇒> ∷ [] ⟩
    _ , (incPtr ∘ decPtr) s
  ≡ₛ⟨ incPtr∘decPtr ⟩
    _ , s
  ∎
  where open ⇒-Reasoning

⇒>< : ⟨ > < cs , s ⟩⇒*⟨ cs , s ⟩
⇒>< {s = s} =
  begin
    > < _ , s
  ⇒*⟨ ⇒> ∷ ⇒< ∷ [] ⟩
    _ , (decPtr ∘ incPtr) s
  ≡ₛ⟨ decPtr∘incPtr ⟩
    _ , s
  ∎
  where open ⇒-Reasoning

⇒+- : ⟨ + - cs , s ⟩⇒*⟨ cs , s ⟩
⇒+- {s = s} =
  begin
    + - _ , s
  ⇒*⟨ ⇒+ ∷ ⇒- ∷ [] ⟩
    _ , s
  ∎
  where open ⇒-Reasoning

⇒-+ : ¬ current s ≡ 0 → ⟨ - + cs , s ⟩⇒*⟨ cs , s ⟩
⇒-+ {s = s} p =
  begin
    - + _ , s
  ⇒*⟨ ⇒- ∷ ⇒+ ∷ [] ⟩
    _ , (incVal ∘ decVal) s
  ≡ₛ⟨ incVal∘decVal p ⟩
    _ , s
  ∎
  where open ⇒-Reasoning

-- Idioms

moveR : State → State
moveR ⟨ left , current , right , input , output ⟩ =
  ⟨ left , 0 , mapHead (_+_ current) right , input , output ⟩

moveRN : ℕ → State → State
moveRN n ⟨ left , current , right , input , output ⟩ =
  ⟨ left , current ∸ n , mapHead (_+_ n) right , input , output ⟩

moveRN0 : moveRN 0 s ≡ s
moveRN0 {s} i =
  record s { right = mapHead-id (right s) i }

moveRNcurrent : moveRN (current s) s ≡ moveR s
moveRNcurrent {s} i =
  record (moveR s) { current = n∸n (current s) i }

+-moveRN : ∀ {m n} → (moveRN m ∘ moveRN n) s ≡ moveRN (n + m) s
+-moveRN {s} {m} {n} i =
  record s
    { current = eqToPath (∸-+-assoc (current s) n m) i
    ; right = lem m n i $ right s
    }
  where
    lem : ∀ m n → mapHead (_+_ m) ∘ mapHead (_+_ n) ≡ mapHead (_+_ (n + m))
    head (lem m n i s) = (+-assoc m n (head s) ∙ cong (_+ head s) (+-comm m n)) i
    tail (lem m n i s) = tail s

decomp-moveRN : moveRN 1 s ≡ (decPtr ∘ incVal ∘ incPtr ∘ decVal) s
decomp-moveRN {s} i =
  record (moveRN 1 s) { right = Stream-η {xs = mapHead suc (right s)} i }

⇒->+< : ⟨ - > + < cs , s ⟩⇒*⟨ cs , moveRN 1 s ⟩
⇒->+< {s = s} =
  begin
    - > + < _ , s
  ⇒*⟨ ⇒- ∷ ⇒> ∷ ⇒+ ∷ ⇒< ∷ [] ⟩
    _ , (decPtr ∘ incVal ∘ incPtr ∘ decVal) s
  ≡ₛ⟨ sym (decomp-moveRN {s}) ⟩
    _ , moveRN 1 s
  ∎
  where open ⇒-Reasoning

⇒[->+<] : ⟨ [ - > + < □ ] cs , s ⟩⇒*⟨ cs , moveR s ⟩
⇒[->+<] {s = s} =
  begin
    [ - > + < □ ] _ , s
  ⇒*⟨ loop ≤-refl ⟩
    [ - > + < □ ] _ , moveRN (current s) s
  ≡ₛ⟨ moveRNcurrent ⟩
    [ - > + < □ ] _ , moveR s
  ⇒⟨ ⇒[≡0] refl ⟩
    _ , moveR s
  ∎
  where
    open ⇒-Reasoning

    loop : ∀ {s m}
      → m ≤ current s
      → ⟨ [ - > + < □ ] cs , s ⟩⇒*⟨ [ - > + < □ ] cs , moveRN m s ⟩
    loop {s = s} {.zero} z≤n = from≡ₛ $ sym moveRN0
    loop {s = s} {suc m} (s≤s m≤n) =
      begin
        [ - > + < □ ] _ , s
      ⇒⟨ ⇒[≢0] snotz ⟩
        - > + < [ - > + < □ ] _ , s
      ⇒*⟨ ⇒->+< ⟩
        [ - > + < □ ] _ , moveRN 1 s
      ⇒*⟨ loop m≤n ⟩
        [ - > + < □ ] _ , (moveRN m ∘ moveRN 1) s
      ≡ₛ⟨ +-moveRN {s} ⟩
        [ - > + < □ ] _ , moveRN (1 + m) s
      ∎

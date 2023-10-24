{-# OPTIONS --cubical --safe --guardedness #-}

module brainfuck where

open import Cubical.Codata.Stream.Base using ( Stream ) renaming ( _,_ to _∷_ )
open import Cubical.Codata.Stream.Properties using ( Stream-η )
open import Cubical.Data.Empty using ( rec )
open import Cubical.Data.Equality using ( eqToPath )
open import Cubical.Data.List using ( List; _∷_ )
open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_; _∸_ )
open import Cubical.Data.Nat.Properties using ( snotz; +-assoc; +-comm; n∸n )
open import Cubical.Data.Sigma using ( _×_; _,_; fst; snd )
open import Cubical.Foundations.Prelude hiding ( _∎ )
open import Cubical.Foundations.Function using ( idfun; _∘_; _$_ )
open import Cubical.Relation.Nullary using ( ¬_ )
open import Data.Nat using ( _≤_; z≤n; s≤s )
open import Data.Nat.Properties using ( ∸-+-assoc; ≤-refl )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using ( Star; ε; _◅_; _◅◅_ )

open Stream

-- Misc -----------------------------------------------------------------------

suc-pred : ∀ n → ¬ n ≡ 0 → suc (n ∸ 1) ≡ n
suc-pred zero p = rec $ p refl
suc-pred (suc n) _ = refl

mapHead : ∀ {A} → (A → A) → Stream A → Stream A
mapHead f s .head = f $ head s
mapHead f s .tail = tail s

mapHead-id : ∀ {A} → mapHead (idfun A) ≡ idfun (Stream A)
mapHead-id i s .head = head s
mapHead-id i s .tail = tail s

mapHead-∘ : ∀ {A} {f g : A → A} → mapHead f ∘ mapHead g ≡ mapHead (f ∘ g)
mapHead-∘ {A} {f} {g} i s .head = f ∘ g $ head s
mapHead-∘ {A} {f} {g} i s .tail = tail s


-- Syntax ---------------------------------------------------------------------

infixr 15 _▶_

data Cmds : Set where
  >_   : Cmds → Cmds
  <_   : Cmds → Cmds
  +_   : Cmds → Cmds
  -_   : Cmds → Cmds
  ·_   : Cmds → Cmds
  ,_   : Cmds → Cmds
  [_]_ : Cmds → Cmds → Cmds
  □    : Cmds

-- c1 ▶ c2 computes a new command equivalent to c1 followed by c2
_▶_ : Cmds → Cmds → Cmds
> c        ▶ c' = > (c ▶ c')
< c        ▶ c' = < (c ▶ c')
+ c        ▶ c' = + (c ▶ c')
- c        ▶ c' = - (c ▶ c')
· c        ▶ c' = · (c ▶ c')
, c        ▶ c' = , (c ▶ c')
[ body ] c ▶ c' = [ body ] (c ▶ c')
□          ▶ c' = c'


-- The state of the machine ---------------------------------------------------

record State : Set where
  constructor ⟨_,_,_,_,_⟩
  field
    left    : Stream ℕ
    current : ℕ
    right   : Stream ℕ
    input   : Stream ℕ
    output  : List ℕ

open State

focusL : State → State
focusL ⟨ left , current , right , input , output ⟩ =
  ⟨ tail left , head left , current ∷ right , input , output ⟩

focusR : State → State
focusR ⟨ left , current , right , input , output ⟩ =
  ⟨ current ∷ left , head right , tail right , input , output ⟩

putCh : State → State
putCh ⟨ left , current , right , input , output ⟩ =
  ⟨ left , current , right , input , current ∷ output ⟩

getCh : State → State
getCh ⟨ left , current , right , input , output ⟩ =
  ⟨ left , head input , right , tail input , output ⟩

incr : State → State
incr ⟨ left , current , right , input , output ⟩ =
  ⟨ left , suc current , right , input , output ⟩

decr : State → State
decr ⟨ left , current , right , input , output ⟩ =
  ⟨ left , current ∸ 1 , right , input , output ⟩

focusL∘focusR : focusL ∘ focusR ≡ idfun State
focusL∘focusR i s =
  record s { right = Stream-η {xs = right s} (~ i) }

focusR∘focusL : focusR ∘ focusL ≡ idfun State
focusR∘focusL i s =
  record s { left = Stream-η {xs = left s} (~ i) }

incr∘decr : ∀ {s} → ¬ current s ≡ 0 → (incr ∘ decr) s ≡ s
incr∘decr {s} p i =
  record s { current = suc-pred (current s) p i }

-- Small-step semantics -------------------------------------------------------

infix 0 _↦_ _↦∗_

data _↦_ : Cmds × State → Cmds × State → Set where
  ↦> : ∀ {cs s} → > cs , s ↦ cs , focusR s
  ↦< : ∀ {cs s} → < cs , s ↦ cs , focusL s
  ↦+ : ∀ {cs s} → + cs , s ↦ cs , incr s
  ↦- : ∀ {cs s} → - cs , s ↦ cs , decr s
  ↦· : ∀ {cs s} → · cs , s ↦ cs , putCh s
  ↦, : ∀ {cs s} → , cs , s ↦ cs , getCh s
  ↦[≡0] :
    ∀ {body cs s} → current s ≡ zero →
    [ body ] cs , s ↦ cs , s
  ↦[≢0] :
    ∀ {body cs s} → ¬ current s ≡ zero →
    [ body ] cs , s ↦ body ▶ [ body ] cs , s

_↦∗_ : Cmds × State → Cmds × State → Set
_↦∗_ = Star _↦_

from≡ₛ : ∀ {cs s t} → s ≡ t → cs , s ↦∗ cs , t
from≡ₛ {cs} {s} eq = subst (λ t → cs , s ↦∗ cs , t) eq ε


-- Convenient mixfix operators for reasoning ----------------------------------

module ↦-Reasoning where

  infix 1 begin_
  infixr 2 _↦⟨⟩_ _↦⟨_⟩_ _↦∗⟨_⟩_ _≡ₛ⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y} → x ↦∗ y → x ↦∗ y
  begin p = p

  _↦⟨⟩_ : ∀ x {y} → x ↦∗ y → x ↦∗ y
  x ↦⟨⟩ p = p

  _↦⟨_⟩_ : ∀ x {y z} → x ↦ y → y ↦∗ z → x ↦∗ z
  x ↦⟨ s ⟩ p = s ◅ p

  _↦∗⟨_⟩_ : ∀ x {y z} → x ↦∗ y → y ↦∗ z → x ↦∗ z
  x ↦∗⟨ p ⟩ q = p ◅◅ q

  _≡ₛ⟨_⟩_ : ∀ x {s y} → snd x ≡ s → fst x , s ↦∗ y → x ↦∗ y
  x ≡ₛ⟨ eq ⟩ p = from≡ₛ eq ◅◅ p

  _∎ : ∀ x → x ↦∗ x
  _∎ x = ε


-- Reasoning ------------------------------------------------------------------

↦<> : ∀ {cs s} → < > cs , s ↦∗ cs , s
↦<> {cs} {s} =
  begin
    < > cs , s
  ↦∗⟨ ↦< ◅ ↦> ◅ ε ⟩
    cs , (focusR ∘ focusL) s
  ≡ₛ⟨ focusR∘focusL ≡$ s ⟩
    cs , s
  ∎
  where open ↦-Reasoning

↦>< : ∀ {cs s} → > < cs , s ↦∗ cs , s
↦>< {cs} {s} =
  begin
    > < cs , s
  ↦∗⟨ ↦> ◅ ↦< ◅ ε ⟩
    cs , (focusL ∘ focusR) s
  ≡ₛ⟨ focusL∘focusR ≡$ s ⟩
    cs , s
  ∎
  where open ↦-Reasoning

↦+- : ∀ {cs s} → + - cs , s ↦∗ cs , s
↦+- {cs} {s} =
  begin
    + - cs , s
  ↦∗⟨ ↦+ ◅ ↦- ◅ ε ⟩
    cs , (decr ∘ incr) s
  ≡ₛ⟨ refl ⟩
    cs , s
  ∎
  where open ↦-Reasoning

↦-+ : ∀ {cs s} → ¬ current s ≡ 0 → - + cs , s ↦∗ cs , s
↦-+ {cs} {s} p =
  begin
    - + cs , s
  ↦∗⟨ ↦- ◅ ↦+ ◅ ε ⟩
    cs , (incr ∘ decr) s
  ≡ₛ⟨ incr∘decr p ⟩
    cs , s
  ∎
  where open ↦-Reasoning

-- Idioms

moveR : State → State
moveR ⟨ left , current , right , input , output ⟩ =
  ⟨ left , 0 , mapHead (_+_ current) right , input , output ⟩

moveRN : ℕ → State → State
moveRN n ⟨ left , current , right , input , output ⟩ =
  ⟨ left , current ∸ n , mapHead (_+_ n) right , input , output ⟩

moveRN0 : moveRN zero ≡ idfun State
moveRN0 i s =
  record s { right = mapHead-id i (right s) }

moveRNcurrent : ∀ {s} → moveRN (current s) s ≡ moveR s
moveRNcurrent {s} i =
  record (moveR s) { current = n∸n (current s) i }

+-moveRN : ∀ {m n} → moveRN m ∘ moveRN n ≡ moveRN (n + m)
+-moveRN {m} {n} i s =
  record s
    { current = eqToPath (∸-+-assoc (current s) n m) i
    ; right = lem m n i $ right s
    }
  where
    lem : ∀ m n → mapHead (_+_ m) ∘ mapHead (_+_ n) ≡ mapHead (_+_ (n + m))
    lem m n =
      mapHead-∘ ∙
      cong mapHead (funExt λ o → +-assoc m n o ∙ cong (_+ o) (+-comm m n))

decomp-moveRN : moveRN 1 ≡ focusL ∘ incr ∘ focusR ∘ decr
decomp-moveRN i s =
  record (moveRN 1 s) { right = Stream-η {xs = mapHead suc (right s)} i }

↦->+< : ∀ {cs s} → - > + < cs , s ↦∗ cs , moveRN 1 s
↦->+< {cs} {s} =
  begin
    - > + <  cs , s
  ↦∗⟨ ↦- ◅ ↦> ◅ ↦+ ◅ ↦< ◅ ε ⟩
    cs , (focusL ∘ incr ∘ focusR ∘ decr) s
  ≡ₛ⟨ sym decomp-moveRN ≡$ s ⟩
    cs , moveRN 1 s
  ∎
  where open ↦-Reasoning

↦[->+<] : ∀ {cs s} → [ - > + < □ ] cs , s ↦∗ cs , moveR s
↦[->+<] {cs} {s} =
  begin
    [ - > + < □ ] cs , s
  ↦∗⟨ loop ≤-refl ⟩
    [ - > + < □ ] cs , moveRN (current s) s
  ≡ₛ⟨ moveRNcurrent ⟩
    [ - > + < □ ] cs , moveR s
  ↦⟨ ↦[≡0] refl ⟩
    cs , moveR s
  ∎
  where
    open ↦-Reasoning

    loop :
      ∀ {cs s m} → m ≤ current s →
      [ - > + < □ ] cs , s ↦∗ [ - > + < □ ] cs , moveRN m s
    loop {cs} {s} {.zero} z≤n = from≡ₛ $ sym moveRN0 ≡$ s
    loop {cs} {s} {suc m} (s≤s m≤n) =
      begin
        [ - > + < □ ] cs , s
      ↦⟨ ↦[≢0] snotz ⟩
        - > + < [ - > + < □ ] cs , s
      ↦∗⟨ ↦->+< ⟩
        [ - > + < □ ] cs , moveRN 1 s
      ↦∗⟨ loop m≤n ⟩
        [ - > + < □ ] cs , (moveRN m ∘ moveRN 1) s
      ≡ₛ⟨ +-moveRN ≡$ s ⟩
        [ - > + < □ ] cs , moveRN (1 + m) s
      ∎

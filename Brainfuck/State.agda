{-# OPTIONS --cubical --safe --guardedness #-}

module Brainfuck.State where

open import Cubical.Codata.Stream.Base using ( Stream ) renaming ( _,_ to _∷_ )
open import Cubical.Codata.Stream.Properties using ( Stream-η )
open import Cubical.Data.Bool.Base using ( Bool→Type; not )
open import Cubical.Data.Empty.Base as ⊥ using ( ⊥ )
open import Cubical.Data.List.Base using ( List; []; _∷_; _++_; rev )
open import Cubical.Data.Nat.Base using ( ℕ; zero; suc; _+_; _∸_; isZero )
open import Cubical.Data.Nat.Properties using ( snotz; +-assoc; +-comm; n∸n )
open import Cubical.Data.Unit.Base using ( Unit; tt )
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( idfun; _∘_ )
open import Cubical.Relation.Nullary.Base using ( ¬_ )
open import Data.Char.Base as Char using ( Char )
open import Data.String.Base as String using ( String )

open Stream

open import Brainfuck.Syntax

private
  variable
    A : Type
    n : ℕ

--------------------------------------------------------------------------------
-- Misc

suc-pred : ∀ n → ¬ n ≡ 0 → suc (n ∸ 1) ≡ n
suc-pred zero p = ⊥.rec (p refl)
suc-pred (suc n) _ = refl

+-∸-assoc : ∀ m n o → m ∸ n ∸ o ≡ m ∸ (n + o)
+-∸-assoc zero zero o = refl
+-∸-assoc zero (suc n) zero = refl
+-∸-assoc zero (suc n) (suc o) = refl
+-∸-assoc (suc m) zero o = refl
+-∸-assoc (suc m) (suc n) o = +-∸-assoc m n o

Zero NonZero : ℕ → Type
Zero n = Bool→Type (isZero n)
NonZero n = Bool→Type (not (isZero n))

repeat : A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

mapHead : (A → A) → Stream A → Stream A
head (mapHead f s) = f (head s)
tail (mapHead f s) = tail s

mapHead-id : ∀ s → mapHead (idfun A) s ≡ s
head (mapHead-id s i) = head s
tail (mapHead-id s i) = tail s

--------------------------------------------------------------------------------
-- The state of the machine

record State : Type where
  constructor ⟨_,_,_,_,_⟩
  field
    left    : Stream ℕ
    current : ℕ
    right   : Stream ℕ
    input   : Stream Char
    output  : List Char

open State public

getOutput : State → String
getOutput s = String.fromList (rev (output s))

default : State
default = ⟨ repeat 0 , 0 , repeat 0 , repeat '\0' , [] ⟩

incPtr decPtr incVal decVal getCh putCh : State → State
incPtr ⟨ ls , c , rs , is , os ⟩ = ⟨ c ∷ ls , head rs , tail rs , is , os ⟩
decPtr ⟨ ls , c , rs , is , os ⟩ = ⟨ tail ls , head ls , c ∷ rs , is , os ⟩
incVal ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , suc c , rs , is , os ⟩
decVal ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , c ∸ 1 , rs , is , os ⟩
putCh ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , c , rs , is , Char.fromℕ c ∷ os ⟩
getCh ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , Char.toℕ (head is) , rs , tail is , os ⟩

decPtr∘incPtr : ∀ {s} → (decPtr ∘ incPtr) s ≡ s
decPtr∘incPtr {s} i = record s
  { right = Stream-η {xs = right s} (~ i)
  }

incPtr∘decPtr : ∀ {s} → (incPtr ∘ decPtr) s ≡ s
incPtr∘decPtr {s} i = record s
  { left = Stream-η {xs = left s} (~ i)
  }

incVal∘decVal : ∀ {s} {{_ : NonZero (current s)}} → (incVal ∘ decVal) s ≡ s
incVal∘decVal {s@record { current = suc _ }} i = record s
  { current = suc-pred (current s) snotz i
  }

moveRN : ℕ → State → State
moveR : State → State
moveRN n ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , c ∸ n , mapHead (_+_ n) rs , is , os ⟩
moveR    ⟨ ls , c , rs , is , os ⟩ = ⟨ ls , 0     , mapHead (_+_ c) rs , is , os ⟩

moveRNcurrent : ∀ {s} → moveRN (current s) s ≡ moveR s
moveRNcurrent {s} i = record (moveR s) { current = n∸n (current s) i }

moveRN0 : ∀ {s} → moveRN 0 s ≡ s
moveRN0 {s} i = record s { right = mapHead-id (right s) i }

+-moveRN : ∀ {s m n} → (moveRN m ∘ moveRN n) s ≡ moveRN (n + m) s
+-moveRN {s} {m} {n} i = record s
  { current = +-∸-assoc (current s) n m i
  ; right = lem m n i (right s)
  }
  where
    lem : ∀ m n → mapHead (_+_ m) ∘ mapHead (_+_ n) ≡ mapHead (_+_ (n + m))
    head (lem m n i s) = (+-assoc m n (head s) ∙ cong (_+ head s) (+-comm m n)) i
    tail (lem m n i s) = tail s

decomp-moveRN : ∀ {s} → moveRN 1 s ≡ (decPtr ∘ incVal ∘ incPtr ∘ decVal) s
decomp-moveRN {s} i = record (moveRN 1 s)
  { right = Stream-η {xs = mapHead suc (right s)} i
  }

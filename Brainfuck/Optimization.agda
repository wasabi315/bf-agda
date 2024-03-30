{-# OPTIONS --cubical --guardedness #-}

module Brainfuck.Optimization where

open import Cubical.Foundations.Everything hiding ( empty )
open import Cubical.Data.NatPlusOne.Base using ( ℕ₊₁; one; 1+_; 2+_; _+₁_; suc₊₁ )
open import Cubical.Data.NatPlusOne.Properties as ℕ using ( +₁-assoc )
open import Cubical.Data.List.Base using ( List; []; _∷_; _++_ )

open import Brainfuck.Syntax as Cmds
open import Brainfuck.State
open import Data.InfZipper

private
  variable
    ℓ : Level
    A B : Type ℓ

--------------------------------------------------------------------------------
-- Misc.

replicate : ℕ₊₁ → A → List A
replicate one x = x ∷ []
replicate (2+ n) x = x ∷ replicate (1+ n) x

--------------------------------------------------------------------------------

mutual

  data Opt : Type where
    `>⟨_⟩ `<⟨_⟩ `+⟨_⟩ `-⟨_⟩ : (n : ℕ₊₁) → Opt
    `· `, : Opt
    `[_] : Opts → Opt

  Opts : Type
  Opts = List Opt

pattern □ = []
pattern >⟨_⟩_ n cs = `>⟨ n ⟩ ∷ cs
pattern <⟨_⟩_ n cs = `<⟨ n ⟩ ∷ cs
pattern +⟨_⟩_ n cs = `+⟨ n ⟩ ∷ cs
pattern -⟨_⟩_ n cs = `-⟨ n ⟩ ∷ cs
pattern ·_ cs = `· ∷ cs
pattern ,_ cs = `, ∷ cs
pattern [_]_ cs cs₁ = `[ cs ] ∷ cs₁

--------------------------------------------------------------------------------
-- Optimization

mutual

  optimize : Cmds → Opts
  optimize □ = □
  optimize (> cs) with optimize cs
  ... | >⟨ n ⟩ cs' = >⟨ suc₊₁ n ⟩ cs'
  ... | cs' = >⟨ one ⟩ cs'
  optimize (< cs) with optimize cs
  ... | <⟨ n ⟩ cs' = <⟨ suc₊₁ n ⟩ cs'
  ... | cs' = <⟨ one ⟩ cs'
  optimize (+ cs) with optimize cs
  ... | +⟨ n ⟩ cs' = +⟨ suc₊₁ n ⟩ cs'
  ... | , cs' = cs' -- getCh overwrites the current cell
  ... | cs' = +⟨ one ⟩ cs'
  optimize (- cs) with optimize cs
  ... | -⟨ n ⟩ cs' = -⟨ suc₊₁ n ⟩ cs'
  ... | , cs' = cs' -- putCh overwrites the current cell
  ... | cs' = -⟨ one ⟩ cs'
  optimize (· cs) = · optimize cs
  optimize (, cs) = , optimize cs
  optimize ([ cs ] cs₁) = [ optimize cs ] optimize cs₁

helloWorld′ : Opts
helloWorld′ = optimize helloWorld

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

unoptimize : Opts → Cmds
unoptimize □ = □
unoptimize (>⟨ n ⟩ cs) = replicate n `> ++ unoptimize cs
unoptimize (<⟨ n ⟩ cs) = replicate n `< ++ unoptimize cs
unoptimize (+⟨ n ⟩ cs) = replicate n `+ ++ unoptimize cs
unoptimize (-⟨ n ⟩ cs) = replicate n `- ++ unoptimize cs
unoptimize (· cs) = · unoptimize cs
unoptimize (, cs) = , unoptimize cs
unoptimize ([ cs ] cs₁) = [ unoptimize cs ] unoptimize cs₁

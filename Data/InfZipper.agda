{-# OPTIONS --cubical #-}

module Data.InfZipper where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma using ( _×_; _,_ )

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

--------------------------------------------------------------------------------

data InfList {A : Type ℓ} (x : A) : Type ℓ where
  [] : InfList x
  _∷_ : (y : A) (xs : InfList x) → InfList x
  ext : [] ≡ x ∷ []
  trunc : isSet (InfList x)

InfZipper : {A : Type ℓ} (x : A) → Type ℓ
InfZipper x = InfList x × InfList x

pattern repeat x = [] , [] {x = x}

--------------------------------------------------------------------------------

module _ {x : A} where

  isSetInfZipper : isSet (InfZipper x)
  isSetInfZipper = isSet× trunc trunc

  extract : isSet A → InfZipper x → A
  extract AType (ls , []) = x
  extract AType (ls , y ∷ rs) = y
  extract AType (ls , ext i) = x
  extract AType (ls , trunc rs rs₁ p q i j) = AType
    (extract AType (ls , rs))
    (extract AType (ls , rs₁))
    (cong (extract AType ∘ (ls ,_)) p)
    (cong (extract AType ∘ (ls ,_)) q)
    i j

  update : (A → A) → InfZipper x → InfZipper x
  update f (ls , []) = ls , f x ∷ []
  update f (ls , y ∷ rs) = ls , f y ∷ rs
  update f (ls , ext i) = ls , f x ∷ []
  update f (ls , trunc rs rs₁ p q i j) = isSetInfZipper
    (update f (ls , rs))
    (update f (ls , rs₁))
    (cong (update f ∘ (ls ,_)) p)
    (cong (update f ∘ (ls ,_)) q)
    i j

  update-id : ∀ xs → update (idfun _) xs ≡ xs
  update-id (ls , []) = cong (ls ,_) (sym ext)
  update-id (ls , y ∷ rs) = refl
  update-id (ls , ext i) j = ls , ext (i ∨ ~ j)
  update-id (ls , trunc rs rs₁ p q i j) = isOfHLevel→isOfHLevelDep 2
    (λ xs → isProp→isSet (isSetInfZipper (update (idfun _) xs) xs))
    (update-id (ls , rs))
    (update-id (ls , rs₁))
    (cong (update-id ∘ (ls ,_)) p)
    (cong (update-id ∘ (ls ,_)) q)
    (λ i j → ls , trunc rs rs₁ p q i j)
    i j

  left right : InfZipper x → InfZipper x
  left ([] , rs) = [] , x ∷ rs
  left (y ∷ ls , rs) = ls , y ∷ rs
  left (ext i , rs) = [] , x ∷ rs
  left (trunc ls ls₁ p q i j , rs) = isSetInfZipper
    (left (ls , rs))
    (left (ls₁ , rs))
    (cong (left ∘ (_, rs)) p)
    (cong (left ∘ (_, rs)) q)
    i j
  right (ls , []) = x ∷ ls , []
  right (ls , y ∷ rs) = y ∷ ls , rs
  right (ls , ext i) = x ∷ ls , []
  right (ls , trunc rs rs₁ p q i j) = isSetInfZipper
    (right (ls , rs))
    (right (ls , rs₁))
    (cong (right ∘ (ls ,_)) p)
    (cong (right ∘ (ls ,_)) q)
    i j

  left-right : ∀ xs → right (left xs) ≡ xs
  left-right ([] , rs) = cong (_, rs) (sym ext)
  left-right (y ∷ ls , rs) = refl
  left-right (ext i , rs) j = ext (i ∨ ~ j) , rs
  left-right (trunc ls ls₁ p q i j , rs) = isOfHLevel→isOfHLevelDep 2
    (λ xs → isProp→isSet (isSetInfZipper (right (left xs)) xs))
    (left-right (ls , rs))
    (left-right (ls₁ , rs))
    (cong (left-right ∘ (_, rs)) p)
    (cong (left-right ∘ (_, rs)) q)
    (λ i j → trunc ls ls₁ p q i j , rs)
    i j

  right-left : ∀ xs → left (right xs) ≡ xs
  right-left (ls , []) = cong (ls ,_) (sym ext)
  right-left (ls , y ∷ rs) = refl
  right-left (ls , ext i) j = ls , ext (i ∨ ~ j)
  right-left (ls , trunc rs rs₁ p q i j) = isOfHLevel→isOfHLevelDep 2
    (λ xs → isProp→isSet (isSetInfZipper (left (right xs)) xs))
    (right-left (ls , rs))
    (right-left (ls , rs₁))
    (cong (right-left ∘ (ls ,_)) p)
    (cong (right-left ∘ (ls ,_)) q)
    (λ i j → ls , trunc rs rs₁ p q i j)
    i j

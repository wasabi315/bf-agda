{-# OPTIONS --cubical #-}

module Brainfuck.Syntax where

open import Cubical.Data.Empty.Base as ⊥ using ( ⊥ )
open import Cubical.Data.List.Base using ( List; []; _∷_ )
open import Cubical.Data.List.Properties using ( discreteList; ¬nil≡cons; ¬cons≡nil; cons-inj₁; cons-inj₂ )
open import Cubical.Data.Sigma.Base using ( _×_; _,_ )
open import Cubical.Data.Unit.Base using ( Unit; tt )
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Relation.Nullary.Base using ( ¬_; Dec; yes; no; Discrete )
open import Cubical.Relation.Nullary.Properties using ( mapDec; Discrete→isSet )

--------------------------------------------------------------------------------
-- Syntax

data Cmd : Type
Cmds : Type

data Cmd where
  `> `< `+ `- `· `, : Cmd
  `[_] : (cs : Cmds) → Cmd

Cmds = List Cmd

pattern □ = []
pattern >_ cs = `> ∷ cs
pattern <_ cs = `< ∷ cs
pattern +_ cs = `+ ∷ cs
pattern -_ cs = `- ∷ cs
pattern ·_ cs = `· ∷ cs
pattern ,_ cs = `, ∷ cs
pattern [_]_ cs cs' = `[ cs ] ∷ cs'

--------------------------------------------------------------------------------

private
  variable
    c : Cmd
    cs cs' : Cmds

elimCmd : ∀ {ℓ} {A : Cmd → Type ℓ}
  → (a> : A `>) (a< : A `<) (a+ : A `+) (a- : A `-) (a· : A `·) (a, : A `,) (a[] : ∀ {cs} → A `[ cs ])
  → (c : Cmd) → A c
elimCmd a> a< a+ a- a· a, a[] `> = a>
elimCmd a> a< a+ a- a· a, a[] `< = a<
elimCmd a> a< a+ a- a· a, a[] `+ = a+
elimCmd a> a< a+ a- a· a, a[] `- = a-
elimCmd a> a< a+ a- a· a, a[] `· = a·
elimCmd a> a< a+ a- a· a, a[] `, = a,
elimCmd a> a< a+ a- a· a, a[] `[ cs ] = a[]

caseCmd : ∀ {ℓ} {A : Type ℓ} (a> a< a+ a- a· a, a[] : A) → Cmd → A
caseCmd a> a< a+ a- a· a, a[] = elimCmd a> a< a+ a- a· a, a[]

¬incPtr≡decPtr : ¬ `> ≡ `<
¬incPtr≡incVal : ¬ `> ≡ `+
¬incPtr≡decVal : ¬ `> ≡ `-
¬incPtr≡putCh : ¬ `> ≡ `·
¬incPtr≡getCh : ¬ `> ≡ `,
¬incPtr≡loop : ¬ `> ≡ `[ cs ]
¬incPtr≡decPtr eq = subst (caseCmd Unit ⊥ ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬incPtr≡incVal eq = subst (caseCmd Unit ⊥ ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬incPtr≡decVal eq = subst (caseCmd Unit ⊥ ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬incPtr≡putCh eq = subst (caseCmd Unit ⊥ ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬incPtr≡getCh eq = subst (caseCmd Unit ⊥ ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬incPtr≡loop eq = subst (caseCmd Unit ⊥ ⊥ ⊥ ⊥ ⊥ ⊥) eq tt

¬decPtr≡incVal : ¬ `< ≡ `+
¬decPtr≡decVal : ¬ `< ≡ `-
¬decPtr≡putCh : ¬ `< ≡ `·
¬decPtr≡getCh : ¬ `< ≡ `,
¬decPtr≡loop : ¬ `< ≡ `[ cs ]
¬decPtr≡incVal eq = subst (caseCmd ⊥ Unit ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬decPtr≡decVal eq = subst (caseCmd ⊥ Unit ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬decPtr≡putCh eq = subst (caseCmd ⊥ Unit ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬decPtr≡getCh eq = subst (caseCmd ⊥ Unit ⊥ ⊥ ⊥ ⊥ ⊥) eq tt
¬decPtr≡loop eq = subst (caseCmd ⊥ Unit ⊥ ⊥ ⊥ ⊥ ⊥) eq tt

¬incVal≡decVal : ¬ `+ ≡ `-
¬incVal≡putCh : ¬ `+ ≡ `·
¬incVal≡getCh : ¬ `+ ≡ `,
¬incVal≡loop : ¬ `+ ≡ `[ cs ]
¬incVal≡decVal eq = subst (caseCmd ⊥ ⊥ Unit ⊥ ⊥ ⊥ ⊥) eq tt
¬incVal≡putCh eq = subst (caseCmd ⊥ ⊥ Unit ⊥ ⊥ ⊥ ⊥) eq tt
¬incVal≡getCh eq = subst (caseCmd ⊥ ⊥ Unit ⊥ ⊥ ⊥ ⊥) eq tt
¬incVal≡loop eq = subst (caseCmd ⊥ ⊥ Unit ⊥ ⊥ ⊥ ⊥) eq tt

¬decVal≡putCh : ¬ `- ≡ `·
¬decVal≡getCh : ¬ `- ≡ `,
¬decVal≡loop : ¬ `- ≡ `[ cs ]
¬decVal≡putCh eq = subst (caseCmd ⊥ ⊥ ⊥ Unit ⊥ ⊥ ⊥) eq tt
¬decVal≡getCh eq = subst (caseCmd ⊥ ⊥ ⊥ Unit ⊥ ⊥ ⊥) eq tt
¬decVal≡loop eq = subst (caseCmd ⊥ ⊥ ⊥ Unit ⊥ ⊥ ⊥) eq tt

¬putCh≡getCh : ¬ `· ≡ `,
¬putCh≡loop : ¬ `· ≡ `[ cs ]
¬putCh≡getCh eq = subst (caseCmd ⊥ ⊥ ⊥ ⊥ Unit ⊥ ⊥) eq tt
¬putCh≡loop eq = subst (caseCmd ⊥ ⊥ ⊥ ⊥ Unit ⊥ ⊥) eq tt

¬getCh≡loop : ¬ `, ≡ `[ cs ]
¬getCh≡loop eq = subst (caseCmd ⊥ ⊥ ⊥ ⊥ ⊥ Unit ⊥) eq tt

loop-injective : `[ cs ] ≡ `[ cs' ] → cs ≡ cs'
loop-injective = congS λ { `[ cs ] → cs; _ → [] }

discreteCmd : Discrete Cmd
discreteCmds : Discrete Cmds
discreteCmd `> `> = yes refl
discreteCmd `> `< = no ¬incPtr≡decPtr
discreteCmd `> `+ = no ¬incPtr≡incVal
discreteCmd `> `- = no ¬incPtr≡decVal
discreteCmd `> `· = no ¬incPtr≡putCh
discreteCmd `> `, = no ¬incPtr≡getCh
discreteCmd `> `[ _ ] = no ¬incPtr≡loop
discreteCmd `< `> = no (¬incPtr≡decPtr ∘ sym)
discreteCmd `< `< = yes refl
discreteCmd `< `+ = no ¬decPtr≡incVal
discreteCmd `< `- = no ¬decPtr≡decVal
discreteCmd `< `· = no ¬decPtr≡putCh
discreteCmd `< `, = no ¬decPtr≡getCh
discreteCmd `< `[ _ ] = no ¬decPtr≡loop
discreteCmd `+ `> = no (¬incPtr≡incVal ∘ sym)
discreteCmd `+ `< = no (¬decPtr≡incVal ∘ sym)
discreteCmd `+ `+ = yes refl
discreteCmd `+ `- = no ¬incVal≡decVal
discreteCmd `+ `· = no ¬incVal≡putCh
discreteCmd `+ `, = no ¬incVal≡getCh
discreteCmd `+ `[ _ ] = no ¬incVal≡loop
discreteCmd `- `> = no (¬incPtr≡decVal ∘ sym)
discreteCmd `- `< = no (¬decPtr≡decVal ∘ sym)
discreteCmd `- `+ = no (¬incVal≡decVal ∘ sym)
discreteCmd `- `- = yes refl
discreteCmd `- `· = no ¬decVal≡putCh
discreteCmd `- `, = no ¬decVal≡getCh
discreteCmd `- `[ _ ] = no ¬decVal≡loop
discreteCmd `· `> = no (¬incPtr≡putCh ∘ sym)
discreteCmd `· `< = no (¬decPtr≡putCh ∘ sym)
discreteCmd `· `+ = no (¬incVal≡putCh ∘ sym)
discreteCmd `· `- = no (¬decVal≡putCh ∘ sym)
discreteCmd `· `· = yes refl
discreteCmd `· `, = no ¬putCh≡getCh
discreteCmd `· `[ _ ] = no ¬putCh≡loop
discreteCmd `, `> = no (¬incPtr≡getCh ∘ sym)
discreteCmd `, `< = no (¬decPtr≡getCh ∘ sym)
discreteCmd `, `+ = no (¬incVal≡getCh ∘ sym)
discreteCmd `, `- = no (¬decVal≡getCh ∘ sym)
discreteCmd `, `· = no (¬putCh≡getCh ∘ sym)
discreteCmd `, `, = yes refl
discreteCmd `, `[ _ ] = no ¬getCh≡loop
discreteCmd `[ _ ] `> = no (¬incPtr≡loop ∘ sym)
discreteCmd `[ _ ] `< = no (¬decPtr≡loop ∘ sym)
discreteCmd `[ _ ] `+ = no (¬incVal≡loop ∘ sym)
discreteCmd `[ _ ] `- = no (¬decVal≡loop ∘ sym)
discreteCmd `[ _ ] `· = no (¬putCh≡loop ∘ sym)
discreteCmd `[ _ ] `, = no (¬getCh≡loop ∘ sym)
discreteCmd `[ cs ] `[ cs' ] =
  mapDec (congS `[_]) (λ p → p ∘ loop-injective) (discreteCmds cs cs')
-- discreteCmds = discreteList discreteCmd -- fails to terminate-check
discreteCmds [] [] = yes refl
discreteCmds [] (_ ∷ _) = no ¬nil≡cons
discreteCmds (_ ∷ _) [] = no ¬cons≡nil
discreteCmds (c ∷ cs) (c' ∷ cs') with discreteCmd c c' | discreteCmds cs cs'
... | yes p | yes q = yes (cong₂ _∷_ p q)
... | no ¬p | _     = no λ q → ¬p (cons-inj₁ q)
... | yes _ | no ¬p = no λ q → ¬p (cons-inj₂ q)

isSetCmd : isSet Cmd
isSetCmd = Discrete→isSet discreteCmd

isSetCmds : isSet Cmds
isSetCmds = Discrete→isSet discreteCmds

--------------------------------------------------------------------------------

NotLoop : Cmd → Type
NotLoop = caseCmd Unit Unit Unit Unit Unit Unit ⊥

notLoop? : ∀ c → Dec (NotLoop c)
notLoop? = elimCmd (yes tt) (yes tt) (yes tt) (yes tt) (yes tt) (yes tt) (no λ ())

NoLoops : Cmds → Type
NoLoops [] = Unit
NoLoops (c ∷ cs) = NotLoop c × NoLoops cs

noLoops? : ∀ cs → Dec (NoLoops cs)
noLoops? [] = yes tt
noLoops? (c ∷ cs) with notLoop? c | noLoops? cs
... | yes nl | yes nls = yes (nl , nls)
... | no ¬nl | _ = no λ (nl , _) → ¬nl nl
... | yes _ | no ¬nls = no λ (_ , nls) → ¬nls nls

--------------------------------------------------------------------------------

NotIO : Cmd → Type
NotIO = caseCmd Unit Unit Unit Unit ⊥ ⊥ Unit

notIO? : ∀ c → Dec (NotIO c)
notIO? = elimCmd (yes tt) (yes tt) (yes tt) (yes tt) (no λ ()) (no λ ()) (yes tt)

NoIO : Cmds → Type
NoIO [] = Unit
NoIO (c ∷ cs) = NotIO c × NoIO cs

noIO? : ∀ cs → Dec (NoIO cs)
noIO? [] = yes tt
noIO? (c ∷ cs) with notIO? c | noIO? cs
... | yes ni | yes nis = yes (ni , nis)
... | no ¬ni | _ = no λ (ni , _) → ¬ni ni
... | yes _ | no ¬nis = no λ (_ , nis) → ¬nis nis

--------------------------------------------------------------------------------

`bf_ : Cmds → Cmds
`bf cs = cs

` : Cmds
` = []

helloWorld : Cmds
helloWorld =
  `bf
    -- "H"
    + + + + +  + + + + +  + + + + +  + + + + +  + + + + +  + + + + +
    + + + + +  + + + + +  + + + + +  + + + + +  + + + + +  + + + + +
    + + + + +  + + + + +  + +
    ·
    -- "e"
    + + + + +  + + + + +  + + + + +  + + + + +  + + + + +  + + + +
    ·
    -- "ll"
    + + + + +  + +
    · ·
    -- "o"
    + + +
    ·
    -- ","
    - - - - -  - - - - -  - - - - -  - - - - -  - - - - -  - - - - -
    - - - - -  - - - - -  - - - - -  - - - - -  - - - - -  - - - - -
    - - - - -  - -
    ·
    -- " "
    - - - - -  - - - - -  - -
    ·
    -- "w"
    + + + + +  + + + + +  + + + + +  + + + + +  + + + + +  + + + + +
    + + + + +  + + + + +  + + + + +  + + + + +  + + + + +  + + + + +
    + + + + +  + + + + +  + + + + +  + + + + +  + + + + +  + +
    ·
    -- "o"
    - - - - -  - - -
    ·
    -- "r"
    + + +
    ·
    -- "l"
    - - - - -  -
    ·
    -- "d"
    - - - - -  - - -
    ·
    -- "!"
    - - - - -  - - - - -  - - - - -  - - - - -  - - - - -  - - - - -
    - - - - -  - - - - -  - - - - -  - - - - -  - - - - -  - - - - -
    - - - - -  - -
    ·
  `

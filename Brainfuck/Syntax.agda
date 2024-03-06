{-# OPTIONS --cubical --safe #-}

module Brainfuck.Syntax where

open import Cubical.Data.Empty.Base as ⊥ using ( ⊥ )
open import Cubical.Data.List.Base using ( List; []; _∷_ )
open import Cubical.Data.Sigma.Base using ( _×_; _,_ )
open import Cubical.Data.Unit.Base using ( Unit; tt )
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using ( ¬_; Dec; yes; no )

--------------------------------------------------------------------------------
-- Syntax

data Cmd : Type
Cmds : Type

data Cmd where
  `> : Cmd
  `< : Cmd
  `+ : Cmd
  `- : Cmd
  `· : Cmd
  `, : Cmd
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

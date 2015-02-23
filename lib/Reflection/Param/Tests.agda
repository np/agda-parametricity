{-# OPTIONS -vtc.unquote.decl:20 -vtc.unquote.def:20 #-}
{-# OPTIONS --without-K #-}
open import Level hiding (zero; suc)
open import Data.Unit renaming (⊤ to 𝟙; tt to 0₁)
open import Data.Bool
  using    (not)
  renaming (Bool to 𝟚; false to 0₂; true to 1₂)
open import Data.String.Core using (String)
open import Data.Float       using (Float)
open import Function
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat hiding (_≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl) renaming (_≗_ to _~_)

open import Function.Param.Unary
open import Function.Param.Binary
open import Type.Param.Unary
open import Type.Param.Binary
open import Data.Two.Param.Binary
open import Data.Nat.Param.Binary
open import Reflection.NP
open import Reflection.Param
open import Reflection.Param.Env

module Reflection.Param.Tests where

import Reflection.Printer as Pr
open Pr using (var;con;def;lam;pi;sort;unknown;showTerm;showType;showDef;showFunDef;showClauses)

-- Local "imports" to avoid depending on nplib
private
  postulate
    opaque : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
    -- opaque-rule : ∀ {x} y → opaque x y ≡ y

  ★₀ = Set₀
  ★₁ = Set₁

infixr 1 _[₀→₀]_
_[₀→₀]_ : ∀ {A : Set₀} (Aₚ : A → Set₀)
            {B : Set₀} (Bₚ : B → Set₀)
            (f : A → B) → Set₀
_[₀→₀]_ = λ {A} Aₚ {B} Bₚ f → ∀ {a} (aₚ : Aₚ a) → Bₚ (f a)

infixr 1 _[₀→₁]_
_[₀→₁]_ : ∀ {A : Set₀} (Aₚ : A → Set₀)
            {B : Set₁} (Bₚ : B → Set₁)
            (f : A → B) → Set₁
_[₀→₁]_ = λ {A} Aₚ {B} Bₚ f → ∀ {a} (aₚ : Aₚ a) → Bₚ (f a)

infixr 1 _[₁→₁]_
_[₁→₁]_ : ∀ {A : Set₁} (Aₚ : A → Set₁)
            {B : Set₁} (Bₚ : B → Set₁)
            (f : A → B) → Set₁
_[₁→₁]_ = λ {A} Aₚ {B} Bₚ f → ∀ {a} (aₚ : Aₚ a) → Bₚ (f a)

infixr 1 _[₁→₂]_
_[₁→₂]_ : ∀ {A : Set₁} (Aₚ : A → Set₁)
            {B : Set₂} (Bₚ : B → Set₂)
            (f : A → B) → Set₂
_[₁→₂]_ = λ {A} Aₚ {B} Bₚ f → ∀ {a} (aₚ : Aₚ a) → Bₚ (f a)

[[Set₀]] : ([Set₀] [₁→₂] [Set₁]) [Set₀]
[[Set₀]] = λ A → A [₀→₁] [Set₀]

{-
EqEnv = {!!}
EqRes = {!!}

eqTerm : EqEnv → Term → Term → EqRes
eqTerm Γ (var x args) (var x₁ args₁) = {!!}
eqTerm Γ (def f₀ args₀) (def f₁ args₁) = {!!}
eqTerm Γ (con c₀ args₀) (con c₁ args₁) = {!!}
eqTerm Γ (lam v t) (lam v' t') = {!!}
eqTerm Γ (pi t₁ t₂) (pi u₁ u₂) = {!!}
eqTerm Γ (sort s₀) (sort s₁) = {!!}
eqTerm Γ (lit l₀) (lit l₁) = {!!}
eqTerm Γ unknown unknown = {!!}
eqTerm Γ (def f args) u = {!!}
--eqTerm Γ (pat-lam cs args) u = {!!}
eqTerm _ _ = ?
-}

{-
import Reflection.Simple as Si
open Si using (var;con;def;lam;pi;sort;unknown;simple;showTerm)
-}

_≡-no-hints_ : Term → Term → Set
t ≡-no-hints u = noHintsTerm t ≡ noHintsTerm u

_≡-def-no-hints_ : Definition → Definition → Set
t ≡-def-no-hints u = noHintsDefinition t ≡ noHintsDefinition u

p[Set₀]-type = param-type-by-name (ε 1) (quote [Set₀])
p[Set₀] = param-clauses-by-name (ε 1) (quote [Set₀])
q[[Set₀]] = definition (quote [[Set₀]]) -- quoteTerm [[Set₀]]
test-type-p[Set₀] : ([Set₀] [₁→₂] [Set₁]) [Set₀] ≡ unquote (unEl p[Set₀]-type)
test-type-p[Set₀] = refl
test-term-p[Set₀] : quoteTerm [[Set₀]] ≡-no-hints Get-term.from-clauses p[Set₀]
test-term-p[Set₀] = refl
u-p[Set₀] : ([Set₀] [₁→₂] [Set₁]) [Set₀]
unquoteDef u-p[Set₀] = p[Set₀]

False : Set₁
False = (A : Set) → A

param1-False-type = param-type-by-name (ε 1) (quote False)
param1-False-term = param-term-by-name (ε 1) (quote False)

param1-False-type-check : [Set₁] False ≡ unquote (unEl param1-False-type)
param1-False-type-check = refl

[False] : unquote (unEl param1-False-type)
[False] = unquote param1-False-term

[Level] : [Set₀] Level
[Level] _ = 𝟙

[String] : [Set₀] String
[String] _ = 𝟙

[Float] : [Set₀] Float
[Float] _ = 𝟙

-- Levels are parametric, hence the relation is total
⟦Level⟧ : ⟦Set₀⟧ Level Level
⟦Level⟧ _ _ = 𝟙

⟦String⟧ : ⟦Set₀⟧ String String
⟦String⟧ = _≡_

⟦Float⟧ : ⟦Set₀⟧ Float Float
⟦Float⟧ = _≡_

data [𝟚] : [Set₀] 𝟚 where
  [0₂] : [𝟚] 0₂
  [1₂] : [𝟚] 1₂

data [ℕ] : [Set₀] ℕ where
  [zero] : [ℕ] zero
  [suc]  : ([ℕ] [→] [ℕ]) suc

[pred] : ([ℕ] [→] [ℕ]) pred
[pred] [zero]     = [zero]
[pred] ([suc] xₚ) = xₚ

defDefEnv1 : Name → Name
defDefEnv1 (quote 𝟚)      = quote [𝟚]
defDefEnv1 (quote ℕ)      = quote [ℕ]
defDefEnv1 (quote String) = quote [String]
defDefEnv1 (quote Float)  = quote [Float]
defDefEnv1 (quote ★₀)     = quote [Set₀]
defDefEnv1 (quote ★₁)     = quote [Set₁]
defDefEnv1 (quote False)  = quote [False]
defDefEnv1 (quote Level)  = quote [Level]
defDefEnv1 n              = opaque "defDefEnv1" n

defConEnv1 : Name → Name
defConEnv1 (quote 0₂)         = quote [0₂]
defConEnv1 (quote 1₂)         = quote [1₂]
defConEnv1 (quote ℕ.zero)     = quote [zero]
defConEnv1 (quote ℕ.suc)      = quote [suc]
defConEnv1 (quote Level.zero) = quote 0₁
defConEnv1 (quote Level.suc)  = quote 0₁
defConEnv1 n                  = opaque "defConEnv1" n

defDefEnv2 : Name → Name
defDefEnv2 (quote 𝟚)      = quote ⟦𝟚⟧
defDefEnv2 (quote ℕ)      = quote ⟦ℕ⟧
defDefEnv2 (quote ★₀)     = quote ⟦Set₀⟧
defDefEnv2 (quote ★₁)     = quote ⟦Set₁⟧
defDefEnv2 (quote String) = quote ⟦String⟧
defDefEnv2 (quote Float)  = quote ⟦Float⟧
defDefEnv2 (quote Level)  = quote ⟦Level⟧
defDefEnv2 n              = opaque "defDefEnv" n

defConEnv2 : Name → Name
defConEnv2 (quote 0₂)         = quote ⟦0₂⟧
defConEnv2 (quote 1₂)         = quote ⟦1₂⟧
defConEnv2 (quote ℕ.zero)     = quote ⟦ℕ⟧.⟦zero⟧
defConEnv2 (quote ℕ.suc)      = quote ⟦ℕ⟧.⟦suc⟧
defConEnv2 (quote Level.zero) = quote 0₁
defConEnv2 (quote Level.suc)  = quote 0₁
defConEnv2 n                  = opaque "defConEnv2" n

defEnv0 : Env' 0
defEnv0 = record (ε 0)
                 { pConT = con
                 ; pConP = con
                 ; pDef  = id }

defEnv1 : Env' 1
defEnv1 = record (ε 1)
  { pConP = con ∘′ defConEnv1
  ; pConT = con ∘′ defConEnv1
  ; pDef = defDefEnv1 }

defEnv2 : Env' 2
defEnv2 = record (ε 2)
  { pConP = con ∘′ defConEnv2
  ; pConT = con ∘′ defConEnv2
  ; pDef = defDefEnv2 }

param1-[False]-type = param-type-by-name defEnv1 (quote [False])
param1-[False]-term = param-term-by-name defEnv1 (quote [False])

{-
module Const where
  postulate
    A  : Set₀
    Aᵣ : A → A → Set₀
  data Wrapper : Set where
    wrap : A → Wrapper

  idWrapper : Wrapper → Wrapper
  idWrapper (wrap x) = wrap x

  data ⟦Wrapper⟧ : Wrapper → Wrapper → Set₀ where
    ⟦wrap⟧ : (Aᵣ ⟦→⟧ ⟦Wrapper⟧) wrap wrap

  wrapperEnv = record (ε 2)
   { pDef = [ quote Wrapper       ≔ quote ⟦Wrapper⟧  ] id
   ; pConP = [ quote Wrapper.wrap ≔ con (quote ⟦Wrapper⟧.⟦wrap⟧) ] con
   ; pConT = [ quote Wrapper.wrap ≔ con (quote ⟦Wrapper⟧.⟦wrap⟧) ] con
   }

  unquoteDecl ⟦idWrapper⟧ = param-rec-def-by-name wrapperEnv (quote idWrapper) ⟦idWrapper⟧
-}

data Wrapper (A : Set₀) : Set₀ where
  wrap : A → Wrapper A

idWrapper : ∀ {A} → Wrapper A → Wrapper A
idWrapper (wrap x) = wrap x

data [Wrapper] {A : Set} (Aₚ : A → Set₀)
   : Wrapper A → Set₀ where
  [wrap] : (Aₚ [→] [Wrapper] Aₚ) wrap

[Wrapper]-env = record (ε 1)
  { pDef = [ quote Wrapper ≔ quote [Wrapper] ] id
  ; pConP = [ quote wrap ≔ con (quote [wrap])  ] con
  ; pConT = [ quote wrap ≔ conSkip' 2 (quote [wrap]) ] con
  }

unquoteDecl [idWrapper] =
  param-rec-def-by-name [Wrapper]-env (quote idWrapper) [idWrapper]

  {-
[idWrapper] = {!  param-rec-def-by-name [Wrapper]-env (quote idWrapper) [idWrapper]!}
-- [idWrapper] = {!  param-rec-def-by-name [Wrapper]-env (quote idWrapper) [idWrapper]!}
-}

{-
-- The generated type bigger since it is a familly for no reason.
data ⟦Wrapper⟧ : (⟦Set₀⟧ ⟦→⟧ ⟦Set₁⟧) Wrapper Wrapper

private
  ⟦Wrapper⟧-ctor = λ c → unEl (param-ctor-by-name (extDefEnv [ quote Wrapper ≔ quote ⟦Wrapper⟧ ] (ε 2)) c)

data ⟦Wrapper⟧ where
  ⟦wrap⟧ : unquote (⟦Wrapper⟧-ctor (quote Wrapper.wrap))
-}
data ⟦Wrapper⟧ {A₀ A₁ : Set} (Aᵣ : A₀ → A₁ → Set₀)
   : Wrapper A₀ → Wrapper A₁ → Set₀ where
  ⟦wrap⟧ : (Aᵣ ⟦→⟧ ⟦Wrapper⟧ Aᵣ) wrap wrap

⟦Wrapper⟧-env = record (ε 2)
  { pDef = [ quote Wrapper ≔ quote ⟦Wrapper⟧ ] id
  ; pConP = [ quote wrap ≔ con (quote ⟦wrap⟧)  ] con
  ; pConT = [ quote wrap ≔ conSkip' 3 (quote ⟦wrap⟧) ] con
  }

⟦idWrapper⟧1 : (∀⟨ A ∶ ⟦Set₀⟧ ⟩⟦→⟧ ⟦Wrapper⟧ A ⟦→⟧ ⟦Wrapper⟧ A) idWrapper idWrapper
⟦idWrapper⟧1 {x0} {x1} (x2) {._} {._} (⟦wrap⟧ {x3} {x4} x5)
  = ⟦wrap⟧ {_} {_} {_} {x3} {x4} x5

⟦idWrapper⟧-clauses =
  clause
  (arg (arg-info hidden  relevant) (var "A0") ∷
   arg (arg-info hidden  relevant) (var "A1") ∷
   arg (arg-info visible relevant) (var "Ar") ∷
   arg (arg-info hidden  relevant) dot ∷
   arg (arg-info hidden  relevant) dot ∷
   arg (arg-info visible relevant)
   (con (quote ⟦wrap⟧)
    (arg (arg-info hidden  relevant) (var "x0") ∷
     arg (arg-info hidden  relevant) (var "x1") ∷
     arg (arg-info visible relevant) (var "xr") ∷ []))
   ∷ [])
  (con (quote ⟦wrap⟧)
   (arg (arg-info hidden relevant) unknown ∷
    arg (arg-info hidden relevant) unknown ∷
    arg (arg-info hidden relevant) unknown ∷
    arg (arg-info hidden relevant)  (var 2 []) ∷
    arg (arg-info hidden relevant)  (var 1 []) ∷
    arg (arg-info visible relevant) (var 0 []) ∷ []))
  ∷ []

⟦idWrapper⟧2 : (∀⟨ A ∶ ⟦Set₀⟧ ⟩⟦→⟧ ⟦Wrapper⟧ A ⟦→⟧ ⟦Wrapper⟧ A) idWrapper idWrapper
unquoteDef ⟦idWrapper⟧2 = ⟦idWrapper⟧-clauses

unquoteDecl ⟦idWrapper⟧ =
  param-rec-def-by-name ⟦Wrapper⟧-env (quote idWrapper) ⟦idWrapper⟧

data Bot (A : Set₀) : Set₀ where
  bot : Bot A → Bot A

gobot : ∀ {A} → Bot A → A
gobot (bot x) = gobot x

data [Bot] {A : Set} (Aₚ : A → Set₀)
   : Bot A → Set₀ where
  [bot] : ([Bot] Aₚ [→] [Bot] Aₚ) bot

[Bot]-env = record (ε 1)
  { pDef = [ quote Bot ≔ quote [Bot] ] id
  ; pConP = [ quote bot ≔ con (quote [bot])  ] con
  ; pConT = [ quote bot ≔ conSkip' 2 (quote [bot]) ] con
  }

[gobot]' : (∀⟨ A ∶ [Set₀] ⟩[→] [Bot] A [→] A) gobot
[gobot]' {x0} (x1) {._} ([bot] {x2} x3)
  = [gobot]' {x0} x1 {x2} x3

-- [gobot]' = {!showClauses "[gobot]'" (param-rec-clauses-by-name [Bot]-env (quote gobot) (quote [gobot]'))!}

[gobot]2 : (∀⟨ A ∶ [Set₀] ⟩[→] [Bot] A [→] A) gobot

[gobot]2-clauses =
  clause
    (arg (arg-info hidden  relevant) (var "Aᵢ0") ∷
     arg (arg-info visible relevant) (var "Aᵣ") ∷
     arg (arg-info hidden  relevant) dot ∷
     arg (arg-info visible relevant)
     (con (quote [bot])
      (arg (arg-info hidden  relevant) (var "xᵢ0") ∷
       arg (arg-info visible relevant) (var "xᵣ") ∷ []))
     ∷ [])
    (def (quote [gobot]2)
     (arg (arg-info hidden  relevant) (var 4 []) ∷
      arg (arg-info visible relevant) (var 3 []) ∷
      arg (arg-info hidden  relevant) (var 1 []) ∷
      arg (arg-info visible relevant) (var 0 []) ∷ []))
    ∷ []

unquoteDef [gobot]2 = [gobot]2-clauses

unquoteDecl [gobot] =
  param-rec-def-by-name [Bot]-env (quote gobot) [gobot]

data ⟦Bot⟧ {A₀ A₁ : Set} (Aᵣ : A₀ → A₁ → Set₀)
   : Bot A₀ → Bot A₁ → Set₀ where
  ⟦bot⟧ : (⟦Bot⟧ Aᵣ ⟦→⟧ ⟦Bot⟧ Aᵣ) bot bot

⟦Bot⟧-env = record (ε 2)
  { pDef = [ quote Bot ≔ quote ⟦Bot⟧ ] id
  ; pConP = [ quote bot ≔ con (quote ⟦bot⟧)  ] con
  ; pConT = [ quote bot ≔ conSkip' 3 (quote ⟦bot⟧) ] con
  }

⟦gobot⟧1 : (∀⟨ A ∶ ⟦Set₀⟧ ⟩⟦→⟧ ⟦Bot⟧ A ⟦→⟧ A) gobot gobot
⟦gobot⟧1 {x0} {x1} x2 {._} {._} (⟦bot⟧ {x3} {x4} x5)
  = ⟦gobot⟧1 {x0} {x1} x2 {x3} {x4} x5

unquoteDecl ⟦gobot⟧ =
  param-rec-def-by-name ⟦Bot⟧-env (quote gobot) ⟦gobot⟧

id₀ : {A : Set₀} → A → A
id₀ x = x

⟦id₀⟧ : (∀⟨ A ∶ ⟦Set₀⟧ ⟩⟦→⟧ A ⟦→⟧ A) id₀ id₀
⟦id₀⟧ = λ {x₁} {x₂} xᵣ {x₃} {x₄} xᵣ₁ → xᵣ₁

data List₀ (A : Set) : Set where
  []  : List₀ A
  _∷_ : A → List₀ A → List₀ A

map₀ : ∀ {A B} (f : A → B) (xs : List₀ A) → List₀ B
map₀ f []       = []
map₀ f (x ∷ xs) = f x ∷ map₀ f xs

idList₀ : ∀ {A} → List₀ A → List₀ A
-- idList₀ : List₀ ℕ → List₀ ℕ
idList₀ []       = []
idList₀ {A} (x ∷ xs) = idList₀ {A} xs

data ⟦List₀⟧ {A₀ A₁ : Set} (Aᵣ : A₀ → A₁ → Set₀) : List₀ A₀ → List₀ A₁ → Set₀ where
  ⟦[]⟧  : ⟦List₀⟧ Aᵣ [] []
  _⟦∷⟧_ : (Aᵣ ⟦→⟧ ⟦List₀⟧ Aᵣ ⟦→⟧ ⟦List₀⟧ Aᵣ) _∷_ _∷_

con⟦List₀⟧ = conSkip' 3
⟦List₀⟧-env = record (ε 2)
  { pDef = [ quote List₀ ≔ quote ⟦List₀⟧ ] id
  ; pConP = [ quote List₀.[]  ≔ con (quote ⟦List₀⟧.⟦[]⟧)  ]
           ([ quote List₀._∷_ ≔ con (quote ⟦List₀⟧._⟦∷⟧_) ]
            con)
  ; pConT = [ quote List₀.[]  ≔ con⟦List₀⟧ (quote ⟦List₀⟧.⟦[]⟧)  ]
           ([ quote List₀._∷_ ≔ con⟦List₀⟧ (quote ⟦List₀⟧._⟦∷⟧_) ]
            con)
  }

⟦idList₀⟧ : unquote (unEl (param-type-by-name ⟦List₀⟧-env (quote idList₀)))
-- ⟦idList₀⟧ : (∀⟨ A ∶ ⟦Set₀⟧ ⟩⟦→⟧ ⟦List₀⟧ A ⟦→⟧ ⟦List₀⟧ A) idList₀ idList₀
unquoteDef ⟦idList₀⟧ = param-rec-clauses-by-name ⟦List₀⟧-env (quote idList₀) (quote ⟦idList₀⟧)

{-
⟦map₀⟧ : {x0 : Set0} → {x1 : Set0} → (x2 : (x2 : x0) → (x3 : x1) → Set0) → {x3 : Set0} → {x4 : Set0} → (x5 : (x5 : x3) → (x6 : x4) → Set0) → {x6 : (x6 : x0) → x3} → {x7 : (x7 : x1) → x4} → (x8 : {x8 : x0} → {x9 : x1} → (x10 : x2 (x8) (x9)) → x5 (x6 (x8)) (x7 (x9))) → {x9 : List₀ (x0)} → {x10 : List₀ (x1)} → (x11 : ⟦List₀⟧ {x0} {x1} (x2) (x9) (x10)) → ⟦List₀⟧ {x3} {x4} (x5) (map₀ {x0} {x3} (x6) (x9)) (map₀ {x1} {x4} (x7) (x10))
⟦map₀⟧ {x0} {x1} (x2) {x3} {x4} (x5) {x6} {x7} (x8) {._} {._} (⟦[]⟧ )  = ⟦[]⟧
⟦map₀⟧ {x0} {x1} (x2) {x3} {x4} (x5) {x6} {x7} (x8) {._} {._} (_⟦∷⟧_ {x11} {x12} (x13) {x14} {x15} (x16) )  = _⟦∷⟧_ {x6 (x11)} {x7 (x12)} (x8 {x11} {x12} (x13)) {map₀ {x0} {x3} (x6) (x14)} {map₀ {x1} {x4} (x7) (x15)} (⟦map₀⟧ {x0} {x1} (x2) {x3} {x4} (x5) {x6} {x7} (x8) {x14} {x15} (x16))
-}

unquoteDecl ⟦map₀⟧
 = param-rec-def-by-name ⟦List₀⟧-env (quote map₀) ⟦map₀⟧

{-
map-nat : ∀ (f : ∀ {X} → List₀ X → List₀ X)
            {A B : Set} (g : A → B)
          → f ∘ map₀ g ~ map₀ g ∘ f
map-nat f g x = {!⟦map₀⟧ _≡_ _≡_ {g}!}

  -- The generated type is bigger since it is a familly for no reason.
  data ⟦List₀⟧ : (⟦Set₀⟧ ⟦→⟧ ⟦Set₁⟧) List₀ List₀

  private
    ⟦List₀⟧-ctor = λ c → unEl (param-ctor-by-name (extDefEnv [ quote List₀ ≔ quote ⟦List₀⟧ ] (ε 2)) c)

  data ⟦List₀⟧ where
    ⟦[]⟧  : unquote (⟦List₀⟧-ctor (quote List₀.[]))
    _⟦∷⟧_ : unquote (⟦List₀⟧-ctor (quote List₀._∷_))

  ⟦List₀⟧-env = extConEnv ([ quote List₀.[]  ≔ quote ⟦List₀⟧.⟦[]⟧  ] ∘
                        [ quote List₀._∷_ ≔ quote ⟦List₀⟧._⟦∷⟧_ ])
             (extDefEnv [ quote List₀ ≔ quote ⟦List₀⟧ ] (ε 2))
-}

data Maybe' (A : Set) : Set₁ where
  nothing : Maybe' A
  just    : A → Maybe' A

{-
-- Set₁ is here because ⟦List₀⟧ is not using parameters, hence gets bigger.
-- This only happens without-K given the new rules for data types.
data List₀ : (A : Set) → Set₁ where
  []  : ∀ {A} → List₀ A
  _∷_ : ∀ {A} → A → List₀ A → List₀ A

map₀ : ∀ {A B} → (A → B) → List₀ A → List₀ B
map₀ f []       = []
map₀ f (x ∷ xs) = f x ∷ map₀ f xs

idList₀ : ∀ {A} → List₀ A → List₀ A
idList₀ []       = []
idList₀ (x ∷ xs) = x ∷ idList₀ xs

-- The generated type bigger since it is a familly for no reason.
data ⟦List₀⟧ : (⟦Set₀⟧ ⟦→⟧ ⟦Set₁⟧) List₀ List₀

private
  ⟦List₀⟧-ctor = λ c → unEl (param-ctor-by-name (extDefEnv [ quote List₀ ≔ quote ⟦List₀⟧ ] (ε 2)) c)

data ⟦List₀⟧ where
  ⟦[]⟧  : unquote (⟦List₀⟧-ctor (quote List₀.[]))
  _⟦∷⟧_ : unquote (⟦List₀⟧-ctor (quote List₀._∷_))

⟦List₀⟧-env = extConEnv ([ quote List₀.[]  ≔ quote ⟦List₀⟧.⟦[]⟧  ] ∘
                      [ quote List₀._∷_ ≔ quote ⟦List₀⟧._⟦∷⟧_ ])
           (extDefEnv [ quote List₀ ≔ quote ⟦List₀⟧ ] (ε 2))

-- test = ⟦[]⟧ {{!showType (type (quote List₀.[]))!}} {{!!}} {!!}
-}

{-
⟦idList₀⟧ : unquote (unEl (param-type-by-name ⟦List₀⟧-env (quote idList₀)))
unquoteDef ⟦idList₀⟧ = param-rec-clauses-by-name ⟦List₀⟧-env (quote idList₀) (quote ⟦idList₀⟧)
-}

{-
⟦map₀⟧ : unquote (unEl (param-type-by-name ⟦List₀⟧-env (quote map₀)))
⟦map₀⟧ {x} {x₁} {x₂} {x₃} {x₄} {x₅} {x₆} {x₇} x₈ {[]} {[]} ⟦[]⟧
  = ⟦[]⟧
⟦map₀⟧ {x} {x₁} {x₂} {x₃} {x₄} {x₅} {x₆} {x₇} x₈ {._ ∷ ._}
  {._ ∷ ._}
  (_⟦∷⟧_ {x₁₃} {x₁₄} x₁₅ {x₁₆} {x₁₇} x₁₈)
  = _⟦∷⟧_ {x₁₀ x₁₃} {x₁₁ x₁₄} (x₁₂ {x₁₃} {x₁₄} x₁₅)
    {map₀ {x₄} {x₇} x₁₀ x₁₆} {map₀ {x₅} {x₈} x₁₁ x₁₇}
    (⟦map₀⟧ {x₄} {x₅} {x₆} {x₇} {x₈} {x₉} {x₁₀} {x₁₁} x₁₂ {x₁₆} {x₁₇}
     x₁₈)
-}

{-
unquoteDef ⟦map₀⟧ = param-rec-clauses-by-name ⟦List₀⟧-env (quote map₀) (quote ⟦map₀⟧)
-}


{-
foo : {x0 : Set0} → {x1 : Set0} → (x2 : (x2 : x0) → (x3 : x1) → Set0) → {x3 : Set0} → {x4 : Set0} → (x5 : (x5 : x3) → (x6 : x4) → Set0) → {x6 : (x6 : x0) → x3} → {x7 : (x7 : x1) → x4} → (x8 : {x8 : x0} → {x9 : x1} → (x10 : x2 (x8) (x9)) → x5 (x6 (x8)) (x7 (x9))) → {x9 : Reflection.Param.List₀ (x0)} → {x10 : Reflection.Param.List₀ (x1)} → (x11 : Reflection.Param.⟦List₀⟧ {x0} {x1} (x2) (x9) (x10)) → Reflection.Param.⟦List₀⟧ {x3} {x4} (x5) (Reflection.Param.map₀ {x0} {x3} (x6) (x9)) (Reflection.Param.map₀ {x1} {x4} (x7) (x10))
foo {A} {A} (A) {B} {B} (B) {f} {f} (f) {._} {._} (Reflection.Param.⟦List₀⟧.⟦[]⟧ )  = Reflection.Param.⟦List₀⟧.⟦[]⟧
foo {A} {A} (A) {B} {B} (B) {f} {f} (f) {._} {._} (Reflection.Param.⟦List₀⟧._⟦∷⟧_ {x} {x} (x) {xs} {xs} (xs) )  = Reflection.Param.⟦List₀⟧._⟦∷⟧_ {x0 (x0)} {x0 (x0)} (x0 {x0} {x0} (x0)) {Reflection.Param.map₀ {x0} {x0} (x0) (x0)} {Reflection.Param.map₀ {x0} {x0} (x0) (x0)} (Reflection.Param.test' {x0} {x0} (x0) {x0} {x0} (x0) {x0} {x0} (x0) {x0} {x0} (x0))
-}

-- test' = {! showFunDef "foo" (param-rec-def-by-name ⟦List₀⟧-env (quote map₀) (quote test'))!}

open import Function.Param.Unary

revealed-[→] = Reveal-args.nåme (quote _[₀→₀]_)

revealed-[→]' : ∀ (A : Set₀) (Aₚ : A → Set₀)
                  (B : Set₀) (Bₚ : B → Set₀)
                  (f : A → B) → Set₀
unquoteDef revealed-[→]' = Get-clauses.from-def revealed-[→]

revelator-[→] : ({A : Set} (Aₚ : A → Set) {B : Set} (Bₚ : B → Set) (f : A → B) → Set)
              →  (A : Set) (Aₚ : A → Set) (B : Set) (Bₚ : B → Set) (f : A → B) → Set
unquoteDef revelator-[→] = Revelator.clauses (type (quote _[₀→₀]_))

p-[→]-type = param-type-by-name    (ε 1) (quote _[₀→₀]_)
p-[→]      = param-clauses-by-name (ε 1) (quote _[₀→₀]_)

p-[→]' = ∀ {A : Set₀}       (A₀ₚ : A → Set₀)
           {Aₚ : A → Set₀}  (A₁ₚ : {x : A} → A₀ₚ x → Aₚ x → Set₀)
           {B : Set₀}       (B₀ₚ : B → Set₀)
           {Bₚ : B → Set₀}  (B₁ₚ : {x : B} → B₀ₚ x → Bₚ x → Set₀)
           {f : A → B}      (fₚ : {x : A} → A₀ₚ x → B₀ₚ (f x))
         → (Aₚ [₀→₀] Bₚ) f
         → Set

p-[→]'-test : p-[→]' ≡ unquote (unEl p-[→]-type)
p-[→]'-test = refl

[[→]] : unquote (unEl p-[→]-type)
unquoteDef [[→]] = p-[→]

data [[ℕ]] : [[Set₀]] [ℕ] [ℕ] where
  [[zero]] : [[ℕ]] [zero] [zero]
  [[suc]]  : [[→]] [ℕ] [[ℕ]] [ℕ] [[ℕ]] [suc] [suc]

_/2 : ℕ → ℕ
zero        /2 = zero
suc zero    /2 = zero
suc (suc n) /2 = suc (n /2)

_⟦/2⟧ : (⟦ℕ⟧ ⟦₀→₀⟧ ⟦ℕ⟧) _/2 _/2
⟦zero⟧          ⟦/2⟧ = ⟦zero⟧
⟦suc⟧ ⟦zero⟧    ⟦/2⟧ = ⟦zero⟧
⟦suc⟧ (⟦suc⟧ n) ⟦/2⟧ = ⟦suc⟧ (n ⟦/2⟧)

_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

pred' : ℕ → ℕ
pred' = λ { zero    → zero
          ; (suc m) → m }

⟦pred'⟧ : (⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧) pred' pred'
unquoteDef ⟦pred'⟧ = param-clauses-by-name defEnv2 (quote pred')

_⟦+ℕ⟧_ : (⟦ℕ⟧ ⟦₀→₀⟧ ⟦ℕ⟧ ⟦₀→₀⟧ ⟦ℕ⟧) _+ℕ_ _+ℕ_
⟦zero⟧  ⟦+ℕ⟧ n = n
⟦suc⟧ m ⟦+ℕ⟧ n = ⟦suc⟧ (m ⟦+ℕ⟧ n)

⟦⟦Set₀⟧⟧ : (⟦Set₀⟧ ⟦₁→₂⟧ ⟦Set₀⟧ ⟦₁→₂⟧ ⟦Set₁⟧) ⟦Set₀⟧ ⟦Set₀⟧
⟦⟦Set₀⟧⟧ = λ A₀ A₁ → A₀ ⟦₀→₁⟧ A₁ ⟦₀→₁⟧ ⟦Set₀⟧

⟦⟦Set₀⟧⟧' : {x₁ x₂ : Set} (xᵣ : x₁ → x₂ → Set) {x₃ : Set} {x₄ : Set}
            (xᵣ₁ : x₃ → x₄ → Set) →
            (x₁ → x₃ → Set) → (x₂ → x₄ → Set) → Set₁
⟦⟦Set₀⟧⟧' = λ A₀ A₁ f₁ f₂ →
  ∀ {x₁} {x₂} (xᵣ : A₀ x₁ x₂)
    {x₃} {x₄} (xᵣ₁ : A₁ x₃ x₄) →
    f₁ x₁ x₃ → f₂ x₂ x₄ → Set

-- Since quoteTerm normalises
test-⟦⟦Set₀⟧⟧ : quoteTerm ⟦⟦Set₀⟧⟧ ≡-no-hints quoteTerm ⟦⟦Set₀⟧⟧'
test-⟦⟦Set₀⟧⟧ = refl

⟦⟦Set₀⟧⟧-type = unquote (unEl (type (quote ⟦⟦Set₀⟧⟧)))
test-⟦⟦Set₀⟧⟧-type : ⟦⟦Set₀⟧⟧-type ≡ unquote (unEl (type (quote ⟦⟦Set₀⟧⟧')))
test-⟦⟦Set₀⟧⟧-type = refl

pSet₀ = pTerm defEnv2 `★₀
ppSet₀ = pTerm defEnv2 pSet₀
p⟦Set₀⟧ = param-clauses-by-name defEnv2 (quote ⟦Set₀⟧)
test-pSet₀ : pSet₀ ≡-no-hints quoteTerm ⟦Set₀⟧
test-pSet₀ = refl
test-ppSet₀ : ppSet₀ ≡-no-hints quoteTerm ⟦⟦Set₀⟧⟧
test-ppSet₀ = refl
test-ppSet₀'' : ppSet₀ ≡-no-hints Get-term.from-clauses p⟦Set₀⟧
test-ppSet₀'' = refl

⟦⟦Set₀⟧⟧'' : (⟦Set₀⟧ ⟦₁→₂⟧ ⟦Set₀⟧ ⟦₁→₂⟧ ⟦Set₁⟧) ⟦Set₀⟧ ⟦Set₀⟧
unquoteDef ⟦⟦Set₀⟧⟧'' = p⟦Set₀⟧

test-⟦⟦Set₀⟧⟧'' : _≡_ {A = ⟦⟦Set₀⟧⟧-type} ⟦⟦Set₀⟧⟧'' ⟦⟦Set₀⟧⟧
test-⟦⟦Set₀⟧⟧'' = refl

test-p0-⟦Set₀⟧ : pTerm defEnv0 (quoteTerm ⟦Set₀⟧) ≡-no-hints quoteTerm ⟦Set₀⟧
test-p0-⟦Set₀⟧ = refl

data ⟦⟦𝟚⟧⟧ : (⟦⟦Set₀⟧⟧ ⟦𝟚⟧ ⟦𝟚⟧) ⟦𝟚⟧ ⟦𝟚⟧ where
  ⟦⟦0₂⟧⟧ : ⟦⟦𝟚⟧⟧ ⟦0₂⟧ ⟦0₂⟧ ⟦0₂⟧ ⟦0₂⟧
  ⟦⟦1₂⟧⟧ : ⟦⟦𝟚⟧⟧ ⟦1₂⟧ ⟦1₂⟧ ⟦1₂⟧ ⟦1₂⟧

p1ℕ→ℕ = pTerm defEnv1 (quoteTerm (ℕ → ℕ))
[ℕ→ℕ] = [ℕ] [→] [ℕ]
test-p1ℕ→ℕ : unquote p1ℕ→ℕ ≡ [ℕ→ℕ]
test-p1ℕ→ℕ = refl

p2ℕ→ℕ = pTerm defEnv2 (quoteTerm (ℕ → ℕ))
⟦ℕ→ℕ⟧ = ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧
test-p2ℕ→ℕ : unquote p2ℕ→ℕ ≡ ⟦ℕ→ℕ⟧
test-p2ℕ→ℕ = refl

pℕ→ℕ→ℕ = pTerm defEnv2 (quoteTerm (ℕ → ℕ → ℕ))
⟦ℕ→ℕ→ℕ⟧ = ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧
test-pℕ→ℕ→ℕ : pℕ→ℕ→ℕ ≡-no-hints quoteTerm ⟦ℕ→ℕ→ℕ⟧
test-pℕ→ℕ→ℕ = refl
ZERO : Set₁
ZERO = (A : Set₀) → A
⟦ZERO⟧ : ZERO → ZERO → Set₁
⟦ZERO⟧ f₀ f₁ =
  {A₀ A₁ : Set₀} (Aᵣ : A₀ → A₁ → Set₀)
  → Aᵣ (f₀ A₀) (f₁ A₁)
pZERO = pTerm (ε 2) (quoteTerm ZERO)
q⟦ZERO⟧ = quoteTerm ⟦ZERO⟧
test-pZERO : pZERO ≡-no-hints q⟦ZERO⟧
test-pZERO = refl
ID : Set₁
ID = (A : Set₀) → A → A
⟦ID⟧ : ID → ID → Set₁
⟦ID⟧ f₀ f₁ =
  {A₀ A₁ : Set₀} (Aᵣ : A₀ → A₁ → Set₀)
  {x₀ : A₀} {x₁ : A₁} (x : Aᵣ x₀ x₁)
  → Aᵣ (f₀ A₀ x₀) (f₁ A₁ x₁)
pID = pTerm (ε 2) (quoteTerm ID)
q⟦ID⟧ = quoteTerm ⟦ID⟧
test-ID : q⟦ID⟧ ≡-no-hints pID
test-ID = refl

⟦not⟧' : (⟦𝟚⟧ ⟦→⟧ ⟦𝟚⟧) not not
unquoteDef ⟦not⟧' = param-clauses-by-name defEnv2 (quote not)
test-not : ∀ {x₀ x₁ : 𝟚} (xᵣ : ⟦𝟚⟧ x₀ x₁) → ⟦not⟧ xᵣ ≡ ⟦not⟧' xᵣ
test-not ⟦0₂⟧ = refl
test-not ⟦1₂⟧ = refl

[pred]' : ([ℕ] [→] [ℕ]) pred
unquoteDef [pred]' = param-clauses-by-name defEnv1 (quote pred)

test-p1-pred : ∀ {n} (nₚ : [ℕ] n) → [pred]' nₚ ≡ [pred] nₚ
test-p1-pred [zero]     = refl
test-p1-pred ([suc] nₚ) = refl

⟦pred⟧' : (⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧) pred pred
unquoteDef ⟦pred⟧' = param-clauses-by-name defEnv2 (quote pred)

test-p2-pred : ∀ {n₀ n₁} (nᵣ : ⟦ℕ⟧ n₀ n₁) → ⟦pred⟧' nᵣ ≡ ⟦pred⟧ nᵣ
test-p2-pred ⟦zero⟧     = refl
test-p2-pred (⟦suc⟧ nᵣ) = refl

p/2 = param-rec-def-by-name defEnv2 (quote _/2)
q⟦/2⟧ = definition (quote _⟦/2⟧)
unquoteDecl _⟦/2⟧' = p/2 _⟦/2⟧'
test-/2 : function (p/2 (quote _⟦/2⟧)) ≡-def-no-hints q⟦/2⟧
test-/2 = refl
test-/2' : ∀ {n₀ n₁} (nᵣ : ⟦ℕ⟧ n₀ n₁) → nᵣ ⟦/2⟧' ≡ nᵣ ⟦/2⟧
test-/2' ⟦zero⟧ = refl
test-/2' (⟦suc⟧ ⟦zero⟧) = refl
test-/2' (⟦suc⟧ (⟦suc⟧ nᵣ)) rewrite test-/2' nᵣ = refl

p+ = param-rec-def-by-name defEnv2 (quote _+ℕ_)
q⟦+⟧ = definition (quote _⟦+ℕ⟧_)
unquoteDecl _⟦+⟧'_ = p+ _⟦+⟧'_
test-+ : function (p+ (quote _⟦+ℕ⟧_)) ≡-def-no-hints q⟦+⟧
test-+ = refl
test-+' : ∀ {n₀ n₁} (nᵣ : ⟦ℕ⟧ n₀ n₁) {n'₀ n'₁} (n'ᵣ : ⟦ℕ⟧ n'₀ n'₁) → nᵣ ⟦+⟧' n'ᵣ ≡ nᵣ ⟦+ℕ⟧ n'ᵣ
test-+' ⟦zero⟧    n'ᵣ = refl
test-+' (⟦suc⟧ nᵣ) n'ᵣ rewrite test-+' nᵣ n'ᵣ = refl

{-
is-good : String → 𝟚
is-good "good" = 1₂
is-good _      = 0₂

⟦is-good⟧ : (⟦String⟧ ⟦₀→₀⟧ ⟦𝟚⟧) is-good is-good
⟦is-good⟧ {"good"} refl = ⟦1₂⟧
⟦is-good⟧ {_}      refl = {!!}

my-good = unquote (lit (string "good"))
my-good-test : my-good ≡ "good"
my-good-test = refl
-}

{-
⟦is-good⟧' : (⟦String⟧ ⟦₀→₀⟧ ⟦𝟚⟧) is-good is-good
unquoteDef ⟦is-good⟧' = param-clauses-by-name defEnv2 (quote is-good)
test-is-good = {!!}
-}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

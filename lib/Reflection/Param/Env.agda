{-# OPTIONS --without-K #-}
module Reflection.Param.Env where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin using (Fin) renaming (toℕ to Fin▹ℕ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.List using (List; map; _++_; replicate)
open import Function
open import Relation.Nullary

open import Reflection.NP

-- Local "imports" to avoid depending on nplib
private
  postulate
    opaque : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
    -- opaque-rule : ∀ {x} y → opaque x y ≡ y

record Env (w : ℕ)(A B : Set) : Set where
  field
    pVarᵢ : Fin w → A → B
    pVarᵣ : A → B
    pConT : Name → Args → Term
    pConP : Name → Pats → Pattern
    pDef  : Name → Name
open Env public

Env' = λ w → Env w ℕ ℕ

ε-pVarᵢ : ∀ {w} → String → Fin w → ℕ → ℕ
ε-pVarᵢ = λ s i → opaque (s ++ˢ ".pVarᵢ " ++ˢ showNat (Fin▹ℕ i))

ε : ∀ w → Env' w
ε w = record { pVarᵢ = λ i n → 100000 + (1000 * Fin▹ℕ i) + n -- ε-pVarᵢ "ε"
             ; pVarᵣ = _+_ 200000 -- opaque "ε.pVarᵣ"
             ; pConP = opaque "ε.pConP" con
             ; pConT = opaque "ε.pConT" con
             ; pDef = opaque "ε.pDef" }

extDefEnv : ((Name → Name) → (Name → Name)) → ∀ {w A B} → Env w A B → Env w A B
extDefEnv ext Γ = record Γ { pDef = ext (pDef Γ) }

{-
extConEnv : ((Name → Name) → (Name → Name)) → ∀ {w A B} → Env w A B → Env w A B
extConEnv ext Γ = record Γ { pCon = ext (pCon Γ) }
-}

[_≔_] : {A : Set}(old : Name)(new : A)
                 (φ : Name → A) → (Name → A)
[ old ≔ new ] φ x = case (x ≟-Name old) of λ { (yes _) → new
                                             ; (no  _) → φ x }

↑pVar : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
↑pVar zero = id
↑pVar (suc n) = ↑pVar n ∘ mapVar↑'

liftConT : (Name → Name) → Name → Args → Term
liftConP : (Name → Name) → Name → Pats → Pattern
liftConT f = con ∘ f
liftConP f = con ∘ f

conSkip : List Visibility → Name → Args → Term
conSkip vs c args = con c (map (λ v → argʳ v unknown) vs ++ args)

conSkip' : ℕ → Name → Args → Term
conSkip' k = conSkip (replicate k hidden)

on-pVar : ∀ {w A B C D}
            (fᵢ : Fin w → (A → B) → (C → D))
            (fᵣ : (A → B) → (C → D))
          → Env w A B → Env w C D
on-pVar fᵢ fᵣ Γ = record
  { pVarᵢ = λ i → fᵢ i (pVarᵢ Γ i)
  ; pVarᵣ = fᵣ (pVarᵣ Γ)
  ; pConT = pConT Γ
  ; pConP = pConP Γ
  ; pDef = pDef Γ
  }

_+↑ : ∀ {w} → Env' w → Env' w
_+↑ {w} = on-pVar goi gor
  where
    goi : Fin w → (ℕ → ℕ) → (ℕ → ℕ)
    goi x f = _+_ (w ∸ Fin▹ℕ x) ∘ ↑pVar 1 (_+_ (Fin▹ℕ x) ∘ f)

    gor : (ℕ → ℕ) → (ℕ → ℕ)
    gor f = ↑pVar 1 (_+_ w ∘ f)

_+'_ : ∀ {w} → Env' w → ℕ → Env' w
Γ +' n = on-pVar (λ i f → _+_ n ∘ f) (λ f → _+_ n ∘ f) Γ

_+ʷ : ∀ {w} → Env' w → Env' w
_+ʷ {w} Γ = Γ +' w

_+1 : ∀ {w} → Env' w → Env' w
Γ +1 = Γ +' 1

module _ {w} (Γ : Env' w) where
    mapTermVarᵢ : (i : Fin w) (t : Term) → Term
    mapTermVarᵢ = mapVarTerm ∘ liftMapVar ∘ pVarᵢ Γ

    mapTypeVarᵢ : (i : Fin w) (t : Type) → Type
    mapTypeVarᵢ = mapVarType ∘ liftMapVar ∘ pVarᵢ Γ

⟦ℕ⟧-env = record (ε 2)
               { pDef  = [ quote ℕ ≔ quote ⟦ℕ⟧ ] id
               ; pConP = [ quote zero ≔ con (quote ⟦zero⟧) ]
                        ([ quote suc  ≔ con (quote ⟦suc⟧)  ]
                         con)
               ; pConT = [ quote zero ≔ con (quote ⟦zero⟧) ]
                        ([ quote zero ≔ con (quote ⟦zero⟧) ]
                         con)
               }

{-
defEnv2Fin = extConEnv ([ quote Fin.zero ≔ quote ⟦Fin⟧.⟦zero⟧ ] ∘
                        [ quote Fin.suc  ≔ quote ⟦Fin⟧.⟦suc⟧  ])
             (extDefEnv [ quote Fin ≔ quote ⟦Fin⟧ ] ⟦ℕ⟧-env)
-}

-- -}
-- -}
-- -}
-- -}

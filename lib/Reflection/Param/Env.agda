{-# OPTIONS --without-K #-}
module Reflection.Param.Env where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin using (Fin) renaming (toℕ to Fin▹ℕ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.List using (List; map; _++_; replicate)
open import Function
open import Relation.Nullary
open import Data.Nat.Param.Binary
open import Agda.Builtin.Reflection using (Visibility; Pattern; Name) renaming (con to conPat)
open import Agda.Builtin.Reflection using (Term) renaming (con to conTerm)
open import Reflection.AST.Name using () renaming (_≟_ to _≟-Name_)

open import Reflection.NP hiding (_≟-Name_)

-- Local "imports" to avoid depending on nplib
private
  postulate
    hide : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
    -- hide-rule : ∀ {x} y → hide x y ≡ y

record Env (w : ℕ)(A B : Set) : Set where
  field
    pVarᵢ : Fin w → A → B
    pVarᵣ : A → B
    pConT : Name → Args Term → Term
    pConP : Name → Pats → Pattern
    pDef  : Name → Name
open Env public

Env' = λ w → Env w ℕ ℕ

ε-pVarᵢ : ∀ {w} → String → Fin w → ℕ → ℕ
ε-pVarᵢ = λ s i → hide (s ++ˢ ".pVarᵢ " ++ˢ showNat (Fin▹ℕ i))

ε-pConP : Name → Pats → Pattern
ε-pConP c ps = hide "ε.pConP" (conPat c ps)

ε-pConT : Name → Args Term → Term
ε-pConT c args = hide "ε.pConT" (conTerm c args)

ε : ∀ w → Env' w
ε w = record { pVarᵢ = λ i n → 100000 + (1000 * Fin▹ℕ i) + n -- ε-pVarᵢ "ε"
             ; pVarᵣ = _+_ 200000 -- hide "ε.pVarᵣ"
             ; pConP = ε-pConP
             ; pConT = ε-pConT
             ; pDef = hide "ε.pDef" }

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

liftConT : (Name → Name) → Name → Args Term → Term
liftConP : (Name → Name) → Name → Pats → Pattern
liftConT f = conTerm ∘ f
liftConP f = conPat ∘ f

conSkip : List Visibility → Name → Args Term → Term
conSkip vs c args = conTerm c (map (λ v → argʳ v unknown) vs ++ args)

conSkip' : ℕ → Name → Args Term → Term
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

⟦ℕ⟧-env = record (ε 2)
               { pDef  = [ quote ℕ ≔ quote ⟦ℕ⟧ ] id
               ; pConP = [ quote zero ≔ conPat (quote ⟦zero⟧) ]
                        ([ quote suc  ≔ conPat (quote ⟦suc⟧)  ]
                         conPat)
               ; pConT = [ quote zero ≔ conTerm (quote ⟦zero⟧) ]
                        ([ quote zero ≔ conTerm (quote ⟦zero⟧) ]
                         conTerm)
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

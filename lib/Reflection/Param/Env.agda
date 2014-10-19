{-# OPTIONS --without-K #-}
module Reflection.Param.Env where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin using (Fin) renaming (toℕ to Fin▹ℕ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Function
open import Relation.Nullary

open import Reflection.NP

-- Local "imports" to avoid depending on nplib
private
  postulate
    opaque : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
    -- opaque-rule : ∀ {x} y → opaque x y ≡ y

record Env (n : ℕ)(A B : Set) : Set where
  field
    pVarᵢ : Fin n → A → B
    pVarᵣ : A → B
    pCon : Name → Name
    pDef : Name → Name
open Env public

Env' = λ n → Env n ℕ ℕ

ε-pVarᵢ : ∀ {n} → String → Fin n → ℕ → ℕ
ε-pVarᵢ = λ s i → opaque (s ++ˢ ".pVarᵢ " ++ˢ showNat (Fin▹ℕ i))

ε : ∀ n → Env' n
ε n = record { pVarᵢ = ε-pVarᵢ "ε"
             ; pVarᵣ = opaque "ε.pVarᵣ"
             ; pCon = opaque "ε.pCon"
             ; pDef = opaque "ε.pDef" }

extDefEnv : ((Name → Name) → (Name → Name)) → ∀ {n A B} → Env n A B → Env n A B
extDefEnv ext Γ = record Γ { pDef = ext (pDef Γ) }

extConEnv : ((Name → Name) → (Name → Name)) → ∀ {n A B} → Env n A B → Env n A B
extConEnv ext Γ = record Γ { pCon = ext (pCon Γ) }

[_≔_] : (old new : Name) (φ : Name → Name) → (Name → Name)
[ old ≔ new ] φ x = case (x ≟-Name old) of λ { (yes _) → new
                                             ; (no  _) → φ x }

↑pVar : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
↑pVar zero = id
↑pVar (suc n) = ↑pVar n ∘ mapVar↑'

on-pVar : ∀ {n A B C D}
            (fᵢ : Fin n → (A → B) → (C → D))
            (fᵣ : (A → B) → (C → D))
          → Env n A B → Env n C D
on-pVar fᵢ fᵣ Γ = record
  { pVarᵢ = λ i → fᵢ i (pVarᵢ Γ i)
  ; pVarᵣ = fᵣ (pVarᵣ Γ)
  ; pCon = pCon Γ
  ; pDef = pDef Γ }

_+↑ : ∀ {n} → Env' n → Env' n
_+↑ {n} = on-pVar goi gor
  where
    goi : Fin n → (ℕ → ℕ) → (ℕ → ℕ)
    goi x f = _+_ (n ∸ Fin▹ℕ x) ∘ ↑pVar 1 (_+_ (Fin▹ℕ x) ∘ f)

    gor : (ℕ → ℕ) → (ℕ → ℕ)
    gor f = ↑pVar 1 (_+_ n ∘ f)

_+'_ : ∀ {w} → Env' w → ℕ → Env' w
Γ +' n = record { pVarᵢ = λ i → _+_ n ∘ pVarᵢ Γ i
                ; pVarᵣ = _+_ n ∘ pVarᵣ Γ
                ; pCon = pCon Γ
                ; pDef = pDef Γ }

_+1 : ∀ {w} → Env' w → Env' w
Γ +1 = Γ +' 1

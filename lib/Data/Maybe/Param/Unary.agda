{-# OPTIONS --without-K #-}
open import Function
open import Level
open import Data.Maybe renaming (map to map?)

open import Type.Param.Unary
open import Function.Param.Unary

module Data.Maybe.Param.Unary where

data [Maybe] {a p} {A : Set a} (Aₚ : A → Set p) : Maybe A → Set (a ⊔ p) where
  [nothing] : [Maybe] Aₚ nothing
  [just]    : (Aₚ [→] [Maybe] Aₚ) just

[maybe] : ∀ {a b} → (∀⟨ Aₚ ∶ [Set] a ⟩[→] (∀⟨ Bₚ ∶ [Set] b ⟩[→] ((Aₚ [→] Bₚ) [→] (Bₚ [→] ([Maybe] Aₚ [→] Bₚ)))))
                     (maybe {a} {b})
[maybe] _ _ justₚ nothingₚ ([just] xₚ) = justₚ xₚ
[maybe] _ _ justₚ nothingₚ [nothing]   = nothingₚ

[map?] : ∀ {a b} → (∀⟨ Aₚ ∶ [Set] a ⟩[→] ∀⟨ Bₚ ∶ [Set] b ⟩[→] (Aₚ [→] Bₚ) [→] [Maybe] Aₚ [→] [Maybe] Bₚ) (map? {a} {b})
[map?] _ _ fₚ ([just] xₚ) = [just] (fₚ xₚ)
[map?] _ _ fₚ [nothing]   = [nothing]

private
    infixr 0 _→?_
    _→?_ : ∀ {a b} → Set a → Set b → Set _
    A →? B = A → Maybe B

_[→?]_ : ∀ {a b pa pb} → ([★] {a} pa [→] [★] {b} pb [→] [★] _) _→?_
Aₚ [→?] Bₚ = Aₚ [→] [Maybe] Bₚ

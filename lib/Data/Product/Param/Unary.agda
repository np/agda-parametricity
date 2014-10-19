{-# OPTIONS --without-K #-}
module Data.Product.Param.Unary where

open import Level
open import Data.Product
  renaming (proj₁ to fst; proj₂ to snd)
open import Type.Param.Unary
open import Function.Param.Unary

record [Σ] {a b aₚ bₚ}
           {A : Set a}
           {B : A → Set b}
           (Aₚ : A → Set aₚ)
           (Bₚ : {x : A} (xₚ : Aₚ x)
                 → B x → Set bₚ)
           (p : Σ A B) : Set (aₚ ⊔ bₚ) where
  constructor _[,]_
  field
    [fst] : Aₚ (fst p)
    [snd] : Bₚ [fst] (snd p)
open [Σ] public
infixr 4 _[,]_

syntax [Σ] Aₚ (λ xₚ → e) = [ xₚ ∶ Aₚ ][×][ e ]

[∃] : ∀ {a aₚ b bₚ} →
        (∀i⟨ Aₚ ∶ [Set] {a} aₚ ⟩[→] ((Aₚ [→] [Set] {b} bₚ) [→] [Set] _)) ∃
[∃] {xₚ = Aₚ} = [Σ] Aₚ

syntax [∃] (λ Aₚ → f) = [∃][ Aₚ ] f

_[×]_ : ∀ {a b aₚ bₚ} → ([Set] {a} aₚ [→] [Set] {b} bₚ [→] [Set] _) _×_
_[×]_ Aₚ Bₚ = [Σ] Aₚ (λ _ → Bₚ)

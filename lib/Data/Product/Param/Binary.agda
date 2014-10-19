{-# OPTIONS --without-K #-}
open import Level
open import Data.Product
  renaming (proj₁ to fst; proj₂ to snd)

open import Function.Param.Binary

module Data.Product.Param.Binary where

record ⟦Σ⟧ {a₁ a₂ b₂ b₁ aᵣ bᵣ}
           {A₁ : Set a₁} {A₂ : Set a₂}
           {B₁ : A₁ → Set b₁}
           {B₂ : A₂ → Set b₂}
           (Aᵣ : A₁ → A₂ → Set aᵣ)
           (Bᵣ : {x₁ : A₁} {x₂ : A₂} (xᵣ : Aᵣ x₁ x₂)
                → B₁ x₁ → B₂ x₂ → Set bᵣ)
           (p₁ : Σ A₁ B₁) (p₂ : Σ A₂ B₂) : Set (aᵣ ⊔ bᵣ) where
  constructor _⟦,⟧_
  field
    ⟦fst⟧ : Aᵣ (fst p₁) (fst p₂)
    ⟦snd⟧ : Bᵣ ⟦fst⟧ (snd p₁) (snd p₂)
open ⟦Σ⟧ public
infixr 4 _⟦,⟧_

syntax ⟦Σ⟧ Aᵣ (λ xᵣ → e) = [ xᵣ ∶ Aᵣ ]⟦×⟧[ e ]

⟦∃⟧ : ∀ {a₁ a₂ b₂ b₁ aᵣ bᵣ}
        {A₁ : Set a₁} {A₂ : Set a₂}
        {Aᵣ : A₁ → A₂ → Set aᵣ}
        {B₁ : A₁ → Set b₁}
        {B₂ : A₂ → Set b₂}
        (Bᵣ : ⟦Pred⟧ bᵣ Aᵣ B₁ B₂)
        (p₁ : Σ A₁ B₁) (p₂ : Σ A₂ B₂) → Set _
⟦∃⟧ = ⟦Σ⟧ _

syntax ⟦∃⟧ (λ xᵣ → e) = ⟦∃⟧[ xᵣ ] e

_⟦×⟧_ : ∀ {a₁ a₂ b₂ b₁ aᵣ bᵣ}
          {A₁ : Set a₁} {A₂ : Set a₂}
          {B₁ : Set b₁} {B₂ : Set b₂}
          (Aᵣ : A₁ → A₂ → Set aᵣ)
          (Bᵣ : B₁ → B₂ → Set bᵣ)
          (p₁ : A₁ × B₁) (p₂ : A₂ × B₂) → Set (aᵣ ⊔ bᵣ)
_⟦×⟧_ Aᵣ Bᵣ = ⟦Σ⟧ Aᵣ (λ _ → Bᵣ)

{-
_⟦×⟧_ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
          {b₁ b₂ bᵣ} {B₁ : Set b₁} {B₂ : Set b₂} (Bᵣ : B₁ → B₂ → Set bᵣ)
          (p₁ : A₁ × B₁) (p₂ : A₂ × B₂) → Set _
_⟦×⟧_ Aᵣ Bᵣ = λ p₁ p₂ → Aᵣ (fst p₁) (fst p₂) ×
                        Bᵣ (snd p₁) (snd p₂)
-}

{- One can give these two types to ⟦_,_⟧:

⟦_,_⟧' : ∀ {a₁ a₂ b₁ b₂ aᵣ bᵣ}
       {A₁ : Set a₁} {A₂ : Set a₂}
       {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
       {Aᵣ : ⟦Set⟧ aᵣ A₁ A₂}
       {Bᵣ : ⟦Pred⟧ Aᵣ bᵣ B₁ B₂}
       {x₁ x₂ y₁ y₂}
       (xᵣ : Aᵣ x₁ x₂)
       (yᵣ : Bᵣ xᵣ y₁ y₂)
     → ⟦Σ⟧ Aᵣ Bᵣ (x₁ , y₁) (x₂ , y₂)
⟦_,_⟧' = ⟦_,_⟧

⟦_,_⟧'' : ∀ {a₁ a₂ b₁ b₂ aᵣ bᵣ}
       {A₁ : Set a₁} {A₂ : Set a₂}
       {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
       {Aᵣ : ⟦Set⟧ aᵣ A₁ A₂}
       {Bᵣ : ⟦Pred⟧ Aᵣ bᵣ B₁ B₂}
       {p₁ p₂}
       (⟦fst⟧ : Aᵣ (fst p₁) (fst p₂))
       (⟦snd⟧ : Bᵣ ⟦fst⟧ (snd p₁) (snd p₂))
     → ⟦Σ⟧ Aᵣ Bᵣ p₁ p₂
⟦_,_⟧'' = ⟦_,_⟧
-}


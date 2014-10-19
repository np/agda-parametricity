{-# OPTIONS --without-K #-}
open import Level
open import Function
open import Data.Maybe renaming (map to map?)

open import Type.Param.Binary
open import Function.Param.Binary

module Data.Maybe.Param.Binary where

data ⟦Maybe⟧ {a b r} {A : Set a} {B : Set b} (_∼_ : A → B → Set r) : Maybe A → Maybe B → Set (a ⊔ b ⊔ r) where
  ⟦just⟧    : ∀ {x₁ x₂} → (xᵣ : x₁ ∼ x₂) → ⟦Maybe⟧ _∼_ (just x₁) (just x₂)
  ⟦nothing⟧ : ⟦Maybe⟧ _∼_ nothing nothing

⟦maybe⟧ : ∀ {a b} → (∀⟨ Aᵣ ∶ ⟦Set⟧ a ⟩⟦→⟧ (∀⟨ Bᵣ ∶ ⟦Set⟧ b ⟩⟦→⟧ ((Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ (Bᵣ ⟦→⟧ (⟦Maybe⟧ Aᵣ ⟦→⟧ Bᵣ)))))
                     (maybe {a} {b}) (maybe {a} {b})
⟦maybe⟧ _ _ justᵣ nothingᵣ (⟦just⟧ xᵣ) = justᵣ xᵣ
⟦maybe⟧ _ _ justᵣ nothingᵣ ⟦nothing⟧   = nothingᵣ

⟦map?⟧ : ∀ {a b} → (∀⟨ Aᵣ ∶ ⟦Set⟧ a ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦Set⟧ b ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ ⟦Maybe⟧ Aᵣ ⟦→⟧ ⟦Maybe⟧ Bᵣ) (map? {a} {b}) (map? {a} {b})
⟦map?⟧ _ _ fᵣ (⟦just⟧ xᵣ) = ⟦just⟧ (fᵣ xᵣ)
⟦map?⟧ _ _ fᵣ ⟦nothing⟧   = ⟦nothing⟧

⟦map?-id⟧ : ∀ {a} → (∀⟨ Aᵣ ∶ ⟦Set⟧ {a} {a} a ⟩⟦→⟧ ⟦Maybe⟧ Aᵣ ⟦→⟧ ⟦Maybe⟧ Aᵣ) (map? id) id
⟦map?-id⟧ _ (⟦just⟧ xᵣ) = ⟦just⟧ xᵣ
⟦map?-id⟧ _ ⟦nothing⟧   = ⟦nothing⟧

private
    infixr 0 _→?_
    _→?_ : ∀ {a b} → Set a → Set b → Set _
    A →? B = A → Maybe B

_⟦→?⟧_ : ∀ {a0 a1 ar b0 b1 br} → (⟦★⟧ {a0} {a1} ar ⟦→⟧ ⟦★⟧ {b0} {b1} br ⟦→⟧ ⟦★⟧ _) _→?_ _→?_
Aᵣ ⟦→?⟧ Bᵣ = Aᵣ ⟦→⟧ ⟦Maybe⟧ Bᵣ

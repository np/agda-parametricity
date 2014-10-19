{-# OPTIONS --without-K #-}
open import Level
open import Function
open import Data.Sum
  renaming (inj₁ to inl; inj₂ to inr)
open import Type.Param.Binary
open import Function.Param.Binary

module Data.Sum.Param.Binary where

infixr 4 _⟦⊎⟧_

data _⟦⊎⟧_ {a₁ a₂ b₁ b₂ aᵣ bᵣ}
            {A₁ : Set a₁} {A₂ : Set a₂}
            (Aᵣ : A₁ → A₂ → Set aᵣ)
            {B₁ : Set b₁} {B₂ : Set b₂}
            (Bᵣ : B₁ → B₂ → Set bᵣ) : A₁ ⊎ B₁ → A₂ ⊎ B₂ → Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ aᵣ ⊔ bᵣ) where
  ⟦inl⟧ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → (Aᵣ ⟦⊎⟧ Bᵣ) (inl x₁) (inl x₂)
  ⟦inr⟧ : ∀ {x₁ x₂} (xᵣ : Bᵣ x₁ x₂) → (Aᵣ ⟦⊎⟧ Bᵣ) (inr x₁) (inr x₂)

⟦[_,_]′⟧ : ∀ {a b c} →
             (∀⟨ A ∶ ⟦Set⟧ a ⟩⟦→⟧ ∀⟨ B ∶ ⟦Set⟧ b ⟩⟦→⟧ ∀⟨ C ∶ ⟦Set⟧ c ⟩⟦→⟧
                (A ⟦→⟧ C) ⟦→⟧ (B ⟦→⟧ C) ⟦→⟧ (A ⟦⊎⟧ B) ⟦→⟧ C)
             ([_,_]′ {a} {b} {c}) ([_,_]′ {a} {b} {c})
⟦[_,_]′⟧ _ _ _ f _ (⟦inl⟧ xᵣ) = f xᵣ
⟦[_,_]′⟧ _ _ _ _ g (⟦inr⟧ xᵣ) = g xᵣ

⟦map⟧ : ∀ {a b c d} →
        (∀⟨ A ∶ ⟦Set⟧ a ⟩⟦→⟧ ∀⟨ B ∶ ⟦Set⟧ b ⟩⟦→⟧ ∀⟨ C ∶ ⟦Set⟧ c ⟩⟦→⟧ ∀⟨ D ∶ ⟦Set⟧ d ⟩⟦→⟧
            (A ⟦→⟧ C) ⟦→⟧ (B ⟦→⟧ D) ⟦→⟧ (A ⟦⊎⟧ B ⟦→⟧ C ⟦⊎⟧ D))
        (map {a} {b} {c} {d}) (map {a} {b} {c} {d})
⟦map⟧ A B C D f g = ⟦[_,_]′⟧ A B (C ⟦⊎⟧ D) (⟦inl⟧ ∘′ f) (⟦inr⟧ ∘′ g)

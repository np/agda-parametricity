{-# OPTIONS --without-K #-}
open import Level
open import Relation.Nullary hiding (yes; no)
open import Relation.Nullary as RN using (yes; no)
open import Relation.Binary

open import Function.Param.Binary
open import Type.Param.Binary
open import Data.Zero.Param.Binary

module Data.Dec.Param.Binary where

data ⟦Dec⟧ {ℓ₁ ℓ₂ ℓᵣ} {P₁ : Set ℓ₁} {P₂ : Set ℓ₂} (Pᵣ : P₁ → P₂ → Set ℓᵣ) : ⟦Set⟧ (ℓ₁ ⊔ ℓ₂ ⊔ ℓᵣ) (Dec P₁) (Dec P₂) where
  ⟦yes⟧ : {p₁ : P₁} {p₂ : P₂} (pᵣ : Pᵣ p₁ p₂) → ⟦Dec⟧ Pᵣ (RN.yes p₁) (RN.yes p₂)
  ⟦no⟧  : {¬p₁ : ¬ P₁} {¬p₂ : ¬ P₂} (¬pᵣ : (⟦¬⟧ Pᵣ) ¬p₁ ¬p₂) → ⟦Dec⟧ Pᵣ (RN.no ¬p₁) (RN.no ¬p₂)

private
  ⟦Dec⟧' : ∀ {p₁} {p₂} {pᵣ} → ⟦Pred⟧ {p₁} {p₂} _ (⟦Set⟧ pᵣ) Dec Dec
  ⟦Dec⟧' = ⟦Dec⟧

⟦Decidable⟧ : ∀ {a₁ a₂ aᵣ b₁ b₂ bᵣ ℓ₁ ℓ₂ ℓᵣ}
              → (∀⟨ Aᵣ ∶ ⟦Set⟧ {a₁} {a₂} aᵣ ⟩⟦→⟧
                 ∀⟨ Bᵣ ∶ ⟦Set⟧ {b₁} {b₂} bᵣ ⟩⟦→⟧
                   ⟦REL⟧ Aᵣ Bᵣ {ℓ₁} {ℓ₂} ℓᵣ ⟦→⟧ ⟦Set⟧ _) Decidable Decidable
⟦Decidable⟧ Aᵣ Bᵣ _∼ᵣ_ = ⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ ⟨ yᵣ ∶ Bᵣ ⟩⟦→⟧ ⟦Dec⟧ (xᵣ ∼ᵣ yᵣ)

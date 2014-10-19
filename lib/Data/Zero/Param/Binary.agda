{-# OPTIONS --without-K #-}
open import Data.Empty renaming (⊥ to 𝟘)
open import Relation.Nullary

open import Type.Param.Binary
open import Function.Param.Binary

module Data.Zero.Param.Binary where

data ⟦𝟘⟧ (x₁ x₂ : 𝟘) : Set₀ where

infix 3 ⟦¬⟧_

⟦¬⟧_ : ∀ {a₁ a₂ aₚ} → (⟦Set⟧ {a₁} {a₂} aₚ ⟦→⟧ ⟦Set⟧ _) ¬_ ¬_
⟦¬⟧ Aᵣ = Aᵣ ⟦→⟧ ⟦𝟘⟧

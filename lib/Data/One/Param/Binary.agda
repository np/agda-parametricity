{-# OPTIONS --without-K #-}
open import Type.Param.Binary
open import Data.Unit renaming (⊤ to 𝟙; tt to 0₁)

module Data.One.Param.Binary where

record ⟦𝟙⟧ (x₁ x₂ : 𝟙) : Set₀ where
  constructor ⟦0₁⟧

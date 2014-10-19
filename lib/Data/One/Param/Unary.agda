module Data.One.Param.Unary where

open import Data.Unit renaming (⊤ to 𝟙; tt to 0₁)

record [𝟙] (x : 𝟙) : Set₀ where
  constructor [0₁]

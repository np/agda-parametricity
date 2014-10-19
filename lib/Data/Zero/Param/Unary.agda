module Data.Zero.Param.Unary where

open import Data.Empty renaming (⊥ to 𝟘)
open import Relation.Nullary

open import Type.Param.Unary
open import Function.Param.Unary

data [𝟘] (x : 𝟘) : Set₀ where

infix 3 [¬]_

[¬]_ : ∀ {a aₚ} → ([Set] {a} aₚ [→] [Set] _) ¬_
[¬] Aₚ = Aₚ [→] [𝟘]

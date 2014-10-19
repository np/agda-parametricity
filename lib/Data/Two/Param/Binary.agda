open import Relation.Binary.Logical

open import Data.Bool
  using    (not; _∧_; _∨_; _xor_)
  renaming (Bool to 𝟚; false to 0₂; true to 1₂)

module Data.Two.Param.Binary where

data ⟦𝟚⟧ : ⟦★₀⟧ 𝟚 𝟚 where
  ⟦0₂⟧ : ⟦𝟚⟧ 0₂ 0₂
  ⟦1₂⟧ : ⟦𝟚⟧ 1₂ 1₂

⟦not⟧ : (⟦𝟚⟧ ⟦→⟧ ⟦𝟚⟧) not not
⟦not⟧ ⟦1₂⟧ = ⟦0₂⟧
⟦not⟧ ⟦0₂⟧ = ⟦1₂⟧

_⟦∧⟧_ : (⟦𝟚⟧ ⟦→⟧ ⟦𝟚⟧ ⟦→⟧ ⟦𝟚⟧) _∧_ _∧_
⟦1₂⟧ ⟦∧⟧ x = x
⟦0₂⟧ ⟦∧⟧ _ = ⟦0₂⟧

_⟦∨⟧_ : (⟦𝟚⟧ ⟦→⟧ ⟦𝟚⟧ ⟦→⟧ ⟦𝟚⟧) _∨_ _∨_
⟦1₂⟧ ⟦∨⟧ _ = ⟦1₂⟧
⟦0₂⟧ ⟦∨⟧ x = x

_⟦xor⟧_ : (⟦𝟚⟧ ⟦→⟧ ⟦𝟚⟧ ⟦→⟧ ⟦𝟚⟧) _xor_ _xor_
⟦1₂⟧ ⟦xor⟧ x = ⟦not⟧ x
⟦0₂⟧ ⟦xor⟧ x = x

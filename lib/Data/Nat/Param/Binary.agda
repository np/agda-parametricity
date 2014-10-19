module Data.Nat.Param.Binary where

import Level as L
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; z≤n; s≤s; ≤-pred; _≤?_; _+_)
open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Logical

data ⟦ℕ⟧ : ⟦Set₀⟧ ℕ ℕ where
  ⟦zero⟧ : ⟦ℕ⟧ zero zero
  ⟦suc⟧  : ∀ {n₁ n₂} (nᵣ : ⟦ℕ⟧ n₁ n₂) → ⟦ℕ⟧ (suc n₁) (suc n₂)

_⟦+⟧_ : (⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧) _+_ _+_
⟦zero⟧  ⟦+⟧ n = n
⟦suc⟧ m ⟦+⟧ n = ⟦suc⟧ (m ⟦+⟧ n)

⟦pred⟧ : (⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧) pred pred
⟦pred⟧ ⟦zero⟧     = ⟦zero⟧
⟦pred⟧ (⟦suc⟧ nᵣ) = nᵣ

data ⟦≤⟧ : ⟦REL⟧ ⟦ℕ⟧ ⟦ℕ⟧ L.zero _≤_ _≤_ where
  z≤n : ∀ {m₁ m₂} {mᵣ : ⟦ℕ⟧ m₁ m₂} → ⟦≤⟧ ⟦zero⟧ mᵣ z≤n z≤n
  s≤s : ∀ {m₁ m₂ n₁ n₂ mᵣ nᵣ} {m≤n₁ : m₁ ≤ n₁} {m≤n₂ : m₂ ≤ n₂} (m≤nᵣ : ⟦≤⟧ mᵣ nᵣ m≤n₁ m≤n₂)
        → ⟦≤⟧ (⟦suc⟧ mᵣ) (⟦suc⟧ nᵣ) (s≤s m≤n₁) (s≤s m≤n₂)

⟦≤-pred⟧ : ∀ {m₁ m₂ n₁ n₂ mᵣ nᵣ} {m≤n₁ : suc m₁ ≤ suc n₁} {m≤n₂ : suc m₂ ≤ suc n₂}
          → ⟦≤⟧ (⟦suc⟧ mᵣ) (⟦suc⟧ nᵣ) m≤n₁ m≤n₂ → ⟦≤⟧ mᵣ nᵣ (≤-pred m≤n₁) (≤-pred m≤n₂)
⟦≤-pred⟧ (s≤s m≤n) = m≤n

_⟦≤?⟧_ : ⟦Decidable⟧ ⟦ℕ⟧ ⟦ℕ⟧ ⟦≤⟧ _≤?_ _≤?_
⟦zero⟧             ⟦≤?⟧ _      = yes z≤n
⟦suc⟧ nᵣ           ⟦≤?⟧ ⟦zero⟧   = no (λ())
⟦suc⟧ {m₁} {m₂} mᵣ ⟦≤?⟧ ⟦suc⟧ {n₁} {n₂} nᵣ
 with m₁ ≤? n₁ | m₂ ≤? n₂ | mᵣ ⟦≤?⟧ nᵣ
... | yes _     | yes _      | yes m≤nᵣ = yes (s≤s m≤nᵣ)
... | no _      | no _       | no ¬m≤nᵣ = no (¬m≤nᵣ ∘ ⟦≤-pred⟧)
... | yes _     | no _       | ()
... | no _      | yes _      | ()

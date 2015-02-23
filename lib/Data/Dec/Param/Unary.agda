{-# OPTIONS --without-K #-}
open import Level
open import Relation.Nullary
open import Relation.Binary

open import Function.Param.Unary
open import Type.Param.Unary
open import Data.Zero.Param.Unary

module Data.Dec.Param.Unary where

data [Dec] {p pₚ} {P : Set p} (Pₚ : P → Set pₚ) : [Set] (p ⊔ pₚ) (Dec P) where
  yes : ∀ {p : P}    (pₚ : Pₚ p) → [Dec] Pₚ (yes p)
  no  : ∀ {¬p : ¬ P} (¬pₚ : ([¬] Pₚ) ¬p) → [Dec] Pₚ (no ¬p)

private
  [Dec]' : ∀ {p} → [Pred] {p} p ([Set] p) Dec
  [Dec]' = [Dec]

[Decidable] : ∀ {a aₚ b bₚ r rₚ}
              → (∀⟨ Aₚ ∶ [Set] {a} aₚ ⟩[→]
                 ∀⟨ Bₚ ∶ [Set] {b} bₚ ⟩[→]
                   [REL] Aₚ Bₚ {r} rₚ [→] [Set] _) Decidable
[Decidable] Aₚ Bₚ _∼ₚ_ = ⟨ xₚ ∶ Aₚ ⟩[→] ⟨ yₚ ∶ Bₚ ⟩[→] [Dec] (xₚ ∼ₚ yₚ)

{-# OPTIONS --without-K #-}
open import Level
open import Function
open import Data.Sum
  renaming (inj₁ to inl; inj₂ to inr)
open import Type.Param.Unary
open import Function.Param.Unary

module Data.Sum.Param.Unary where

infixr 4 _[⊎]_

data _[⊎]_ {a b aₚ bₚ}
            {A : Set a}
            (Aₚ : A → Set aₚ)
            {B : Set b}
            (Bₚ : B → Set bₚ) : A ⊎ B → Set (a ⊔ b ⊔ aₚ ⊔ bₚ) where
  [inl] : ∀ {x} (xₚ : Aₚ x) → (Aₚ [⊎] Bₚ) (inl x)
  [inr] : ∀ {x} (xₚ : Bₚ x) → (Aₚ [⊎] Bₚ) (inr x)

[[_,_]′] : ∀ {a b c} →
             (∀⟨ A ∶ [Set] a ⟩[→] ∀⟨ B ∶ [Set] b ⟩[→] ∀⟨ C ∶ [Set] c ⟩[→]
                (A [→] C) [→] (B [→] C) [→] (A [⊎] B) [→] C)
             ([_,_]′ {a} {b} {c})
[[_,_]′] _ _ _ f _ ([inl] xₚ) = f xₚ
[[_,_]′] _ _ _ _ g ([inr] xₚ) = g xₚ

[map] : ∀ {a b c d} →
        (∀⟨ A ∶ [Set] a ⟩[→] ∀⟨ B ∶ [Set] b ⟩[→] ∀⟨ C ∶ [Set] c ⟩[→] ∀⟨ D ∶ [Set] d ⟩[→]
            (A [→] C) [→] (B [→] D) [→] (A [⊎] B [→] C [⊎] D))
        (map {a} {b} {c} {d})
[map] A B C D f g = [[_,_]′] A B (C [⊎] D) ([inl] ∘′ f) ([inr] ∘′ g)

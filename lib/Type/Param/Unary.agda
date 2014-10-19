{-# OPTIONS --without-K #-}
module Type.Param.Unary where

open import Level

private
  ★₀ = Set₀
  ★₁ = Set₁
  ★₂ = Set₂
  ★_ : ∀ ℓ → Set (suc ℓ)
  ★ ℓ = Set ℓ

[★] : ∀ {a} aₚ (A : ★ a) → ★ _
[★] aₚ A = A → ★ aₚ

[★₀] : ∀ (A : ★₀) → ★₁
[★₀] = [★] zero

[★₁] : ∀ (A : ★₁) → ★₂
[★₁] = [★] (suc zero)

[Set] : ∀ {a} aₚ (A : ★ a) → Set _
[Set] aₚ = λ A → A → Set aₚ

[Set₀] : Set₀ → Set₁
[Set₀] = λ A → A → Set₀

[Set₁] : Set₁ → Set₂
[Set₁] = λ A → A → Set₁

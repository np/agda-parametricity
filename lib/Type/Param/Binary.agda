{-# OPTIONS --without-K #-}
open import Level renaming (zero to ₀; suc to ₛ)

module Type.Param.Binary where

private
  ★_ = λ ℓ → Set ℓ
  ★₀ = Set₀
  ★₁ = Set₁
  ★₂ = Set₂

⟦★⟧ : ∀ {a₁ a₂} aᵣ (A₁ : ★ a₁) (A₂ : ★ a₂) → ★ _
⟦★⟧ aᵣ A₁ A₂ = A₁ → A₂ → ★ aᵣ

⟦★⟧₀ : ∀ {a₁ a₂} (A₁ : ★ a₁) (A₂ : ★ a₂) → ★ _
⟦★⟧₀ = ⟦★⟧ ₀

⟦★₀⟧ : ∀ (A₁ A₂ : ★₀) → ★₁
⟦★₀⟧ = ⟦★⟧₀

⟦★₁⟧ : ∀ (A₁ A₂ : ★₁) → ★₂
⟦★₁⟧ = ⟦★⟧ (ₛ ₀)

-- old name
⟦Set⟧ : ∀ {a₁ a₂} aᵣ (A₁ : ★ a₁) (A₂ : ★ a₂) → ★ _
⟦Set⟧ aᵣ A₁ A₂ = A₁ → A₂ → ★ aᵣ

-- old name (simpler internal representation: no use of defined names, no patterns)
⟦Set₀⟧ : (A₁ A₂ : Set₀) → Set₁
⟦Set₀⟧ = λ A₁ A₂ → A₁ → A₂ → Set₀

-- old name (see ⟦Set₀⟧)
⟦Set₁⟧ : (A₁ A₂ : Set₁) → Set₂
⟦Set₁⟧ = λ A₁ A₂ → A₁ → A₂ → Set₁

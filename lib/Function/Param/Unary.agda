{-# OPTIONS --without-K #-}
open import Level
open import Algebra.FunctionProperties
open import Relation.Nullary
open import Relation.Binary

module Function.Param.Unary where

open import Type.Param.Unary

private
  ★₀ = Set₀
  ★₁ = Set₁
  ★₂ = Set₂
  ★_ : ∀ ℓ → Set (suc ℓ)
  ★ ℓ = Set ℓ
 
[Π] : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
        {b bₚ} {B : A → ★ b} (Bₚ : ∀ {x} (xₚ : Aₚ x) → B x → ★ bₚ)
        (f : (x : A) → B x) → ★ _
[Π] Aₚ Bₚ = λ f → ∀ {x} (xₚ : Aₚ x) → Bₚ xₚ (f x)

infixr 0 [Π]
syntax [Π] Aₚ (λ xₚ → f) = ⟨ xₚ ∶ Aₚ ⟩[→] f

[Π]e : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
         {b bₚ} {B : A → ★ b} (Bₚ : ∀ {x} (xₚ : Aₚ x) → B x → ★ bₚ)
         (f : (x : A) → B x) → ★ _
[Π]e Aₚ Bₚ = λ f → ∀ x (xₚ : Aₚ x) → Bₚ xₚ (f x)

[∀] : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
        {b bₚ} {B : A → ★ b} (Bₚ : ∀ {x} (xₚ : Aₚ x) → B x → ★ bₚ)
        (f : {x : A} → B x) → ★ _
[∀] Aₚ Bₚ = λ f → ∀ {x} (xₚ : Aₚ x) → Bₚ xₚ (f {x})

-- more implicit than [∀]
[∀]i : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
         {b bₚ} {B : A → ★ b} (Bₚ : ∀ {x} (xₚ : Aₚ x) → B x → ★ bₚ)
         (f : {x : A} → B x) → ★ _
[∀]i Aₚ Bₚ = λ f → ∀ {x} {xₚ : Aₚ x} → Bₚ xₚ (f {x})

infixr 0 [∀] [∀]i
syntax [∀]  Aₚ (λ xₚ → f) = ∀⟨ xₚ ∶ Aₚ ⟩[→] f
syntax [∀]i Aₚ (λ xₚ → f) = ∀i⟨ xₚ ∶ Aₚ ⟩[→] f

infixr 1 _[→]_
_[→]_ : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
          {b bₚ} {B : ★ b} (Bₚ : B → ★ bₚ)
          (f : A → B) → ★ _
Aₚ [→] Bₚ = [Π] Aₚ (λ _ → Bₚ)

infixr 0 _[→]e_
_[→]e_ : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
           {b bₚ} {B : ★ b} (Bₚ : B → ★ bₚ)
           (f : A → B) → ★ _
_[→]e_ Aₚ Bₚ = [Π]e Aₚ (λ _ → Bₚ)

-- Products [Σ], [∃], [×] are in Data.Product.Param.Unary

-- open import Relation.Unary.NP using (Pred)
private
    -- Flipped version of Relation.Unary.Pred which scale better
    -- to logical relation [Pred] and ⟦Pred⟧
    Pred : ∀ ℓ {a} (A : ★ a) → ★ (a ⊔ suc ℓ)
    Pred ℓ A = A → ★ ℓ

[Pred] : ∀ {p} pₚ {a aₚ} → ([★] {a} aₚ [→] [★] _) (Pred p)
[Pred] pₚ Aₚ = Aₚ [→] [★] pₚ

private
  REL′ : ∀ r {a b} → ★ a → ★ b → ★ (a ⊔ b ⊔ suc r)
  REL′ r A B = A → B → ★ r

  [REL]′ : ∀ {r} rₚ {a aₚ b bₚ} →
          ([★] {a} aₚ [→] [★] {b} bₚ [→] [★] _) (REL′ r)
  [REL]′ rₚ Aₚ Bₚ = Aₚ [→] Bₚ [→] ([★] rₚ)

[REL] : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
          {b bₚ} {B : ★ b} (Bₚ : B → ★ bₚ)
          {r} rₚ (∼ : REL A B r) → ★ _
[REL] Aₚ Bₚ rₚ = Aₚ [→] Bₚ [→] ([★] rₚ)

[Rel] : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
          {r} rₚ (∼ : Rel A r) → ★ _
[Rel] Aₚ rₚ = [REL] Aₚ Aₚ rₚ

[Op₁] : ∀ {a} → ([★] {a} a [→] [★] a) Op₁
[Op₁] Aₚ = Aₚ [→] Aₚ

[Op₂] : ∀ {a aₚ} → ([★] {a} (a ⊔ aₚ) [→] [★] (a ⊔ aₚ)) Op₂
[Op₂] Aₚ = Aₚ [→] Aₚ [→] Aₚ

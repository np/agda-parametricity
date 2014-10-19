open import Level
open import Type.Param.Binary
open import Algebra.FunctionProperties

module Function.Param.Binary where

private
  ★_ = λ ℓ → Set ℓ
  ★₀ = Set₀
  ★₁ = Set₁
  ★₂ = Set₂

⟦Π⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → ★ b₁} {B₂ : A₂ → ★ b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → ★ bᵣ)
         (f₁ : (x : A₁) → B₁ x) (f₂ : (x : A₂) → B₂ x) → ★ _
⟦Π⟧ Aᵣ Bᵣ = λ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ x₁) (f₂ x₂)

infixr 0 ⟦Π⟧
syntax ⟦Π⟧ Aᵣ (λ xᵣ → f) = ⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ f

⟦Π⟧e : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → ★ b₁} {B₂ : A₂ → ★ b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → ★ bᵣ)
         (f₁ : (x : A₁) → B₁ x) (f₂ : (x : A₂) → B₂ x) → ★ _
⟦Π⟧e Aᵣ Bᵣ = λ f₁ f₂ → ∀ x₁ x₂ (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ x₁) (f₂ x₂)

⟦∀⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → ★ b₁} {B₂ : A₂ → ★ b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → ★ bᵣ)
         (f₁ : {x : A₁} → B₁ x) (f₂ : {x : A₂} → B₂ x) → ★ _
⟦∀⟧ Aᵣ Bᵣ = λ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ {x₁}) (f₂ {x₂})

infixr 0 ⟦∀⟧
syntax ⟦∀⟧ Aᵣ (λ xᵣ → f) = ∀⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ f

infixr 1 _⟦→⟧_
_⟦→⟧_ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : B₁ → B₂ → ★ bᵣ)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★ _
Aᵣ ⟦→⟧ Bᵣ = ⟦Π⟧ Aᵣ (λ _ → Bᵣ)

infixr 0 _⟦→⟧e_
_⟦→⟧e_ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : B₁ → B₂ → ★ bᵣ)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★ _
_⟦→⟧e_ Aᵣ Bᵣ = ⟦Π⟧e Aᵣ (λ _ → Bᵣ)

infixr 1 _→⟧_
_→⟧_ : ∀ {a b₁ b₂ bᵣ} (A : ★ a) {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : ⟦★⟧ bᵣ B₁ B₂) → ⟦★⟧ _ (A → B₁) (A → B₂)
(A →⟧ Bᵣ) f₁ f₂ = ∀ (x : A) → Bᵣ (f₁ x) (f₂ x)

Π⟧ : ∀ {a b₁ b₂ bᵣ} (A : ★ a) {B₁ : A → ★ b₁} {B₂ : A → ★ b₂} (Bᵣ : (A →⟧ ⟦★⟧ bᵣ) B₁ B₂) → ⟦★⟧ _ ((x : A) → B₁ x) ((x : A) → B₂ x)
Π⟧ A Bᵣ f₁ f₂ = ∀ (x : A) → Bᵣ x (f₁ x) (f₂ x)

infixr 0 Π⟧
syntax Π⟧ A (λ x → f) = ⟨ x ∶ A ⟩→⟧ f

∀⟧ : ∀ {a} (A : ★ a)
       {b₁ b₂ bᵣ} {B₁ : A → ★ b₁} {B₂ : A → ★ b₂} (Bᵣ : ∀ x → B₁ x → B₂ x → ★ bᵣ)
       (f₁ : {x : A} → B₁ x) (f₂ : {x : A} → B₂ x) → ★ _
∀⟧ A Bᵣ f₁ f₂ = {x : A} → Bᵣ x (f₁ {x}) (f₂ {x})

infixr 0 ∀⟧
syntax ∀⟧ A (λ x → f) = ∀⟨ x ∶ A ⟩→⟧ f

-- Non universe polymorphic versions

infixr 1 _⟦₀→₀⟧_ _⟦₀→₁⟧_ _⟦₁→₂⟧_

_⟦₀→₀⟧_ : ∀ {A₁ A₂ : ★₀} (Aᵣ : A₁ → A₂ → ★₀)
          {B₁ B₂ : ★₀} (Bᵣ : B₁ → B₂ → ★₀)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★₀
_⟦₀→₀⟧_ = λ {A₁} {A₂} Aᵣ {B₁} {B₂} Bᵣ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ (f₁ x₁) (f₂ x₂)

_⟦₀→₁⟧_ : ∀ {A₁ A₂ : ★₀} (Aᵣ : A₁ → A₂ → ★₀)
          {B₁ B₂ : ★₁} (Bᵣ : B₁ → B₂ → ★₁)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★₁
_⟦₀→₁⟧_ = λ {A₁} {A₂} Aᵣ {B₁} {B₂} Bᵣ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ (f₁ x₁) (f₂ x₂)

_⟦₁→₂⟧_ : ∀ {A₁ A₂ : ★₁} (Aᵣ : A₁ → A₂ → ★₁)
          {B₁ B₂ : ★₂} (Bᵣ : B₁ → B₂ → ★₂)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★₂
_⟦₁→₂⟧_ = λ {A₁} {A₂} Aᵣ {B₁} {B₂} Bᵣ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ (f₁ x₁) (f₂ x₂)

-- open import Relation.Unary.NP using (Pred)
private
  -- Flipped version of Relation.Unary.Pred which scale better
  -- to logical relation [Pred] and ⟦Pred⟧
  Pred : ∀ ℓ {a} (A : ★ a) → ★ (a ⊔ suc ℓ)
  Pred ℓ A = A → ★ ℓ

⟦Pred⟧ : ∀ {p₁ p₂} pᵣ {a₁ a₂ aᵣ} → (⟦★⟧ {a₁} {a₂} aᵣ ⟦→⟧ ⟦★⟧ _) (Pred p₁) (Pred p₂)
⟦Pred⟧ pᵣ Aᵣ = Aᵣ ⟦→⟧ ⟦★⟧ pᵣ

private
  -- from Relation.Binary
  REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
  REL A B ℓ = A → B → Set ℓ

  -- from Relation.Binary
  Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
  Rel A ℓ = REL A A ℓ

  REL′ : ∀ ℓ {a b} → ★ a → ★ b → ★ (a ⊔ b ⊔ suc ℓ)
  REL′ ℓ A B = A → B → ★ ℓ

  ⟦REL⟧′ : ∀ {a₁ a₂ aᵣ b₁ b₂ bᵣ r₁ r₂} rᵣ →
          (⟦★⟧ {a₁} {a₂} aᵣ ⟦→⟧ ⟦★⟧ {b₁} {b₂} bᵣ ⟦→⟧ ⟦★⟧ _) (REL′ r₁) (REL′ r₂)
  ⟦REL⟧′ rᵣ Aᵣ Bᵣ = Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ (⟦★⟧ rᵣ)

⟦REL⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : B₁ → B₂ → ★ bᵣ)
          {r₁ r₂} rᵣ (∼₁ : REL A₁ B₁ r₁) (∼₂ : REL A₂ B₂ r₂) → ★ _
⟦REL⟧ Aᵣ Bᵣ rᵣ = Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ (⟦★⟧ rᵣ)

⟦Rel⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {r₁ r₂} ℓᵣ (∼₁ : Rel A₁ r₁) (∼₂ : Rel A₂ r₂) → ★ _
⟦Rel⟧ Aᵣ rᵣ = ⟦REL⟧ Aᵣ Aᵣ rᵣ

⟦Op₁⟧ : ∀ {a₁ a₂ aᵣ} → (⟦★⟧ {a₁} {a₂} (a₁ ⊔ a₂ ⊔ aᵣ) ⟦→⟧ ⟦★⟧ _) Op₁ Op₁
⟦Op₁⟧ Aᵣ = Aᵣ ⟦→⟧ Aᵣ

⟦Op₂⟧ : ∀ {a₁ a₂ aᵣ} → (⟦★⟧ {a₁} {a₂} (a₁ ⊔ a₂ ⊔ aᵣ) ⟦→⟧ ⟦★⟧ _) Op₂ Op₂
⟦Op₂⟧ Aᵣ = Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ Aᵣ

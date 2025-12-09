{-# OPTIONS --without-K #-}
open import Function
open import Data.Unit renaming (⊤ to 𝟙; tt to 0₁)
open import Data.Bool
  using    (not)
  renaming (Bool to 𝟚; false to 0₂; true to 1₂)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin using (Fin; zero; suc) renaming (toℕ to Fin▹ℕ)
open import Data.Vec using (Vec; []; _∷_; replicate; tabulate; allFin; reverse; _⊛_; toList) renaming (map to vmap)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.String  using (String) renaming (_++_ to _++ˢ_)
open import Agda.Builtin.Reflection -- using (Visibility; Pattern)
open import Reflection.NP
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat.Param.Binary
open import Reflection.Param.Env

module Reflection.Param where

-- Local "imports" to avoid depending on nplib
private
  postulate
    hide : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
    -- hide-rule : ∀ {x} y → hide x y ≡ y

  Endo : Set → Set
  Endo A = A → A

infix 0 `_

`_ : ∀ {A} → List A → Endo (List A)
(` xs) ys = xs ++ ys

app-tabulate : ∀ {n a} {A : Set a} → (Fin n → A) → List A → List A
app-tabulate {zero}  f xs = xs
app-tabulate {suc n} f xs = f zero ∷ app-tabulate (f ∘ suc) xs

allVarsFrom : ∀ n → ℕ → Vec Term n
allVarsFrom zero    k = []
allVarsFrom (suc n) k = var (k + n) [] ∷ allVarsFrom n k

pattern `⟦zero⟧  = con (quote ⟦ℕ⟧.⟦zero⟧) []
pattern `⟦suc⟧ t = con (quote ⟦ℕ⟧.⟦suc⟧)  (argᵛʳ t ∷ [])

pNat : ℕ → Term
pNat zero    = `⟦zero⟧
pNat (suc n) = `⟦suc⟧ (pNat n)

lam^ : ℕ → String → Visibility → Term → Term
lam^ n' s v = go 0 n'
  where
    go : (i n : ℕ) → Term → Term
    go i zero    t = t
    go i (suc n) t = lam v (abs (s ++ˢ showNat i) (go (suc i) n t))
  {-
lam^ zero    s v x = x
lam^ (suc n) s v x = lam v (abs s (lam^ n s v x))
-}

lam∈ : ∀ {n} → String → Env' n → (f : Env' n → Vec Term n → Term) → Term
lam∈ {n} s Γ f = lam^ n s visible (f (Γ +' n) (reverse (tabulate (λ n → var (Fin▹ℕ n) []))))

target-visibility : Visibility → Visibility
target-visibility _ = visible
-- target-visibility v = v

hint : String → String
hint "_" = "x"
hint  s  =  s

hintᵢ : String → String
hintᵢ s = hint s ++ˢ "ᵢ"

hintᵢ' : ℕ → String → String
hintᵢ' k s = hintᵢ s ++ˢ showNat k

hintᵣ : String → String
hintᵣ s = hint s ++ˢ "ᵣ"

hintₖ : String → String
hintₖ s = hint s ++ˢ "ₖ"

hintₖ' : ℕ → String → String
hintₖ' k s = hintₖ s ++ˢ showNat k

-- Add 'n' hidden args then one visible arg, then the rest of given args
pArgs^ : ∀ {n} {A : Set} → ArgInfo → (Fin n → A) → A → List (Arg A) → List (Arg A)
pArgs^ (arg-info v (modality r _)) f x args =
  app-tabulate (arg (argiʰω r) ∘ f) --<-- to be synced with pEnvPat +1/+↑
    (argʳ (target-visibility v) x ∷ args)

p^lam : Visibility → String → ℕ → Term → Term
p^lam v s n t = lam^ n (hintᵢ s) hidden
                 (lam (target-visibility v) (abs (hintᵣ s) t))

module _ {n} (Γ : Env' n) where
    pPi∈ⁿ : ∀ (s     : String)
              (i     : ArgInfo)
              (ty    : Type)
              (t₀ t₁ : Env' n → Vec Term n → Type) → Term
    pPi∈ⁿ s (arg-info v (modality r _)) ty t₀ t₁ = go Γ 0 (allFin n)
      where
      -- Add 'n' hidden arguments and one visible argument
      -- for the relation between the 'n' firsts.
      go : ∀ {m} → Env' n → ℕ → Vec (Fin n) m → Type
      go Δ k [] =
          `Π (argʳ (target-visibility v) (t₀ Δ (allVarsFrom n 0)))
             (abs (hintᵣ s) (t₁ (Γ +↑) (allVarsFrom n 1)))
      go Δ k (i ∷ is) =
          `Π (arg (argiʰω r) (mapTermVarᵢ Δ i ty))
             (abs (hintᵢ' k s) (go (Δ +1) (suc k) is))

pAppⁿ : ∀ n (v : Visibility)(a tᵢ : Term) → Term
pAppⁿ n v a tᵢ = app (raiseTerm (suc n) a) (argʳ v tᵢ ∷ [])

----------------
--- Sorts ---
----------------

pSort∈ : ∀ {n} → Sort → Vec Term n → Type
pSort∈ s = go 0
  where
    go : ℕ → ∀ {n} → Vec Term n → Type
    go k []       = agda-sort s
    go k (t ∷ ts) = `Πᵛʳ (raiseTerm k t)
                         (abs (hintₖ' k "A") (go (suc k) ts))

----------------
--- Patterns ---
----------------

EnvPat = ∀ {n} → Env' n → Env' n

pEnvPats : Pats    → EnvPat
pEnvPat  : Pattern → EnvPat

pEnvPat (con _ pats) = pEnvPats pats -- ∘ _+ʷ -- WRONG but try _+ʷ ∘ pEnvPats pats
pEnvPat (var _)      = _+↑ -- _+1
pEnvPat (dot t)      = hide "pEnvPats/dot" id -- WRONG
pEnvPat (lit _)      = id
pEnvPat (proj _)     = hide "pEnvPats/proj" id
pEnvPat (absurd n)   = id

pEnvPats [] = id
pEnvPats (arg i p ∷ ps) = pEnvPats ps ∘ pEnvPat p

module _ {n} (Γ : Env' n) where
    PPat = Endo Pats

    pPatCon : ArgInfo → Name → Pattern → Pats → PPat
    pPatCon i c p pats
      = pArgs^ {n} i (const p) (pConP Γ c pats)

    pPatℕ : ArgInfo → ℕ → PPat
    pPatℕ i zero    = pPatCon i (quote ℕ.zero) (dot unknown) []
    pPatℕ i (suc l) = pPatCon i (quote ℕ.suc)  (dot unknown) (pPatℕ i l [])

    pPats : Pats        → PPat
    pPat  : Arg Pattern → PPat

    pPat (arg i (con c pats))
      = pPatCon i c (dot unknown) (pPats pats [])
    pPat (arg i (dot t))
      = pArgs^ {n} i (const (dot unknown)) (dot unknown)
    pPat (arg i (var x))
      = pArgs^ {n} i (λ j → var (Fin▹ℕ j)) (var x)
    pPat (arg i (lit (nat n)))
      = pPatℕ i n
    pPat (arg i (lit l))
      = pArgs^ {n} i pLitArg (con (quote refl) [])
          where
            pLitArg : ∀ {n} → Fin n → Pattern
            pLitArg zero    = lit l
            pLitArg (suc _) = dot unknown
    pPat (arg i (absurd x))   = pArgs^ {n} i (const (lit (nat 42))) (absurd x) -- TODO fix 42
    pPat (arg i (proj p)) = hide "pPat/proj" id

    pPats []         = id
    pPats (pat ∷ ps) = pPat pat ∘ pPats ps

pLit : Literal → Term
pLit (nat n) = pNat n
pLit _       = con (quote refl) []

module _ {n} where
    pTerm    : (Γ : Env' n) → Term      → Term
    pArgs    : (Γ : Env' n) → Args Term → Args Term
    pClause  : (Γ : Env' n) → Clause    → Clause
    pClauses : (Γ : Env' n) → Clauses   → Clauses
    pTerm∈   : (Γ : Env' n) → Term                     → Vec Term n → Term
    pPi∈     : (Γ : Env' n) → String → Arg Type → Type → Vec Term n → Term

    pTerm Γ (lam v (abs s t)) = p^lam v s n (pTerm (Γ +↑) t)
    pTerm Γ (var  v args)     = var (pVarᵣ Γ v) (pArgs Γ args)
    pTerm Γ (con  c args)     = pConT Γ c (pArgs Γ args)
    pTerm Γ (def  d args)     = def (pDef Γ d) (pArgs Γ args)
    pTerm Γ (lit l)           = pLit l
    pTerm Γ (agda-sort s)          = lam∈ "Aₖ" Γ λ _ → pSort∈ s
    pTerm Γ (pi t (abs s u))  = lam∈ (hintₖ s) Γ λ Δ → pPi∈ Δ s t u
    pTerm Γ (pat-lam cs args) = pat-lam (pClauses Γ cs) (pArgs Γ args)
    pTerm Γ (meta m args)     = unknown -- ??? newMeta λ m → meta m (pArgs Γ args)
    pTerm Γ unknown           = unknown

    pPi∈ Γ s (arg (arg-info v r) t) u as =
      pPi∈ⁿ Γ s (arg-info v r) t (λ Δ → pTerm∈ Δ t) λ Δ vs →
        pTerm∈ Δ u
          (vmap (pAppⁿ n v) as ⊛ vs)

    pTerm∈ Γ (agda-sort s)         = pSort∈ s
    pTerm∈ Γ (pi t (abs s u)) = pPi∈ Γ s t u
    pTerm∈ Γ t                = app (pTerm Γ t) ∘ toList ∘ vmap argᵛʳ -- <--- visible ?

    pArgs Γ [] = []
    pArgs Γ (arg i t ∷ as)
      = pArgs^ i (λ i → mapTermVarᵢ Γ i t) (pTerm Γ t) (pArgs Γ as)

    pClause Γ (clause tel pats body)   = clause tel (pPats Γ pats []) (pTerm (pEnvPats pats Γ) body)
    pClause Γ (absurd-clause tel pats) = absurd-clause tel (pPats Γ pats [])

    pClauses Γ []       = []
    pClauses Γ (c ∷ cs) = pClause Γ c ∷ pClauses Γ cs

module _ {n} (Γ : Env' n) where
    pType : (t : Term) (typeof-t : Type) → Type
    pType t typeof-t = pTerm∈ Γ typeof-t (replicate n t)

    pDefinitionClauses : Definition → Clauses
    pDefinitionClauses (function cs) = pClauses Γ cs
    pDefinitionClauses _ = hide "pDefinitionClauses" []

    param-type-by-name : Name → TC Type
    param-type-by-name d = mapTC (pType (def d [])) (getType d)

    param-clauses-by-name : Name → TC Clauses
    param-clauses-by-name d = mapTC pDefinitionClauses (getDefinition d)

    param-term-by-name : Name → TC Term
    param-term-by-name = mapTC (pTerm Γ) ∘ Get-term.from-name

pTerm^ : ∀ (k : ℕ) {n} (Γ : Env' n) → Term → Term
pTerm^ zero    Γ t = t
pTerm^ (suc k) Γ t = pTerm Γ (pTerm^ k Γ t)

-- Not sure
pType^ : ∀ (k : ℕ) {n} (Γ : Env' n) → (t : Term) (typeof-t : Type) → Type
pType^ zero    Γ t typeof-t = typeof-t
pType^ (suc k) Γ t typeof-t = pType^ k Γ (pTerm Γ t) (pType Γ t typeof-t)

module _ (k : ℕ) {n} (Γ : Env' n) where
    param-term-by-name^ : Name → TC Term
    param-term-by-name^ = mapTC (pTerm^ k Γ) ∘ Get-term.from-name

    -- When k=1 we can use `def n []` instead of `Get-term.from-name`
    -- The issue is that the `app` function does not do hereditary substition.
    param-type-by-name^ : Name → TC Type
    param-type-by-name^ n = bindTC (Get-term.from-name n) (λ tm → mapTC (pType^ k Γ tm) (getType n))

param-rec-clauses-by-name : ∀ {n} → Env' n → (x xₚ : Name) → TC Clauses
param-rec-clauses-by-name Γ x xₚ = param-clauses-by-name (extDefEnv [ x ≔ xₚ ] Γ) x

param-def-by-name-dbg : ∀ {n} → Env' n → (x xₚ : Name) → TC 𝟙
param-def-by-name-dbg Γ x xₚ =
  param-rec-clauses-by-name Γ x xₚ >>= λ cs →
  withNormalisation 1₂ (quoteTC cs) >>= λ qcs → typeError (termErr qcs ∷ [])

param-def-by-name : ∀ {n} → Env' n → (x xₚ : Name) → TC 𝟙
param-def-by-name Γ x xₚ =
  param-rec-clauses-by-name Γ x xₚ >>= λ cs →
  defineFun xₚ cs

param-decl-by-name : ∀ {n} → Env' n → (x xₚ : Name) → TC 𝟙
param-decl-by-name Γ x xₚ =
  param-type-by-name Γ x >>= λ t →
  declareDef (argᵛʳ xₚ) t >>
  param-def-by-name Γ x xₚ

param-ctor-by-name : ∀ {n} → Env' n → (c : Name) → TC Type
param-ctor-by-name Γ c = mapTC (pType Γ (con c [])) (getType c)
-- -}
-- -}
-- -}
-- -}
-- -}

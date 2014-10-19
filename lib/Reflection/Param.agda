open import Function
open import Data.Nat hiding (_≟_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin using (Fin; zero; suc) renaming (toℕ to Fin▹ℕ)
open import Data.Vec using (Vec; []; _∷_; replicate; tabulate; allFin; reverse; _⊛_; toList) renaming (map to vmap)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String  using (String) renaming (_++_ to _++ˢ_)
open import Reflection.NP
open import Relation.Nullary.NP
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat.Param.Binary

module Reflection.Param where

-- Local opaque function to avoid depending on nplib
module _ {a} {A : Set a} where
  postulate
    opaque : String → A → A
    opaque-rule : ∀ {s} x → opaque s x ≡ x

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

record Env (n : ℕ)(A B : Set) : Set where
  field
    pVarᵢ : Fin n → A → B
    pVarᵣ : A → B
    pCon : Name → Name
    pDef : Name → Name
open Env

Env' = λ n → Env n ℕ ℕ

ε-pVarᵢ : ∀ {n} → String → Fin n → ℕ → ℕ
ε-pVarᵢ = λ s i → opaque (s ++ˢ ".pVarᵢ " ++ˢ showNat (Fin▹ℕ i))

ε : ∀ n → Env' n
ε n = record { pVarᵢ = ε-pVarᵢ "ε"
             ; pVarᵣ = opaque "ε.pVarᵣ"
             ; pCon = opaque "ε.pCon"
             ; pDef = opaque "ε.pDef" }

extDefEnv : ((Name → Name) → (Name → Name)) → ∀ {n A B} → Env n A B → Env n A B
extDefEnv ext Γ = record Γ { pDef = ext (pDef Γ) }

extConEnv : ((Name → Name) → (Name → Name)) → ∀ {n A B} → Env n A B → Env n A B
extConEnv ext Γ = record Γ { pCon = ext (pCon Γ) }

[_≔_] : (old new : Name) (φ : Name → Name) → (Name → Name)
[ old ≔ new ] φ x = [yes: (λ _ → new) no: (λ _ → φ x) ]′ (x ≟-Name old)

↑pVar : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
↑pVar zero = id
↑pVar (suc n) = ↑pVar n ∘ mapVar↑'

on-pVar : ∀ {n A B C D}
            (fᵢ : Fin n → (A → B) → (C → D))
            (fᵣ : (A → B) → (C → D))
          → Env n A B → Env n C D
on-pVar fᵢ fᵣ Γ = record
  { pVarᵢ = λ i → fᵢ i (pVarᵢ Γ i)
  ; pVarᵣ = fᵣ (pVarᵣ Γ)
  ; pCon = pCon Γ
  ; pDef = pDef Γ }

_+↑ : ∀ {n} → Env' n → Env' n
_+↑ {n} = on-pVar goi gor
  where
    goi : Fin n → (ℕ → ℕ) → (ℕ → ℕ)
    goi x f = _+_ (n ∸ Fin▹ℕ x) ∘ ↑pVar 1 (_+_ (Fin▹ℕ x) ∘ f)

    gor : (ℕ → ℕ) → (ℕ → ℕ)
    gor f = ↑pVar 1 (_+_ n ∘ f)

_+'_ : ∀ {w} → Env' w → ℕ → Env' w
Γ +' n = record { pVarᵢ = λ i → _+_ n ∘ pVarᵢ Γ i
                ; pVarᵣ = _+_ n ∘ pVarᵣ Γ
                ; pCon = pCon Γ
                ; pDef = pDef Γ }

_+1 : ∀ {w} → Env' w → Env' w
Γ +1 = Γ +' 1

pattern `⟦zero⟧  = con (quote ⟦ℕ⟧.⟦zero⟧) []
pattern `⟦suc⟧ t = con (quote ⟦ℕ⟧.⟦suc⟧)  (argᵛʳ t ∷ [])

pNat : ℕ → Term
pNat zero    = `⟦zero⟧
pNat (suc n) = `⟦suc⟧ (pNat n)

lam^ : ℕ → String → Visibility → Term → Term
lam^ zero    s v x = x
lam^ (suc n) s v x = lam v (abs s (lam^ n s v x))

lam∈ : ∀ {n} → String → Env' n → (f : Env' n → Vec Term n → Term) → Term
lam∈ {n} s Γ f = lam^ n s visible (f (Γ +' n) (reverse (tabulate (λ n → var (Fin▹ℕ n) []))))

-- Add 'n' hidden args then one visible arg, then the rest of given args
pArgs^ : ∀ {n A} → Relevance → (Fin n → A) → A → List (Arg A) → List (Arg A)
pArgs^ r f x args = app-tabulate (argʰ r ∘ f) (argᵛʳ x ∷ args)

p^lam : String → ℕ → Term → Term
p^lam s n t = lam^ n s hidden (lam visible (abs s t))

pPi∈ⁿ : ∀ {n} (Γ : Env' n) (r : Relevance)
          (s   : Type)
          (t u : Env' n → Vec Term n → Type) → Term
pPi∈ⁿ {n} Γ r s t u = unEl (go Γ (allFin n))
  where
  -- Add 'n' implicit arguments and one explicit argument
  -- for the relation between the 'n' firsts.
  go : ∀ {m} → Env' n → Vec (Fin n) m → Type
  go Δ [] = 
      `Πᵛʳ (t Δ (allVarsFrom n 0)) (u (Γ +↑) (allVarsFrom n 1))
  go Δ (i ∷ is) =
      `Π (argʰ r (mapVarType (liftMapVar (pVarᵢ Δ i)) s))
         (go (Δ +1) is)
    
----------------
--- Sorts ---
----------------

pSort∈ : ∀ {n} → Sort → Vec Term n → Type
pSort∈ s = go 0
  where
    go : ℕ → ∀ {n} → Vec Term n → Type
    go k []       = el (suc-sort s) (sort s)
    go k (t ∷ ts) = `Πᵛʳ (mapVarType (liftMapVar (_+_ k)) (el s t)) (go (suc k) ts)
    
----------------
--- Patterns ---
----------------

EnvPat = ∀ {n} → Env' n → Env' n

pEnvPats : Pats    → EnvPat
pEnvPat  : Pattern → EnvPat

pEnvPat (con _ pats) = pEnvPats pats
pEnvPat dot          = id
pEnvPat (var _)      = _+↑
pEnvPat (lit _)      = id
pEnvPat (proj _)     = opaque "pEnvPats/proj" id
pEnvPat absurd       = id

pEnvPats [] = id
pEnvPats (arg i p ∷ ps) = pEnvPat p ∘ pEnvPats ps

module _ {n} (Γ : Env' n) where
    PPat = Endo Pats

    pPatCon : Arg-info → Name → Pats → PPat
    pPatCon (arg-info _ r) c pats
      = pArgs^ {n} r (const dot) (con (pCon Γ c) pats)

    pPatℕ : Arg-info → ℕ → PPat
    pPatℕ i zero    = pPatCon i (quote ℕ.zero) []
    pPatℕ i (suc l) = pPatCon i (quote ℕ.suc)  (pPatℕ i l [])

    pPats : Pats        → PPat
    pPat  : Arg Pattern → PPat

    pPat (arg i (con c pats))
      = pPatCon i c (pPats pats [])
    pPat (arg (arg-info _ r) dot)
      = pArgs^ {n} r (const dot) dot
    pPat (arg (arg-info _ r) (var s))
      = pArgs^ {n} r (const (var s)) (var s)
    pPat (arg i (lit (nat n)))
      = pPatℕ i n
    pPat (arg (arg-info _ r) (lit l))
      = pArgs^ {n} r pLitArg (con (quote refl) [])
          where
            pLitArg : ∀ {n} → Fin n → Pattern
            pLitArg zero    = lit l
            pLitArg (suc _) = dot
    pPat (arg (arg-info _ r) absurd) = pArgs^ {n} r (const (var "_")) absurd
    pPat (arg i (proj p))            = opaque "pPat/proj" id

    pPats []         = id
    pPats (pat ∷ ps) = pPat pat ∘ pPats ps

pLit : Literal → Term
pLit (nat n) = pNat n
pLit _       = con (quote refl) []

module _ {n} where
    pTerm    : (Γ : Env' n) → Term    → Term
    pArgs    : (Γ : Env' n) → Args    → Args
    pClause  : (Γ : Env' n) → Clause  → Clause
    pClauses : (Γ : Env' n) → Clauses → Clauses
    pType∈   : (Γ : Env' n) → Type                     → Vec Term n → Type
    pTerm∈   : (Γ : Env' n) → Term                     → Vec Term n → Term
    pPi∈     : (Γ : Env' n) → String → Arg Type → Type → Vec Term n → Term

    pTerm Γ (lam _ (abs s t)) = p^lam s n (pTerm (Γ +↑) t)
    pTerm Γ (var v args)      = var (pVarᵣ Γ v) (pArgs Γ args)
    pTerm Γ (con c args)      = con (pCon Γ c) (pArgs Γ args)
    pTerm Γ (def d args)      = def (pDef Γ d) (pArgs Γ args)
    pTerm Γ (lit l)           = pLit l
    pTerm Γ (sort s)          = lam∈ "A" Γ λ _ → unEl ∘ pSort∈ s
    pTerm Γ (pi t (abs s u))  = lam∈ s Γ λ Δ → pPi∈ Δ s t u
    pTerm Γ (pat-lam cs args) = pat-lam (pClauses Γ cs) (pArgs Γ args)
    pTerm Γ unknown           = unknown

    pPi∈ Γ s (arg (arg-info v r) t) u as =
      pPi∈ⁿ Γ r t (λ Δ → pType∈ Δ t) (λ Δ vs → pType∈ Δ u
        (vmap (λ a i → app (mapVarTerm (liftMapVar (_+_ (suc n))) a) (argʳ v i ∷ [])) as ⊛ vs))

    pTerm∈ Γ (sort s) = unEl ∘ pSort∈ s
    pTerm∈ Γ (pi t (abs s u)) = pPi∈ Γ s t u
    pTerm∈ Γ t                = app (pTerm Γ t) ∘ toList ∘ vmap argᵛʳ

    pType∈ Γ (el s t) = el s ∘ pTerm∈ Γ t

    pArgs Γ [] = []
    pArgs Γ (arg (arg-info _ r) t ∷ as)
      = pArgs^ r (λ i → mapVarTerm (liftMapVar (pVarᵢ Γ i)) t) (pTerm Γ t) (pArgs Γ as)

    pClause Γ (clause pats body)   = clause (pPats Γ pats []) (pTerm (pEnvPats pats Γ) body)
    pClause Γ (absurd-clause pats) = absurd-clause (pPats Γ pats [])

    pClauses Γ []       = []
    pClauses Γ (c ∷ cs) = pClause Γ c ∷ pClauses Γ cs

module _ {n} (Γ : Env' n) where
    pType : (t : Term) (typeof-t : Type) → Type
    pType t typeof-t = pType∈ Γ typeof-t (replicate t)

    pFunctionDef : Name → FunctionDef → FunctionDef
    pFunctionDef d (fun-def t cs)
      = fun-def (pType (def d []) t) (pClauses Γ cs)

    param-fun-def-by-name : Name → FunctionDef
    param-fun-def-by-name x with definition x
    ... | function d = pFunctionDef x d
    ... | _ = opaque "pFunName" unknown-fun-def

    param-type-by-name : Name → Type
    param-type-by-name d with definition d
    ... | function (fun-def ty _) = pType (def d []) ty
    ... | constructor′ = pType (con d []) (type d)
    ... | _ = opaque "param-type-by-name" unknown-type

    param-clauses-by-name : Name → Clauses
    param-clauses-by-name x with definition x
    ... | function (fun-def _ cs) = pClauses Γ cs
    ... | _ = []

    param-term-by-name : Name → Term
    param-term-by-name = pTerm Γ ∘ Get-term.from-name

pTerm^ : ∀ (k : ℕ) {n} (Γ : Env' n) → Term → Term
pTerm^ zero    Γ t = t
pTerm^ (suc k) Γ t = pTerm Γ (pTerm^ k Γ t)

-- Not sure
pType^ : ∀ (k : ℕ) {n} (Γ : Env' n) → (t : Term) (typeof-t : Type) → Type
pType^ zero    Γ t typeof-t = typeof-t
pType^ (suc k) Γ t typeof-t = pType^ k Γ (pTerm Γ t) (pType Γ t typeof-t)

module _ (k : ℕ) {n} (Γ : Env' n) where
    param-term-by-name^ : Name → Term
    param-term-by-name^ = pTerm^ k Γ ∘ Get-term.from-name

    -- When k=1 we can use `def n []` instead of `Get-term.from-name`
    -- The issue is that the `app` function does not do hereditary substition.
    param-type-by-name^ : Name → Type
    param-type-by-name^ n = pType^ k Γ (Get-term.from-name n) (type n)

pFunNameRec : ∀ {n} → Env' n → (x xₚ : Name) → FunctionDef
pFunNameRec Γ x xₚ = param-fun-def-by-name (extDefEnv [ x ≔ xₚ ] Γ) x

param-ctor-by-name : ∀ {n} → Env' n → (c : Name) → Type
param-ctor-by-name Γ c = pType Γ (con c []) (type c)

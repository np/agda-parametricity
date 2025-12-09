{-# OPTIONS --without-K #-}
module Reflection.NP where

open import Level
  renaming (zero to ₀; suc to ₛ)
open import Data.Nat
  using (ℕ; module ℕ; zero; suc; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.String using () renaming (_++_ to _++ˢ_)
open import Data.List
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Reflection
open import Data.Maybe hiding (_>>=_) renaming (map to map?)
open import Data.Vec.N-ary using (N-ary; N-ary-level)
open import Function

open import Reflection public

mapTC : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → TC A → TC B
mapTC f m = bindTC m λ x → returnTC (f x)

-- Local "imports" to avoid depending on nplib
private
  _→⟨_⟩_ : ∀ {a b} (A : Set a) (n : ℕ) (B : Set b) → Set (N-ary-level a b n)
  A →⟨ n ⟩ B = N-ary n A B

private
  postulate
    hide : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
    -- hide-rule : ∀ {x} y → hide x y ≡ y

-- lamᵛ : String → Term → Term
pattern lamᵛ s t = lam visible (abs s t)

-- lamʰ : String → Term → Term
pattern lamʰ s t = lam hidden (abs s t)

-- argiᵛ : Relevance → Quantity → ArgInfo
pattern argiᵛ r q = arg-info visible (modality r q)

-- argiᵛω : Relevance → ArgInfo
pattern argiᵛω r = argiᵛ r quantity-ω

-- argiʳ : Visibility → Quantity → ArgInfo
pattern argiʳ v q = arg-info v (modality relevant q)

-- argiʳω : Visibility → ArgInfo
pattern argiʳω v = argiʳ v quantity-ω

-- argiᵛʳ : Quantity → ArgInfo
pattern argiᵛʳ q = argiᵛ relevant q

-- argiᵛʳω : ArgInfo
pattern argiᵛʳω = argiᵛʳ quantity-ω

-- argiʰ : Relevance → Quantity → ArgInfo
pattern argiʰ r q = arg-info hidden (modality r q)

-- argiʰω : Relevance → ArgInfo
pattern argiʰω r = argiʰ r quantity-ω

-- argiʰʳ : Quantity → ArgInfo
pattern argiʰʳ q = argiʰ relevant q

-- argiʰʳω : ArgInfo
pattern argiʰʳω = argiʰʳ quantity-ω

-- argᵛ : ∀{A} → Relevance → A → Arg A
pattern argᵛ r v = arg (argiᵛω r) v

-- argᵛʳ : ∀{A} → Visibility → A → Arg A
pattern argʳ v x = arg (argiʳω v) x

-- argʰ : ∀{A} → Relevance → A → Arg A
pattern argʰ r v = arg (argiʰω r) v

-- argᵛʳ : ∀{A} → A → Arg A
pattern argᵛʳ v = arg argiᵛʳω v

-- argʰʳ : ∀{A} → A → Arg A
pattern argʰʳ v = arg argiʰʳω v

pattern conᵛ n r t = con n (argᵛ r t ∷ [])
pattern conʰ n r t = con n (argʰ r t ∷ [])
pattern defᵛ n r t = def n (argᵛ r t ∷ [])
pattern defʰ n r t = def n (argʰ r t ∷ [])

pattern conᵛʳ n t = con n (argᵛʳ t ∷ [])
pattern conʰʳ n t = con n (argʰʳ t ∷ [])
pattern defᵛʳ n t = def n (argᵛʳ t ∷ [])
pattern defʰʳ n t = def n (argʰʳ t ∷ [])

ArgInfos : Set
ArgInfos = List ArgInfo

app` : (Args Term → Term) → (ais : ArgInfos) → Term →⟨ length ais ⟩ Term
app` f = go [] where
  go : Args Term → (ais : ArgInfos) → Term →⟨ length ais ⟩ Term
  go args []         = f (reverse args)
  go args (ai ∷ ais) = λ t → go (arg ai t ∷ args) ais

con` : Name → (ais : ArgInfos) → Term →⟨ length ais ⟩ Term
con` x = app` (con x)

def` : Name → (ais : ArgInfos) → Term →⟨ length ais ⟩ Term
def` x = app` (def x)

var` : ℕ → (ais : ArgInfos) → Term →⟨ length ais ⟩ Term
var` x = app` (var x)

coe : ∀ {A : Set} {z : A} n → (Term →⟨ length (replicate n z) ⟩ Term) → Term →⟨ n ⟩ Term
coe zero    t = t
coe (suc n) f = λ t → coe n (f t)

con`ⁿʳ : Name → (n : ℕ) → Term →⟨ n ⟩ Term
con`ⁿʳ x n = coe n (app` (con x) (replicate n argiᵛʳω))

def`ⁿʳ : Name → (n : ℕ) → Term →⟨ n ⟩ Term
def`ⁿʳ x n = coe n (app` (def x) (replicate n argiᵛʳω))

var`ⁿʳ : ℕ → (n : ℕ) → Term →⟨ n ⟩ Term
var`ⁿʳ x n = coe n (app` (var x) (replicate n argiᵛʳω))

-- sort₀ : Sort
pattern sort₀ = lit 0

-- sort₁ : Sort
pattern sort₁ = lit 1

-- `Set_ : ℕ → Term
`Set_ : ℕ → Term
`Set_ i = agda-sort (lit i)

-- `Set₀ : Term
`Set₀ : Term
`Set₀ = `Set_ 0

-- `★_ : ℕ → Term
`★_ : ℕ → Term
`★_ i = agda-sort (lit i)

-- `★₀ : Term
`★₀ : Term
`★₀ = `★_ 0

unArg : ∀ {a} {A : Set a} → Arg A → A
unArg (arg _ x) = x

unAbs : ∀ {a} {A : Set a} → Abs A → A
unAbs (abs _ x) = x

-- `Level : Term
pattern `Level = def (quote Level) []

pattern `₀ = def (quote ₀) []

pattern `ₛ_ v = def (quote ₛ) (argᵛʳ v ∷ [])

-- `suc-agda-sort : Sort → Sort
pattern `suc-agda-sort s = set (`ₛ (agda-sort s))

pattern `set₀ = set `₀
pattern `setₛ_ s = set (`ₛ s)
pattern `set_ s = set (agda-sort s)

suc-agda-sort : Sort → Sort
suc-agda-sort (set t) = set (`ₛ t)
suc-agda-sort (lit n) = lit (suc n)
suc-agda-sort (prop t) = prop (`ₛ t)
suc-agda-sort (propLit n) = propLit (suc n)
suc-agda-sort (inf n) = inf (suc n)
suc-agda-sort unknown = unknown

decode-Sort : Sort → Maybe ℕ
decode-Sort `set₀ = just zero
decode-Sort (`setₛ_ s) = map? suc (decode-Sort (set s))
decode-Sort (`set_ s) = decode-Sort s
decode-Sort (set _) = nothing
decode-Sort (lit n) = just n
decode-Sort (prop _) = nothing
decode-Sort (propLit n) = just n
decode-Sort (inf n) = just n
decode-Sort unknown = nothing

pattern _`⊔_ s₁ s₂ = set (def (quote _⊔_) (argᵛʳ (agda-sort s₁) ∷ argᵛʳ (agda-sort s₂) ∷ []))

_`⊔`_ : Sort → Sort → Sort
s₁ `⊔` s₂ with decode-Sort s₁ | decode-Sort s₂
...          | just n₁        | just n₂        = lit (n₁ ⊔ℕ n₂)
...          | _              | _              = s₁ `⊔ s₂

record MapVar : Set where
  field
    onVar  : ℕ → ℕ
    onDef  : Name → Name
    onCon  : Name → Name
    onPrj  : Name → Name
    onMeta : Meta → Meta
    onStr  : String → String
open MapVar public

idMapVar : MapVar
idMapVar = record { onVar = id; onDef = id; onCon = id; onMeta = id; onPrj = id; onStr = id }

liftMapVar : (ℕ → ℕ) → MapVar
liftMapVar f = record idMapVar { onVar = f }

mapVar↑' : (ℕ → ℕ) → (ℕ → ℕ)
mapVar↑' f zero    = zero
mapVar↑' f (suc n) = suc (f n)

mapVar↑ : MapVar → MapVar
mapVar↑ Γ = record Γ { onVar = mapVar↑' (onVar Γ) }

Pats = List (Arg Pattern)

mapVarTerm     : MapVar → Term → Term
mapVarArgsTerm : MapVar → Args Term → Args Term
mapVarArgsName : MapVar → Args Name → Args Name
mapVarSort     : MapVar → Sort → Sort
mapVarAbsTerm  : MapVar → Abs Term → Abs Term
mapVarClause   : MapVar → Clause → Clause
mapVarClauses  : MapVar → Clauses → Clauses
mapVarPattern  : MapVar → Pattern → Pattern
mapVarPatterns : MapVar → Pats → Pats

mapVarPattern Γ (con c ps) = con (onCon Γ c) (mapVarPatterns Γ ps)
mapVarPattern Γ (dot t) = dot (mapVarTerm Γ t)
mapVarPattern Γ (var n) = var (onVar Γ n)
mapVarPattern Γ (lit l) = lit l
mapVarPattern Γ (proj p) = proj (onPrj Γ p)
mapVarPattern Γ (absurd n) = absurd (onVar Γ n)

mapVarPatterns Γ [] = []
mapVarPatterns Γ (arg i p ∷ ps) = arg i (mapVarPattern Γ p) ∷ mapVarPatterns Γ ps

mapVarTerm Γ (var x args)  = var (onVar Γ x)   (mapVarArgsTerm Γ args)
mapVarTerm Γ (con c args)  = con (onCon Γ c)   (mapVarArgsTerm Γ args)
mapVarTerm Γ (def d args)  = def (onDef Γ d)   (mapVarArgsTerm Γ args)
mapVarTerm Γ (meta m args) = meta (onMeta Γ m) (mapVarArgsTerm Γ args)
mapVarTerm Γ (lam v t) = lam v (mapVarAbsTerm Γ t)
mapVarTerm Γ (pat-lam cs args) = pat-lam (mapVarClauses Γ cs) (mapVarArgsTerm Γ args)
mapVarTerm Γ (pi (arg i t₁) t₂) = pi (arg i (mapVarTerm Γ t₁)) (mapVarAbsTerm Γ t₂)
mapVarTerm Γ (agda-sort x) = agda-sort (mapVarSort Γ x)
mapVarTerm Γ (lit x) = lit x
mapVarTerm Γ unknown = unknown

mapVarClause Γ (clause tel pats body) = clause tel (mapVarPatterns Γ pats) (mapVarTerm Γ body)
mapVarClause Γ (absurd-clause tel pats) = absurd-clause tel (mapVarPatterns Γ pats)

mapVarClauses Γ [] = []
mapVarClauses Γ (c ∷ cs) = mapVarClause Γ c ∷ mapVarClauses Γ cs

mapVarAbsTerm Γ (abs s x) = abs (onStr Γ s) (mapVarTerm (mapVar↑ Γ) x)

mapVarArgsTerm Γ [] = []
mapVarArgsTerm Γ (arg i x ∷ args) = arg i (mapVarTerm Γ x) ∷ mapVarArgsTerm Γ args

mapVarArgsName Γ [] = []
mapVarArgsName Γ (arg i x ∷ args) = arg i (onPrj Γ x) ∷ mapVarArgsName Γ args

mapVarSort Γ (set t) = set (mapVarTerm Γ t)
mapVarSort Γ (lit n) = lit n
mapVarSort Γ (prop t) = prop (mapVarTerm Γ t)
mapVarSort Γ (propLit n) = propLit n
mapVarSort Γ (inf n) = inf n
mapVarSort Γ unknown = unknown

module _ (Γ : MapVar) where
  mapVarDefinition : Definition → Definition
  mapVarDefinition (function cs) = function (mapVarClauses Γ cs)
  mapVarDefinition (data-type pars cs) = data-type pars cs
  mapVarDefinition (record-type x args) = record-type x (mapVarArgsName Γ args)
  mapVarDefinition (data-cons x q) = data-cons x q
  mapVarDefinition axiom = axiom
  mapVarDefinition prim-fun = prim-fun

raiseMapVar : ℕ → MapVar
raiseMapVar k = liftMapVar (_+_ k)

raiseTerm : ℕ → Term → Term
raiseTerm = mapVarTerm ∘ raiseMapVar

raiseArgs : ℕ → Args Term → Args Term
raiseArgs = mapVarArgsTerm ∘ raiseMapVar

noHintsMapVar : MapVar
noHintsMapVar = record idMapVar { onStr = const "_" }

noHintsTerm : Term → Term
noHintsTerm = mapVarTerm noHintsMapVar

noHintsDefinition : Definition → Definition
noHintsDefinition = mapVarDefinition noHintsMapVar

noAbsTerm : Term → Abs Term
noAbsTerm = abs "_" ∘ raiseTerm 1

pattern piᵛʳ s t u = pi (argᵛʳ t) (abs s u)
pattern piʰʳ s t u = pi (argʰʳ t) (abs s u)

`Π : Arg Type → Abs Type → Type
`Π = pi

`Πᵛʳ : Type → Abs Type → Type
`Πᵛʳ t u = `Π (argᵛʳ t) u

`Πʰʳ : Type → Abs Type → Type
`Πʰʳ t u = `Π (argʰʳ t) u

_`→_ : Arg Type → Type → Type
t `→ u = `Π t (noAbsTerm u)

_`→ʰʳ_ : Type → Type → Type
t `→ʰʳ u = `Πʰʳ t (noAbsTerm u)

_`→ᵛʳ_ : Type → Type → Type
t `→ᵛʳ u = `Πᵛʳ t (noAbsTerm u)

`Πⁿ : List (Arg Type) → Type → Type
`Πⁿ []       u = u
`Πⁿ (t ∷ ts) u = `Π t (abs "_" (`Πⁿ ts u))

`Πᵛʳⁿ : List Type → Type → Type
`Πᵛʳⁿ ts u = `Πⁿ (map argᵛʳ ts) u

`Πʰʳⁿ : List Type → Type → Type
`Πʰʳⁿ ts u = `Πⁿ (map argʰʳ ts) u

-- η vs mk: performs no shifting of the result of mk.
-- Safe values of mk are def and con for instance
η : List ArgInfo → (Args Term → Term) → Term
η ais₀ mk = go ais₀ where
  vars : List ArgInfo → Args Term
  vars []         = []
  vars (ai ∷ ais) = arg ai (var (length ais) []) ∷ vars ais
  go : List ArgInfo → Term
  go []                   = mk (vars ais₀)
  go (arg-info v _ ∷ ais) = lam v (abs "_" (go ais))

ηʰ : ℕ → (Args Term → Term) → Term
ηʰ n = η (replicate n argiʰʳω)

ηᵛ : ℕ → (Args Term → Term) → Term
ηᵛ n = η (replicate n argiᵛʳω)

ηʰⁿ : ℕ → Name → Term
ηʰⁿ n = ηʰ n ∘ def

ηᵛⁿ : ℕ → Name → Term
ηᵛⁿ n = ηᵛ n ∘ def

argInfos : Term → List ArgInfo

argInfos (pi (arg ai _) (abs _ t)) = ai ∷ argInfos t

-- no more arguments
argInfos (var _ _) = []
argInfos (agda-sort s)  = []

-- TODO
argInfos (def f args) = []

-- fail
argInfos unknown      = []
argInfos (meta _ _)   = []

-- absurd/ill-typed cases
argInfos (con c args)  = []
argInfos (lit _)       = []
argInfos (lam _ _)     = []
argInfos (pat-lam _ _) = []

arity : Term → ℕ
arity = length ∘ argInfos

ηⁿ : Name → TC Term
ηⁿ nm = mapTC (λ ty → η (argInfos ty) (def nm)) (getType nm)

data AbsTerm : Set where
  var : ℕ → AbsTerm
  []  : AbsTerm
  _,_ : AbsTerm → AbsTerm → AbsTerm
  abs : String → AbsTerm → AbsTerm

_,,_ : AbsTerm → AbsTerm → AbsTerm
[]      ,, x  = x
x       ,, [] = x
(x , y) ,, z  = x ,, (y ,, z)
x       ,, y  = x , y

abs' : String → AbsTerm → AbsTerm
abs' _ [] = []
abs' s x  = abs s x

absTerm : Term → AbsTerm
absArgs : Args Term → AbsTerm
absSort : Sort → AbsTerm

absTerm (var  x args) = var x ,, absArgs args
absTerm (con  c args) = absArgs args
absTerm (def  f args) = absArgs args
absTerm (meta m args) = absArgs args
absTerm (lam v (abs s t)) = abs' s (absTerm t)
absTerm (pat-lam cs args) = hide "absTm/pat-lam" []
absTerm (pi (arg _ t₁) (abs s t₂)) = absTerm t₁ ,, abs' s (absTerm t₂)
absTerm (agda-sort x) = absSort x
absTerm (lit x) = []
absTerm unknown = []

absArgs [] = []
absArgs (arg i x ∷ as) = absTerm x ,, absArgs as

absSort (set t) = absTerm t
absSort (lit n) = []
absSort (prop t) = absTerm t
absSort (propLit n) = []
absSort (inf n) = []
absSort unknown = []

app : Term → Args Term → Term
app (var  x args) args₁ = var  x (args ++ args₁)
app (con  c args) args₁ = con  c (args ++ args₁)
app (def  f args) args₁ = def  f (args ++ args₁)
app (meta m args) args₁ = meta m (args ++ args₁)
app (lam v t)         _ = hide "app/lam"               (lam v t)
app (pat-lam cs args) _ = hide "app/pat-lam"           (pat-lam cs args)
app (pi t₁ t₂)        _ = hide "app/pi (type-error)"   (pi t₁ t₂)
app (agda-sort x)          _ = hide "app/agda-sort (type-error)" (agda-sort x)
app (lit x)           _ = hide "app/lit (type-error)"  (lit x)
app unknown           _ = unknown

pattern `ℕ     = def (quote ℕ) []
pattern `zero  = con (quote ℕ.zero) []
pattern `suc t = conᵛʳ (quote ℕ.suc) t

quoteNat : ℕ → Term
quoteNat zero    = `zero
quoteNat (suc n) = `suc (quoteNat n)

unlit : Literal → Term
unlit (nat x) = quoteNat x
unlit x = lit x

unknown-definition : Definition
unknown-definition = hide "unknown-definition" axiom

module Map-arg-info (f : ArgInfo → ArgInfo) where

    On : Set → Set
    On T = T → T

    -- Mutual declarations
    pat : On Pattern
    pats : On (List (Arg Pattern))
    term : On Term
    årgs : On (Args Term)
    sørt : On Sort
    clåuse  : On Clause
    clåuses : On (List Clause)

    -- Definitions
    pat (con c ps) = con c (pats ps)
    pat (dot t) = dot (term t)
    pat (var n) = (var n)
    pat (lit l) = lit l
    pat (proj p) = proj p
    pat (absurd n) = absurd n

    pats [] = []
    pats (arg i p ∷ ps) = arg (f i) (pat p) ∷ pats ps

    term (var  x args) = var  x (årgs args)
    term (con  c args) = con  c (årgs args)
    term (def  f args) = def  f (årgs args)
    term (meta m args) = meta m (årgs args)
    term (lam v (abs s t)) = case f (arg-info v (modality relevant quantity-ω{- arbitrary choice -})) of λ
                              { (arg-info v' _) → lam v' (abs s (term t)) }
    term (pat-lam cs args) = pat-lam (clåuses cs) (årgs args)
    term (pi (arg i t₁) (abs s t₂)) = pi (arg (f i) (term t₁)) (abs s (term t₂))
    term (agda-sort s) = agda-sort (sørt s)
    term (lit l) = lit l
    term unknown = unknown

    årgs [] = []
    årgs (arg i t ∷ args) = arg (f i) (term t) ∷ årgs args

    sørt (set t) = set (term t)
    sørt (lit n) = lit n
    sørt (prop t) = prop (term t)
    sørt (propLit n) = propLit n
    sørt (inf n) = inf n
    sørt unknown = unknown

    clåuse (clause tel ps body) = clause tel (pats ps) (term body)
    clåuse (absurd-clause tel ps) = absurd-clause tel (pats ps)

    clåuses [] = []
    clåuses (x ∷ cs) = clåuse x ∷ clåuses cs

    dëf : Definition → Definition
    dëf (function cs) = function (clåuses cs)
    dëf (data-type pars cs) = hide "Map-arg-info.dëf/data-type" unknown-definition
    dëf (record-type _ _) = hide "Map-arg-info.dëf/record-type" unknown-definition
    dëf (data-cons x q) = hide "Map-arg-info.dëf/data-cons" unknown-definition
    dëf axiom = hide "Map-arg-info.dëf/axiom" unknown-definition
    dëf prim-fun = hide "Map-arg-info.dëf/prim-fun" unknown-definition

    nåme : Name → TC Definition
    nåme = mapTC dëf ∘ getDefinition

reveal-arg : ArgInfo → ArgInfo
reveal-arg (arg-info v r) = arg-info visible r

module Reveal-args = Map-arg-info reveal-arg

module Get-clauses where
    from-def : Definition → Clauses
    from-def (function cs) = cs
    from-def (data-type pars cs) = hide "Get-clauses.from-def/data-type" []
    from-def (record-type _ _) = hide "Get-clauses.from-def/record-type" []
    from-def (data-cons x q) = hide "Get-clauses.from-def/data-cons" []
    from-def axiom = hide "Get-clauses.from-def/axiom" []
    from-def prim-fun = hide "Get-clauses.from-def/prim-fun" []

    from-name : Name → TC Clauses
    from-name n = mapTC from-def (getDefinition n)

module Get-term where
    from-clause : Clause → Term
    from-clause (clause tel [] body) = body
    from-clause (clause tel (arg (arg-info v _) (var n) ∷ pats) body)
      = lam v (abs ("x" ++ˢ showNat n) (from-clause (clause [] pats body)))
    from-clause _ = unknown

    from-clauses : Clauses → Term
    from-clauses (c ∷ []) = from-clause c
    from-clauses _ = hide "Get-term.from-clauses" unknown

    from-def : Definition → Term
    from-def (function cs) = from-clauses cs
    from-def (data-type pars cs) = unknown
    from-def (record-type _ _) = unknown
    from-def (data-cons x q) = unknown
    from-def axiom = unknown
    from-def prim-fun = unknown

    from-name : Name → TC Term
    from-name n = mapTC from-def (getDefinition n)

-- Given a type `tyH` with potential hidden arguments, this module builds
-- a function from `tyH` to `tyE` with is `tyH` with explicit arguments
-- instead.
module Revelator (tyH : Type) where
    tyE : Type
    tyE = Reveal-args.term tyH
    tyF : Type
    tyF = tyH `→ᵛʳ tyE
    tm : Term → ℕ → Args Term → Term
    tm (pi (arg i t₁) (abs s t₂)) y args
      = lamᵛ s (tm t₂ (suc y) (raiseArgs 1 args ++ arg i (var 0 []) ∷ []))
    tm (var x  args) = var
    tm (def f  args) = var
    tm (meta m args) = var
    tm (agda-sort s)      = var
    tm unknown _ _ = unknown
    tm (con c args) _ _ = hide "revealator/tm/con: impossible" unknown
    tm (lam v ty) _ _ = hide "revealator/tm/lam: impossible" unknown
    tm (lit l) _ _ = hide "revealator/tm/lit: impossible" unknown
    tm (pat-lam cs args) _ _ = hide "revealator/tm/pat-lam: TODO" unknown
    term : Term
    term = lamᵛ "_" (tm tyH 0 [])
    clauses : Clauses
    clauses = clause [] [] term ∷ []

revelator-by-name : (source dest : Name) → TC ⊤
revelator-by-name source dest = bindTC (getType source) (defineFun dest ∘ Revelator.clauses)

-- A test
private
    revelator-id : ({a : Level} {A : Set a} (x : A) → A)
                 →  (a : Level) (A : Set a) (x : A) → A
    unquoteDef revelator-id = revelator-by-name (quote id) revelator-id

-- -}
-- -}
-- -}
-- -}

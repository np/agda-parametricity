{-# OPTIONS --without-K #-}
module Reflection.NP where

open import Level
  renaming (zero to ₀; suc to ₛ)
open import Data.Nat
  using (ℕ; module ℕ; zero; suc; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.List
open import Data.String.Base using (String)
open import Data.Maybe renaming (map to map?)
open import Data.Vec.N-ary using (N-ary; N-ary-level)
open import Function

open import Reflection public

-- Local "imports" to avoid depending on nplib
private
  _→⟨_⟩_ : ∀ {a b} (A : Set a) (n : ℕ) (B : Set b) → Set (N-ary-level a b n)
  A →⟨ n ⟩ B = N-ary n A B
  
  postulate
    opaque : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
    -- opaque-rule : ∀ {x} y → opaque x y ≡ y

Args : Set
Args = List (Arg Term)

-- lamᵛ : String → Term → Term
pattern lamᵛ s t = lam visible (abs s t)

-- lamʰ : String → Term → Term
pattern lamʰ s t = lam hidden (abs s t)

-- argiᵛ : Relevance → Arg-info
pattern argiᵛ x = arg-info visible x

-- argiʳ : Visibility → Arg-info
pattern argiʳ x = arg-info x relevant

-- argiᵛʳ : Arg-info
pattern argiᵛʳ = argiᵛ relevant

-- argiʰ : Relevance → Arg-info
pattern argiʰ x = arg-info hidden x

-- argiʰʳ : Arg-info
pattern argiʰʳ = argiʰ relevant

-- argᵛ : ∀{A} → Relevance → A → Arg A
pattern argᵛ r v = arg (argiᵛ r) v

-- argᵛʳ : ∀{A} → Visibility → A → Arg A
pattern argʳ v x = arg (argiʳ v) x

-- argʰ : ∀{A} → Relevance → A → Arg A
pattern argʰ r v = arg (argiʰ r) v

-- argᵛʳ : ∀{A} → A → Arg A
pattern argᵛʳ v = arg argiᵛʳ v

-- argʰʳ : ∀{A} → A → Arg A
pattern argʰʳ v = arg argiʰʳ v

pattern conᵛ n r t = con n (argᵛ r t ∷ [])
pattern conʰ n r t = con n (argʰ r t ∷ [])
pattern defᵛ n r t = def n (argᵛ r t ∷ [])
pattern defʰ n r t = def n (argʰ r t ∷ [])

pattern conᵛʳ n t = con n (argᵛʳ t ∷ [])
pattern conʰʳ n t = con n (argʰʳ t ∷ [])
pattern defᵛʳ n t = def n (argᵛʳ t ∷ [])
pattern defʰʳ n t = def n (argʰʳ t ∷ [])

Arg-infos : Set
Arg-infos = List Arg-info

app` : (Args → Term) → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
app` f = go [] where
  go : Args → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
  go args []         = f (reverse args)
  go args (ai ∷ ais) = λ t → go (arg ai t ∷ args) ais

con` : Name → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
con` x = app` (con x)

def` : Name → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
def` x = app` (def x)

var` : ℕ → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
var` x = app` (var x)

coe : ∀ {A : Set} {z : A} n → (Term →⟨ length (replicate n z) ⟩ Term) → Term →⟨ n ⟩ Term
coe zero    t = t
coe (suc n) f = λ t → coe n (f t)

con`ⁿʳ : Name → (n : ℕ) → Term →⟨ n ⟩ Term
con`ⁿʳ x n = coe n (app` (con x) (replicate n argiᵛʳ))

def`ⁿʳ : Name → (n : ℕ) → Term →⟨ n ⟩ Term
def`ⁿʳ x n = coe n (app` (def x) (replicate n argiᵛʳ))

var`ⁿʳ : ℕ → (n : ℕ) → Term →⟨ n ⟩ Term
var`ⁿʳ x n = coe n (app` (var x) (replicate n argiᵛʳ))

-- sort₀ : Sort
pattern sort₀ = lit 0

-- sort₁ : Sort
pattern sort₁ = lit 1

-- `Set_ : ℕ → Term
pattern  `Set_ i = sort (lit i)

-- `Set₀ : Term
pattern `Set₀ = `Set_ 0

-- `★_ : ℕ → Term
pattern  `★_ i = sort (lit i)

-- `★₀ : Term
pattern `★₀ = `★_ 0

-- el₀ : Term → Type
pattern el₀ t = el sort₀ t

-- Builds a type variable (of type ★₀)
``var₀ : ℕ → Args → Type
``var₀ n args = el₀ (var n args)

-- ``set : ℕ → ℕ → Type
pattern ``set i j = el (lit (suc j)) (`★_ i)

``★_ : ℕ → Type
``★_ i = el (lit (suc i)) (`★_ i)

-- ``★₀ : Type
pattern ``★₀ = ``set 0 0

unEl : Type → Term
unEl (el _ tm) = tm

getSort : Type → Sort
getSort (el s _) = s

unArg : ∀ {A} → Arg A → A
unArg (arg _ a) = a

unAbs : ∀ {A} → Abs A → A
unAbs (abs _ a) = a

-- `Level : Term
pattern `Level = def (quote Level) []

-- ``Level : Type
pattern ``Level = el₀ `Level

pattern `₀ = def (quote ₀) []

-- `ₛ_ : Term → Term
-- `ₛ_ = def`ⁿʳ (quote L.suc) 1
pattern `ₛ_ v = def (quote ₛ) (argᵛʳ v ∷ [])

-- `suc-sort : Sort → Sort
pattern `suc-sort s = set (`ₛ (sort s))

pattern `set₀ = set `₀
pattern `setₛ_ s = set (`ₛ s)
pattern `set_ s = set (sort s)

suc-sort : Sort → Sort
suc-sort (set t) = set (`ₛ t)
suc-sort (lit n) = lit (suc n)
suc-sort unknown = unknown

decode-Sort : Sort → Maybe ℕ
decode-Sort `set₀ = just zero
decode-Sort (`setₛ_ s) = map? suc (decode-Sort (set s))
decode-Sort (`set_ s) = decode-Sort s
decode-Sort (set _) = nothing
decode-Sort (lit n) = just n
decode-Sort unknown = nothing

pattern _`⊔_ s₁ s₂ = set (def (quote _⊔_) (argᵛʳ (sort s₁) ∷ argᵛʳ (sort s₂) ∷ []))

_`⊔`_ : Sort → Sort → Sort
s₁ `⊔` s₂ with decode-Sort s₁ | decode-Sort s₂
...          | just n₁        | just n₂        = lit (n₁ ⊔ℕ n₂)
...          | _              | _              = s₁ `⊔ s₂

record MapVar : Set where
  field
    onVar : ℕ → ℕ
    onDef : Name → Name
    onCon : Name → Name
    onPrj : Name → Name
    onStr : String → String
open MapVar public

idMapVar : MapVar
idMapVar = record { onVar = id ; onDef = id ; onCon = id ; onPrj = id; onStr = id }

liftMapVar : (ℕ → ℕ) → MapVar
liftMapVar f = record idMapVar { onVar = f }

mapVar↑' : (ℕ → ℕ) → (ℕ → ℕ)
mapVar↑' f zero    = zero
mapVar↑' f (suc n) = suc (f n)

mapVar↑ : MapVar → MapVar
mapVar↑ Γ = record Γ { onVar = mapVar↑' (onVar Γ) }

Pats = List (Arg Pattern)

module _ (Γ : MapVar) where
    mapVarPattern  : Pattern → Pattern
    mapVarPatterns : Pats    → Pats

    mapVarPatterns [] = []
    mapVarPatterns (arg i p ∷ ps) = arg i (mapVarPattern p) ∷ mapVarPatterns ps

    mapVarPattern (con c pats) = con (onCon Γ c) (mapVarPatterns pats)
    mapVarPattern dot = dot
    mapVarPattern (var s) = var (onStr Γ s)
    mapVarPattern (lit l) = lit l
    mapVarPattern (proj p) = proj (onPrj Γ p)
    mapVarPattern absurd = absurd

mapVarTerm    : MapVar → Term → Term
mapVarArgs    : MapVar → Args → Args
mapVarType    : MapVar → Type → Type
mapVarSort    : MapVar → Sort → Sort
mapVarAbsTerm : MapVar → Abs Term → Abs Term
mapVarAbsType : MapVar → Abs Type → Abs Type
mapVarClause  : MapVar → Clause → Clause
mapVarClauses : MapVar → Clauses → Clauses

mapVarTerm Γ (var x args) = var (onVar Γ x) (mapVarArgs Γ args)
mapVarTerm Γ (con c args) = con (onCon Γ c) (mapVarArgs Γ args)
mapVarTerm Γ (def d args) = def (onDef Γ d) (mapVarArgs Γ args)
mapVarTerm Γ (lam v t) = lam v (mapVarAbsTerm Γ t)
mapVarTerm Γ (pat-lam cs args) = pat-lam (mapVarClauses Γ cs) (mapVarArgs Γ args)
mapVarTerm Γ (pi (arg i t₁) t₂) = pi (arg i (mapVarType Γ t₁)) (mapVarAbsType Γ t₂)
mapVarTerm Γ (sort x) = sort (mapVarSort Γ x)
mapVarTerm Γ (lit x) = lit x
mapVarTerm Γ unknown = unknown

mapVarClause Γ (clause pats body) = clause (mapVarPatterns Γ pats) (mapVarTerm Γ body)
mapVarClause Γ (absurd-clause pats) = absurd-clause (mapVarPatterns Γ pats)

mapVarClauses Γ [] = []
mapVarClauses Γ (c ∷ cs) = mapVarClause Γ c ∷ mapVarClauses Γ cs

mapVarAbsTerm Γ (abs s x) = abs (onStr Γ s) (mapVarTerm (mapVar↑ Γ) x)
mapVarAbsType Γ (abs s x) = abs (onStr Γ s) (mapVarType (mapVar↑ Γ) x)

mapVarArgs Γ [] = []
mapVarArgs Γ (arg i x ∷ as) = arg i (mapVarTerm Γ x) ∷ mapVarArgs Γ as
mapVarType Γ (el s t) = el (mapVarSort Γ s) (mapVarTerm Γ t)
mapVarSort Γ (set t) = set (mapVarTerm Γ t)
mapVarSort Γ (lit n) = lit n
mapVarSort Γ unknown = unknown

module _ (Γ : MapVar) where
  mapVarFunDef : FunctionDef → FunctionDef
  mapVarFunDef (fun-def ty cs) = fun-def (mapVarType Γ ty) (mapVarClauses Γ cs)
  
  mapVarDefinition : Definition → Definition
  mapVarDefinition (function x) = function (mapVarFunDef x)
  mapVarDefinition (data-type x) = data-type x
  mapVarDefinition (record′ x) = record′ x
  mapVarDefinition constructor′ = constructor′
  mapVarDefinition axiom = axiom
  mapVarDefinition primitive′ = primitive′

raiseMapVar : ℕ → MapVar
raiseMapVar k = liftMapVar (_+_ k)

raiseTerm : ℕ → Term → Term
raiseTerm = mapVarTerm ∘ raiseMapVar

raiseType : ℕ → Type → Type
raiseType = mapVarType ∘ raiseMapVar

raiseArgs : ℕ → Args → Args
raiseArgs = mapVarArgs ∘ raiseMapVar

noHintsMapVar : MapVar
noHintsMapVar = record idMapVar { onStr = const "_" }

noHintsTerm : Term → Term
noHintsTerm = mapVarTerm noHintsMapVar

noHintsType : Type → Type
noHintsType = mapVarType noHintsMapVar

noHintsDefinition : Definition → Definition
noHintsDefinition = mapVarDefinition noHintsMapVar

noAbsType : Type → Abs Type
noAbsType ty = abs "_" (raiseType 1 ty)

pattern piᵛʳ s t u = pi (argᵛʳ t) (abs s u)
pattern piʰʳ s t u = pi (argʰʳ t) (abs s u)

`Π : Arg Type → Abs Type → Type
`Π t u = el (getSort (unArg t) `⊔` getSort (unAbs u)) (pi t u)

`Πᵛʳ : Type → Abs Type → Type
`Πᵛʳ t u = `Π (argᵛʳ t) u

`Πʰʳ : Type → Abs Type → Type
`Πʰʳ t u = `Π (argʰʳ t) u

_`→_ : Arg Type → Type → Type
t `→ u = `Π t (noAbsType u)

_`→ʰʳ_ : Type → Type → Type
t `→ʰʳ u = `Πʰʳ t (noAbsType u)

_`→ᵛʳ_ : Type → Type → Type
t `→ᵛʳ u = `Πᵛʳ t (noAbsType u)

`Πⁿ : List (Arg Type) → Type → Type
`Πⁿ []       u = u
`Πⁿ (t ∷ ts) u = `Π t (abs "_" (`Πⁿ ts u))

`Πᵛʳⁿ : List Type → Type → Type
`Πᵛʳⁿ ts u = `Πⁿ (map argᵛʳ ts) u

`Πʰʳⁿ : List Type → Type → Type
`Πʰʳⁿ ts u = `Πⁿ (map argʰʳ ts) u

-- η vs mk: performs no shifting of the result of mk.
-- Safe values of mk are def and con for instance
η : List Arg-info → (Args → Term) → Term
η ais₀ mk = go ais₀ where
  vars : List Arg-info → Args
  vars []         = []
  vars (ai ∷ ais) = arg ai (var (length ais) []) ∷ vars ais
  go : List Arg-info → Term
  go []                   = mk (vars ais₀)
  go (arg-info v _ ∷ ais) = lam v (abs "_" (go ais))

ηʰ : ℕ → (Args → Term) → Term
ηʰ n = η (replicate n argiʰʳ)

ηᵛ : ℕ → (Args → Term) → Term
ηᵛ n = η (replicate n argiᵛʳ)

ηʰⁿ : ℕ → Name → Term
ηʰⁿ n = ηʰ n ∘ def

ηᵛⁿ : ℕ → Name → Term
ηᵛⁿ n = ηᵛ n ∘ def

term-arg-infos : Term → List Arg-info
type-arg-infos : Type → List Arg-info

type-arg-infos (el _ u) = term-arg-infos u
term-arg-infos (pi (arg ai _) (abs _ t)) = ai ∷ type-arg-infos t

-- no more arguments
term-arg-infos (var _ _) = []
term-arg-infos (sort s)  = []

-- TODO
term-arg-infos (def f args) = []

-- fail
term-arg-infos unknown      = []

-- absurd/ill-typed cases
term-arg-infos (con c args)  = []
term-arg-infos (lit _)       = []
term-arg-infos (lam _ _)     = []
term-arg-infos (pat-lam _ _) = []

term-arity : Term → ℕ
term-arity = length ∘ term-arg-infos
type-arity : Type → ℕ
type-arity = length ∘ type-arg-infos

ηⁿ : Name → Term
ηⁿ nm = η (type-arg-infos (type nm)) (def nm)

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
absArgs : Args → AbsTerm
absType : Type → AbsTerm
absSort : Sort → AbsTerm

absTerm (var x args) = var x ,, absArgs args
absTerm (con c args) = absArgs args
absTerm (def f args) = absArgs args
absTerm (lam v (abs s t)) = abs' s (absTerm t)
absTerm (pat-lam cs args) = opaque "absTm/pat-lam" []
absTerm (pi (arg _ t₁) (abs s t₂)) = absType t₁ ,, abs' s (absType t₂)
absTerm (sort x) = absSort x
absTerm (lit x) = []
absTerm unknown = []

absArgs [] = []
absArgs (arg i x ∷ as) = absTerm x ,, absArgs as
absType (el _ t) = absTerm t
absSort (set t) = absTerm t
absSort (lit n) = []
absSort unknown = []

app : Term → Args → Term
app (var x args) args₁ = var x (args ++ args₁)
app (con c args) args₁ = con c (args ++ args₁)
app (def f args) args₁ = def f (args ++ args₁)
app (lam v t)         _ = opaque "app/lam"               (lam v t)
app (pat-lam cs args) _ = opaque "app/pat-lam"           (pat-lam cs args)
app (pi t₁ t₂)        _ = opaque "app/pi (type-error)"   (pi t₁ t₂)
app (sort x)          _ = opaque "app/sort (type-error)" (sort x)
app (lit x)           _ = opaque "app/lit (type-error)"  (lit x)
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

unknown-type : Type
unknown-type = el unknown unknown

unknown-fun-def : FunctionDef
unknown-fun-def = opaque "unknown-fun-def" (fun-def (el unknown unknown) [])

unknown-definition : Definition
unknown-definition = opaque "unknown-definition" (function unknown-fun-def)

un-function : Definition → FunctionDef
un-function (function x) = x
un-function _            = unknown-fun-def

module Map-arg-info (f : Arg-info → Arg-info) where

    On : Set → Set
    On T = T → T

    pat : On Pattern
    pats : On (List (Arg Pattern))
    pat (con c ps) = con c (pats ps)
    pat dot = dot
    pat (var s) = (var s)
    pat (lit l) = lit l
    pat (proj p) = proj p
    pat absurd = absurd
    pats [] = []
    pats (arg i p ∷ ps) = arg (f i) (pat p) ∷ pats ps

    term : On Term
    tÿpe : On Type
    årgs : On Args
    sørt : On Sort
    clåuse  : On Clause
    clåuses : On (List Clause)

    term (var x as) = var x (årgs as)
    term (con c as) = con c (årgs as)
    term (def f as) = def f (årgs as)
    term (lam v (abs s t)) = lam (visibility (f (arg-info v (relevant{- arbitrary choice -})))) (abs s (term t))
    term (pat-lam cs as) = pat-lam (clåuses cs) (årgs as)
    term (pi (arg i t₁) (abs s t₂)) = pi (arg (f i) (tÿpe t₁)) (abs s (tÿpe t₂))
    term (sort s) = sort (sørt s)
    term (lit l) = lit l
    term unknown = unknown

    tÿpe (el s t) = el (sørt s) (term t)

    årgs [] = []
    årgs (arg i t ∷ as) = arg (f i) (term t) ∷ årgs as

    sørt (set t) = set (term t)
    sørt (lit n) = lit n
    sørt unknown = unknown

    clåuse (clause ps body) = clause (pats ps) (term body)
    clåuse (absurd-clause ps) = absurd-clause (pats ps)

    clåuses [] = []
    clåuses (x ∷ cs) = clåuse x ∷ clåuses cs

    fün-def : FunctionDef → FunctionDef
    fün-def (fun-def t cs) = fun-def (tÿpe t) (clåuses cs)

    dëf : Definition → Definition
    dëf (function x) = function (fün-def x)
    dëf (data-type x) = opaque "Map-arg-info.dëf/data-type" unknown-definition
    dëf (record′ x) = opaque "Map-arg-info.dëf/record′" unknown-definition
    dëf constructor′ = opaque "Map-arg-info.dëf/constructor′" unknown-definition
    dëf axiom = opaque "Map-arg-info.dëf/axiom" unknown-definition
    dëf primitive′ = opaque "Map-arg-info.dëf/primitive′" unknown-definition

    nåme : Name → Definition
    nåme = dëf ∘ definition

reveal-arg : Arg-info → Arg-info
reveal-arg (arg-info v r) = arg-info visible r

module Reveal-args = Map-arg-info reveal-arg

module Get-clauses where
    from-fun-def : FunctionDef → Clauses
    from-fun-def (fun-def _ cs) = cs
    from-def : Definition → Clauses
    from-def (function x) = from-fun-def x
    from-def (data-type x) = opaque "Get-clauses.from-def/data-type" []
    from-def (record′ x) = opaque "Get-clauses.from-def/record′" []
    from-def constructor′ = opaque "Get-clauses.from-def/constructor′" []
    from-def axiom = opaque "Get-clauses.from-def/axiom" []
    from-def primitive′ = opaque "Get-clauses.from-def/primitive′" []
    from-name : Name → Clauses
    from-name n = from-def (definition n)

module Get-type where
    from-fun-def : FunctionDef → Type
    from-fun-def (fun-def t _) = t
    from-def : Definition → Type
    from-def (function x) = from-fun-def x
    from-def (data-type x) = opaque "Get-type.from-def/data-type" ``★₀
    from-def (record′ x) = opaque "Get-type.from-def/record′" ``★₀
    from-def constructor′ = opaque "Get-type.from-def/constructor" ``★₀
    from-def axiom = opaque "Get-type.from-def/axiom" ``★₀
    from-def primitive′ = opaque "Get-type.from-def/primitive′" ``★₀
    {-
    from-name : Name → Type
    from-name = type -- or: λ n → from-def (definition n)
    -}

module Get-term where
    from-clause : Clause → Term
    from-clause (clause [] body) = body
    from-clause (clause (arg (arg-info v _) (var s) ∷ pats) body)
      = lam v (abs s (from-clause (clause pats body)))
    from-clause _ = unknown
    from-clauses : Clauses → Term
    from-clauses (c ∷ []) = from-clause c
    from-clauses _ = opaque "Get-term.from-clauses" unknown
    from-fun-def : FunctionDef → Term
    from-fun-def (fun-def _ cs) = from-clauses cs
    from-def : Definition → Term
    from-def (function x) = from-fun-def x
    from-def (data-type x) = unknown
    from-def (record′ x) = unknown
    from-def constructor′ = unknown
    from-def axiom = unknown
    from-def primitive′ = unknown
    from-name : Name → Term
    from-name n = from-def (definition n)

-- Given a type `tyH` with potential hidden arguments, this module builds
-- a function from `tyH` to `tyE` with is `tyH` with explicit arguments
-- instead.
module Revelator (tyH : Type) where
    tyE : Type
    tyE = Reveal-args.tÿpe tyH
    tyF : Type
    tyF = tyH `→ᵛʳ tyE
    tm : Term → ℕ → Args → Term
    tm (pi (arg (arg-info v _) t₁) (abs s (el _ t₂))) y as
      = lamᵛ s (tm t₂ (suc y) (raiseArgs 1 as ++ argʳ v (var 0 []) ∷ []))
    tm (var x args) = var
    tm (def f args) = var
    tm (sort s)     = var
    tm unknown _ _ = unknown
    tm (con c args) _ _ = opaque "revealator/tm/con: impossible" unknown
    tm (lam v ty) _ _ = opaque "revealator/tm/lam: impossible" unknown
    tm (lit l) _ _ = opaque "revealator/tm/lit: impossible" unknown
    tm (pat-lam cs args) _ _ = opaque "revealator/tm/pat-lam: TODO" unknown
    term : Term
    term = lamᵛ "_" (tm (unEl tyH) 0 [])
    clauses : Clauses
    clauses = clause [] term ∷ []
    fun : FunctionDef
    fun = fun-def tyF clauses

module Revelator-by-name (n : Name) = Revelator (type n)

{-
revelator-id : ({a : Level} {A : Set a} (x : A) → A)
             →  (a : Level) (A : Set a) (x : A) → A
unquoteDef revelator-id = Revelator-by-name.clauses (quote id)

module Ex where
  open import Relation.Binary.PropositionalEquality
  postulate
    f : ℕ → ℕ → ℕ
    g : {x y : ℕ} → ℕ
    h : {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → ℕ
  H : ★
  H = {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → ℕ
  postulate
    h₂ : H
  test₁ : unquote (ηᵛⁿ 2 (quote f)) ≡ f
  test₁ = refl
  test₂ : unquote (ηʰⁿ 2 (quote g)) ≡ λ {x y : ℕ} → g {x} {y}
  test₂ = refl
  test₃ : unquote (ηⁿ (quote f)) ≡ f
  test₃ = refl
  test₄ : unquote (ηⁿ (quote g)) ≡ λ {x y : ℕ} → g {x} {y}
  test₄ = refl
  ηh = ηⁿ (quote h)
  -- this test passes but leave an undecided instance argument
  -- test₅ : unquote ηh ≡ λ {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → h {x} {y} {{z}} t u {v}
  -- test₅ = refl
  ηh₂ : Term
  ηh₂ = ηⁿ (quote h₂)
  {-
  test₆ : unquote ηh₂ ≡ {!unquote ηh₂!} -- λ {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → h {x} {y} {{z}} t u {v}
  test₆ = refl
  -}
  test₇ : decode-ℕ (quoteTerm (ℕ.suc (suc zero))) ≡ just 2
  test₇ = refl
  test₈ : decode-ℕ (quoteTerm (ℕ.suc (suc 3))) ≡ just 5
  test₈ = refl
  test₉ : decode-Maybe decode-𝟚 (quoteTerm (Maybe.just 0₂)) ≡ just (just 0₂)
  test₉ = refl
  test₁₀ : decode-List decode-ℕ (quoteTerm (0 ∷ 1 ∷ 2 ∷ [])) ≡ just (0 ∷ 1 ∷ 2 ∷ [])
  test₁₀ = refl
  test₁₁ : quoteTerm (_,′_ 0₂ 1₂) ≡ `0₂ `, `1₂
  test₁₁ = refl
  test₁₁' : decode-List (decode-Σ {A = 𝟚} {B = [0: 𝟚 1: ℕ ]} decode-𝟚 [0: decode-𝟚 1: decode-ℕ ])
                        (quoteTerm ((Σ._,_ {B = [0: 𝟚 1: ℕ ]} 0₂ 1₂) ∷ (1₂ , 4) ∷ [])) ≡ just ((0₂ , 1₂) ∷ (1₂ , 4) ∷ [])
  test₁₁' = refl

-- -}
-- -}
-- -}
-- -}

{-# OPTIONS --with-K #-}
module Data.Fin.Param.Binary where

open import Data.Fin
open import Data.Nat
open import Function

open import Data.Nat.Param.Binary
open import Reflection.NP
open import Reflection.Param
open import Reflection.Param.Env
open import Function.Param.Binary
open import Type.Param.Binary

{-
-- See Data.Fin.Logical for an example

data ⟦Fin⟧ : (⟦ℕ⟧ ⟦→⟧ ⟦Set₀⟧) Fin Fin where
  ⟦zero⟧ : ∀ {n₀ n₁}(n : ⟦ℕ⟧ n₀ n₁) → ⟦Fin⟧ (⟦suc⟧ n) zero zero
  ⟦suc⟧  : (∀⟨ n ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Fin⟧ n ⟦→⟧ ⟦Fin⟧ (⟦suc⟧ n)) suc suc
-}

{- TODO
data ⟦Fin⟧ : (⟦ℕ⟧ ⟦→⟧ ⟦Set₀⟧) Fin Fin

private
  ⟦Fin⟧-ctor = λ c → unEl (param-ctor-by-name (extDefEnv [ quote Fin ≔ quote ⟦Fin⟧ ] ⟦ℕ⟧-env) c)

data ⟦Fin⟧ where
  ⟦zero⟧ : unquote (⟦Fin⟧-ctor (quote Fin.zero))
  ⟦suc⟧  : unquote (⟦Fin⟧-ctor (quote Fin.suc ))

{-
inject₁ : ∀ {m} → Fin m → Fin (suc m)
inject₁ zero    = zero
inject₁ (suc i) = suc (inject₁ i)
-}

defEnv2Fin = extConEnv ([ quote Fin.zero ≔ quote ⟦Fin⟧.⟦zero⟧ ] ∘
                        [ quote Fin.suc  ≔ quote ⟦Fin⟧.⟦suc⟧  ])
             (extDefEnv [ quote Fin ≔ quote ⟦Fin⟧ ] ⟦ℕ⟧-env)

open import Data.Fin using (inject₁)

unquoteDecl ⟦inject₁⟧ = pFunNameRec defEnv2Fin (quote inject₁) ⟦inject₁⟧
-}

-- NOTE with-K
module Data.Fin.Param.Binary where

open import Data.Nat.Param.Binary
open import Data.Fin
open import Reflection.NP
open import Reflection.Param
open import Function.Param.Binary
open import Type.Param.Binary

data ⟦Fin⟧ : (⟦ℕ⟧ ⟦→⟧ ⟦Set₀⟧) Fin Fin

private
  ⟦Fin⟧-ctor = λ c → unEl (param-ctor-by-name (extDefEnv [ quote Fin ≔ quote ⟦Fin⟧ ] defEnv2) c)

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
             (extDefEnv [ quote Fin ≔ quote ⟦Fin⟧ ] defEnv2)

open import Data.Fin using (inject₁)

unquoteDecl ⟦inject₁⟧ = pFunNameRec defEnv2Fin (quote inject₁) ⟦inject₁⟧

module Recursive where

open import Data.Bool using (Bool; true; false)

-- defining natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

nine : ℕ
nine = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

ten : ℕ
ten = suc nine

-- Binary representation of ℕ

data ℕ⁺ : Set where
  one      :      ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero :      ℕ₂
  id   : ℕ⁺ → ℕ₂

-- Exercise: define nine : ℕ₂!

nine' : ℕ₂
nine' = id (double+1 (double (double one)))
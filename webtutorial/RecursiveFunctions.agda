module RecursiveFunctions where

open import Data.Bool using (Bool; true; false)

data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ


{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_

-- predecessor (pred 0 = 0)

pred  : ℕ → ℕ
pred 0 = 0
pred (suc n) = n

infixl 6 _∸_

_∸_   : ℕ → ℕ → ℕ  -- subtraction (0 ∸ n = n)
0 ∸ m = m
n ∸ 0 = n
suc n ∸ suc m = suc (n ∸ m)

infixl 7 _*_

_*_   : ℕ → ℕ → ℕ  -- multiplication
0 * _ = 0
suc n * m = m + (n * m)

infixl 6 _⊔_

_⊔_   : ℕ → ℕ → ℕ  -- maximum
0 ⊔ m = m
n ⊔ 0 = n
(suc n) ⊔ (suc m) = suc (n ⊔ m)


infixl 7 _⊓_

_⊓_   : ℕ → ℕ → ℕ  -- minimum
0 ⊓ m = 0
n ⊓ 0 = 0
(suc n) ⊓ (suc m) = suc (n ⊔ m)


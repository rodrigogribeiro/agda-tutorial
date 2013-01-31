module Proofs where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)

data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →               zero  ≤ n
  s≤s : {m n : ℕ} →   m ≤ n  →  suc m ≤ suc n

infix 4 _≤_

≤-refl : (n : ℕ) → n ≤ n
≤-refl 0 =  z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n no = z≤n
≤-trans (s≤s y) (s≤s y') = s≤s (≤-trans y y')

total : ∀ m n → m ≤ n ⊎ n ≤ m -- hint: use [_,_]′
total zero n = inj₁ z≤n
total (suc n) zero = inj₂ z≤n
total (suc n) (suc n') with total n n' 
...| inj₁ n≤n' = inj₁ (s≤s n≤n')
...| inj₂ n'≤n = inj₂ (s≤s n'≤n)

≤-pred  : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s y) = y

≤-mono  : ∀ (m n k : ℕ) → n ≤ m → k + n ≤ k + m
≤-mono m n zero p = p
≤-mono m n (suc n') p = s≤s (≤-mono m n n' p)
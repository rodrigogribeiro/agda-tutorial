module Universes where

open import Data.Nat hiding (compare)
open import Data.Empty
open import Data.Unit
open import Data.Bool


isTrue : Bool → Set
isTrue true = ⊤
isTrue false = ⊥

notNotId : (a : Bool) → isTrue (not (not a)) → isTrue a
notNotId true p = p
notNotId false () 

∧-intro : (a b : Bool) → isTrue a → isTrue b → isTrue (a ∧ b)
∧-intro true true p q = tt
∧-intro false _ () _
∧-intro _ false _ ()

-- Exercices 1)

--a)

data Compare : ℕ → ℕ → Set where
  less : ∀ {n} k → Compare n (n + suc k)
  more : ∀ {n} k → Compare (n + suc k) n
  same : ∀ {n} → Compare n n

compare : (a b : ℕ) → Compare a b
compare zero zero = same
compare zero (suc k) = less k
compare (suc k) zero = more k
compare (suc a) (suc b) with compare a b
compare (suc a)            (suc .a)           | same   = same
compare (suc a)            (suc .(a + suc k)) | less k = less k
compare (suc .(b + suc k)) (suc b)            | more k = more k

-- b)

difference : ℕ → ℕ → ℕ
difference n m with compare n m
difference n            .n           | same   = zero
difference n            .(n + suc k) | less k = zero
difference .(m + suc k) m            | more k = suc k
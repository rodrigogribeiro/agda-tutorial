module Indexed where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc)


-- finite sets

data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)

-- Exercises

-- * Define a Bool indexed family of sets such that the set indexed by false contains 
--   no elements and the set indexed by true contains one element!

data BFin : Bool → Set where
  one : BFin true

-- Define a ℕ indexed family of sets such that the sets indexed by even numbers contains one element and others are empty!

data EvenSet : ℕ → Set where
  z : EvenSet 0
  ss : (n : ℕ) → EvenSet n → EvenSet (suc (suc n))

t : EvenSet 4
t = ss (suc (suc zero)) (ss zero z)

-------------------------------------

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

-- Exercise

-- * Define a Bool indexed family of sets with two parameters, A and B, such that the set indexed
--   by false contains an A element and the set indexed by true contains a B element!

data SEither (A B : Set) : Bool → Set where
  left : A → SEither A B false
  right : B → SEither A B true
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

-- Exercises

--Define binary trees
--  * with natural number data attached to the leafs

data BTreeNat : Set where
  nleaf : ℕ → BTreeNat
  nnode : BTreeNat → BTreeNat → BTreeNat

-- * with natural number data attached to the nodes

data BTreeNat' : Set where
  nleaf' : BTreeNat'
  nnode' : ℕ → BTreeNat' → BTreeNat' → BTreeNat'

-- * with Booleans in the nodes and natural numbers in the leafs

data BTreeNat'' : Set where
  nleaf : ℕ → BTreeNat''
  nnode : ℕ → BTreeNat'' → BTreeNat'' → BTreeNat''

-- * Define the lists of natural numbers! Use _∷_ as list consructor with right precedence!

data NList : Set where
  nil : NList
  _∷_ : ℕ → NList → NList

-- * Define the non-empty lists of natural numbers!

data NEList : Set where
  end : ℕ → NEList
  cons : ℕ → NEList → NEList

-- * Define trees with nodes with finite children (0, 1, 2, ...)!
-- in order to answer this, I believe that is necessary polymorphism...

data L : Set
data M : Set

data L where
  nil : L
  _∷_ : ℕ → M → L

data M where
  _∷_ : Bool → L → M

-- What are the elements of L and M?
-- * L: an empty list or a list formed by a sequences of naturals and after a boolean value.
-- * M: A non-empty list formed by at least a boolean or sequences of booleans and after a natural.


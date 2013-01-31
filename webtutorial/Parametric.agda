module Parametric where

open import Data.Nat

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

-- Exercises

-- * What is the connection between List ⊤ and ℕ?
-- The types ℕ and List ⊤ are isomorphic, since:
-- [] ≅ 0
-- ⊤ ∷ [] ≅ 1
-- and so on...
-- Define a Maybe set (lists with 0 or 1 elements)!

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

-- Define paramteric trees (various sorts)!

data Tree (A : Set) : Set where
  leaf : Tree A
  node : A → List (Tree A) → Tree A

---------------------------------------------------

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

-- Exercises

-- * How many elements are there in ⊤ × ⊤, ⊤ × ⊥, ⊥ × ⊤ and ⊥ × ⊥?
-- a) 1 
-- b) 0
-- c) 0
-- d) 0
-- How should we define Top so that ∀ A : Set. Top × A would be isomorphic to A (neutral element of _×_)?
-- Top must have a definition isomorphic to ⊤, like:

data Top : Set where
  unit : Top

--------------------------------------------------

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- Exercises

-- * What are the elements of Bool ⊎ ⊤?
-- The elements are: true, false, tt

-- * What are the elements of ⊤ ⊎ (⊤ ⊎ ⊤)?
-- This set has a single element: tt

-- * Name an already learned isomorphic type to ⊤ ⊎ ⊤!
-- ⊤ is isomorphic to ⊤⊎⊤

-- * How should we define Bottom so that ∀ A : Set. Bottom ⊎ A would be isomorphic to A (Neutral element of _⊎_)?
-- Bottom must be isomorphic to empty type, like:

data Bottom : Set where 

-- Give an isomorphic definition of Maybe A with the help of _⊎_ and ⊤!
-- Maybe A = A ⊎ ⊤




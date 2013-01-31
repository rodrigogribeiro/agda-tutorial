module Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

-- Define two functions which define the isomorphism between List ⊤ and ℕ!

-- fromList : List ⊤ → ℕ

fromList : List ⊤ → ℕ
fromList [] = 0
fromList (p ∷ l) = suc (fromList l)

toList   : ℕ → List ⊤
toList 0 = []
toList (suc n) = tt ∷ (toList n)

-- Define the following functions on lists:

map  : {A B : Set} → (A → B)      → List A → List B -- regular map
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map
maps [] [] = []
maps fs [] = []
maps [] xs = []
maps (f ∷ fs) (a ∷ as) = (f a) ∷ (maps fs as)

-- Define the singleton list function:

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

-- id function

id : {A : Set} → A → A
id x = x

-- const function

const : {A B : Set} → A → B → B
const x y = y

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

swap : {A B : Set} → A × B → B × A
swap (a , b) = (b , a)

proj₁ : {A B : Set} → A × B → A
proj₁ (a , b) = a

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[ f , g ] (inj₁ a) = f a
[ f , g ] (inj₂ b) = g b
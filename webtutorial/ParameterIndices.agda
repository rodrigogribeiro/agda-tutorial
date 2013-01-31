module ParameterIndices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Empty

data  _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_

data _∈_ {A : Set}(x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

-------------------

data _⊆_ {A : Set} : List A → List A → Set where
  base : ∀ {ys} → [] ⊆ ys
  rec  : ∀ {x xs ys} → xs ⊆ ys → x ∈ ys → x ∷ xs ⊆ ys

infix 3 _⊆_

p1 :  1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
p1 = rec (rec base (later first)) first

px : 3 ∈ 1 ∷ 2 ∷ [] → ⊥
px (later (later ()))

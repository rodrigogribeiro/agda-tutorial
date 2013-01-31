module Equality where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_) 

data _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_

refl'  : ∀ {A} (a : A) → a ≡ a
refl' a = refl

sym   : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl   -- after pattern matching on 'refl', 'a' and 'b' coincides


--Exercise

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

--Prove that every function is compatible with the equivalence relation (congruency):

cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero    = refl
+-right-identity (suc n) = cong suc (+-right-identity n)

+-left-identity  : ∀ a → 0 + a ≡ a
+-left-identity a = refl

+-assoc          : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
+-assoc zero b c = refl
+-assoc (suc n) b c = cong suc (+-assoc n b c)

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

infix  2 _∎

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm zero    n = sym (+-right-identity n)
+-comm (suc m) n =
      suc m + n
    ≡⟨ refl ⟩
      suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
      suc (n + m)
    ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
      n + suc m
    ∎

module trySemiringSolver where

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡-official_)

f : ∀ a b c → a + b * c + 1 ≡-official 1 + c * b + a
f = solve 3 (λ a b c → a :+ b :* c :+ con 1 := con 1 :+ c :* b :+ a) refl

g : ∀ a b c d → a + b * (c + d)  ≡-official a + b * c + b * d
g = solve 4 (λ a b c d → a :+ b :* (c :+ d) := a :+ b :* c :+ b :* d) refl
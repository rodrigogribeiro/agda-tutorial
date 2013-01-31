module Propositions where

open import Data.Nat using (ℕ; zero; suc)


-- truth proposition

data ⊤ : Set where
  tt : ⊤

-- false proposition

data ⊥ : Set where

-- product

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

-- disjunction

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- Exercices

-- Construct one proof for each proposition if possible:

-- ⊤ × ⊤

p1 : ⊤ × ⊤
p1 = tt , tt

-- ⊤ × ⊥
-- no possible proof for ⊥

-- ⊥ × ⊥
-- no possible proof for ⊥

-- ⊤ ⊎ ⊤

p2 : ⊤ ⊎ ⊤
p2 = inj₁ tt

-- ⊤ ⊎ ⊥

p3 : ⊤ ⊎ ⊥
p3 = inj₁ tt

-- ⊥ ⊎ ⊥
-- no proof for ⊥

-- ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤

p4 : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
p4 = inj₂ (inj₁ tt)

---------------------------------

data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                       zero  ≤ n
  s≤s : {m : ℕ} → {n : ℕ} →   m ≤ n  →  suc m ≤ suc n

infix 4 _≤_

p6 : 3 ≤ 7
p6 = s≤s (s≤s (s≤s z≤n))

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ()))

---------------------------------


data _isDoubleOf_ : ℕ → ℕ → Set where
  zidf : 0 isDoubleOf 0 
  uidf : (suc (suc zero)) isDoubleOf (suc zero)
  sidf : {n : ℕ} → {m : ℕ} → m isDoubleOf n →  suc (suc m) isDoubleOf (suc n)

p7 : 8 isDoubleOf 4
p7 = sidf (sidf (sidf uidf))

p8 : 9 isDoubleOf 4 → ⊥
p8 (sidf (sidf (sidf (sidf ()))))

-------------------------------

data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  zev : Even zero
  sev : {n : ℕ} → Odd n → Even (suc n)

data Odd where
  ood : Odd (suc zero)
  sod : {n : ℕ} → Even n → Odd (suc n)

p9 : Odd 9
p9 = sod (sev (sod (sev (sod (sev (sod (sev ood)))))))

---------------------------------

data _≡_ : ℕ → ℕ → Set where
  zeq : 0 ≡ 0
  seq : {n m : ℕ} → n ≡ m → (suc n) ≡ (suc m)

data _≠_ : ℕ → ℕ → Set where
  zneq1 : {m : ℕ} → 0 ≠ m
  zneq2 : {n : ℕ} → n ≠ 0
  sneq  : {n m : ℕ} → n ≠ m → (suc n) ≠ (suc m)

---------------------------------

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

-- Prove that 5 + 5 = 10!
p11 : 5 + 5 ≡ 10
p11 = sns (sns (sns (sns (sns znn))))

-- Prove that 2 + 2 ≠ 5!

p12 : 2 + 2 ≡ 5 → ⊥
p12 (sns (sns ())) 

----------------------------------

-- Define _⊓_ : ℕ → ℕ → Set such that n ⊓ m ≡ k iff k is the minimum of n and m!

data _⊓_≡_ : ℕ → ℕ → ℕ → Set where
  lle : {n m : ℕ} → n ≤ m → n ⊓ m ≡ n
  rle : {n m : ℕ} → m ≤ n → n ⊓ m ≡ m

-- Prove that 3 ⊓ 5 ≡ 3 is non-empty!

p13 : 3 ⊓ 5 ≡ 3
p13 = lle (s≤s (s≤s (s≤s z≤n)))

-- Prove that 3 ⊓ 5 ≡ 5 is empty!

p14 : 3 ⊓ 5 ≡ 5 → ⊥
p14 (rle (s≤s (s≤s (s≤s ()))))

-- Define _⊔_ : ℕ → ℕ → Set such that n ⊔ m ≡ k iff k is the maximum of n and m!

data _⊔_≡_ : ℕ → ℕ → ℕ → Set where
  lge : {n m : ℕ} → m ≤ n → n ⊔ m ≡ n
  rge : {n m : ℕ} → n ≤ m → n ⊔ m ≡ m

-- Prove that 3 ⊔ 5 ≡ 5 is non-empty!

p15 : 3 ⊔ 5 ≡ 5
p15 = rge (s≤s (s≤s (s≤s z≤n)))

-- Prove that 3 ⊔ 5 ≡ 3 is empty!

p16 : 3 ⊔ 5 ≡ 3 → ⊥
p16 (lge (s≤s (s≤s (s≤s ()))))


-----------------------------------------------

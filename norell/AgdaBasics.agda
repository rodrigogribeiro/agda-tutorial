module AgdaBasics where

data Bool : Set where
  true false : Bool

not : Bool → Bool
not false = true
not true = false

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
(suc n) + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m = zero
(suc n) * m = m + (n * m)

_or_ : Bool → Bool → Bool
false or b = b
true or _ = true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix 5 if_then_else_

infixr 40 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

id : (A : Set) → A → A
id A x = x

zero' : ℕ
zero' = id ℕ zero

apply : (A : Set) (B : A → Set) →
        ((x : A) → B x) → (a : A) → B a
apply A B f a = f a

id' : {A : Set} → A → A
id' x = x 

true' : Bool
true' = id' true

_∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set}
      (f : {x : A}(y : B x) → C x y)(g : (x : A) → B x)
      (x : A) → C x (g x)
(f ∘ g) x = f (g x)

plus-two = suc ∘ suc

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ xs) = x

vmap : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x ∷ xs) = f x ∷ vmap f xs

data Vec₂ (A : Set) : ℕ → Set where
  nil : Vec₂ A zero
  cons : (n : ℕ) → A → Vec₂ A n → Vec₂ A (suc n)

vmap₂ : {A B : Set}(n : ℕ) → (A → B) → Vec₂ A n → Vec₂ B n
vmap₂ .zero f nil = nil
vmap₂ .(suc n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)

vmap₃ : {A B : Set}(n : ℕ) → (A → B) → Vec₂ A n → Vec₂ B n
vmap₃ zero f nil = nil
vmap₃ (suc n) f (cons .n x xs) = cons n (f x) (vmap₃ n f xs)

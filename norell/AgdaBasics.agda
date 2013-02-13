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


data Image_∋_ {A B : Set}(f : A → B) : B → Set where
  im : (x : A) → Image f ∋ f x

inv : {A B : Set} (f : A → B)(y : B) → Image f ∋ y → A
inv f .(f x) (im x) = x

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)

magic : {A : Set} → Fin zero → A
magic ()

_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[] ! ()
(x ∷ xs) ! fzero = x
(x ∷ xs) ! (fsuc i) = xs ! i

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero} f = []
tabulate {suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

isTrue : Bool → Set
isTrue true = ⊤
isTrue false = ⊥

_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < suc n = true
suc n < suc m = n < m

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

lookup : {A : Set}(xs : List A)(n : ℕ) → isTrue (n < length xs) → A
lookup [] n ()
lookup (x ∷ xs) zero p = x
lookup (x ∷ xs) (suc n) p = lookup xs n p

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

data _≤_ : ℕ → ℕ → Set where
  leq-zero : {n : ℕ} → zero ≤ n
  leq-succ : {n m : ℕ} → n ≤ m → suc n ≤ suc m

leq-trans : {l m n : ℕ} → l ≤ m → m ≤ n → l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-succ p) (leq-succ q) = leq-succ (leq-trans p q)

min : ℕ → ℕ → ℕ
min x y with x < y
...| true = x
...| false = y

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
...| true = x ∷ (filter p xs)
...| false = filter p xs

data _≠_ : ℕ → ℕ → Set where
  z≠s : {n : ℕ} → zero ≠ suc n
  s≠z : {n : ℕ} → (suc n) ≠ zero
  s≠s : {n m : ℕ} → n ≠ m → suc n ≠ suc m

data Equal? (n m : ℕ) : Set where
  eq : n == m → Equal? n m
  neq : n ≠ m → Equal? n m

equal? : (n m : ℕ) → Equal? n m
equal? zero zero = eq refl
equal? zero (suc m) = neq z≠s
equal? (suc n) zero = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc n) (suc m)  | neq p   = neq (s≠s p)

infix 20 _⊆_ 

data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ (y ∷ ys)
  keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys

lem-filter : {A : Set}(p : A → Bool)(xs : List A) → filter p xs ⊆ xs
lem-filter p [] = stop
lem-filter p (x ∷ xs) with p x
...| true = keep (lem-filter p xs)
...| false = drop (lem-filter p xs)

-- Exercices
--1-a)

vec : {n : ℕ}{A : Set} → A → Vec A n
vec {zero} _ = []
vec {suc n} x = x ∷ (vec x)

--1-b)

infixl 90 _$_

_$_ : {n : ℕ}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
[] $ xs = []
(y ∷ y') $ (x ∷ x') = y x ∷ y' $ x'

Matrix : Set → ℕ → ℕ → Set
Matrix A n m = Vec (Vec A n) m

--- LOL this function is really cool!

transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
transpose [] = vec []
transpose (a ∷ as) = ((vec _∷_) $ a) $ (transpose as)

--2-a)

lem-!-tab : ∀ {A n} (f : Fin n → A) (i : Fin n) → ((tabulate f) ! i) == f i
lem-!-tab f fzero = refl
lem-!-tab f (fsuc x) = lem-!-tab (λ z → f (fsuc z)) x

-- 2-b)

lem-tab-! : ∀ {A n} (xs : Vec A n) → tabulate (_!_ xs) == xs
lem-tab-! {A} {zero} [] = refl
lem-tab-! {A} {suc y} (x ∷ xs) with tabulate (_!_ xs) | lem-tab-! xs
...| .xs | refl = refl

-- 3-a)

⊆-refl : {A : Set}{xs : List A} → xs ⊆ xs
⊆-refl {A} {[]} = stop
⊆-refl {A} {y ∷ y'} = keep ⊆-refl

-- 3-b)

⊆-trans : {A : Set}{xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans p stop = p
⊆-trans p (drop ys) = drop (⊆-trans p ys)
⊆-trans (drop y) (keep ys) = drop (⊆-trans y ys)
⊆-trans (keep y) (keep ys) = keep (⊆-trans y ys)

-- 4)

infixr 30 _::_

data SubList {A : Set} : List A → Set where
  [] : SubList []
  _::_ : ∀ x {xs} → SubList xs → SubList (x ∷ xs)
  skip : ∀ {x xs} → SubList xs → SubList (x ∷ xs)

--a)

forget : {A : Set}{xs : List A} → SubList xs → List A
forget [] = []
forget (x :: ss) = x ∷ (forget ss)
forget (skip ss) = forget ss

--b)

lem-forget : {A : Set}{xs : List A}(zs : SubList xs) → forget zs ⊆ xs
lem-forget [] = stop
lem-forget (x :: y) = keep (lem-forget y)
lem-forget (skip y) = drop (lem-forget y)

--c) 

filter' : {A : Set} → (A → Bool) → (xs : List A) → SubList xs
filter' p [] = []
filter' p (x ∷ xs) with p x
...| true = x :: (filter' p xs)
...| false = skip (filter' p xs)

--d)

complement : {A : Set}{xs : List A} → SubList xs → SubList xs
complement [] = []
complement (x :: xs) = skip (complement xs)
complement (skip {x = x} xs) = x :: (complement xs)

--e)

sublists : {A : Set}(xs : List A) → List (SubList xs)
sublists [] = []
sublists (x ∷ xs) = let xss = sublists xs
                    in map skip xss ++ map (_::_ x) xss
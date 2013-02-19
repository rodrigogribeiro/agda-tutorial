module BrutalDepTypes where

module ThrowAwayIntroduction where
  data Bool : Set where
    true false : Bool -- Note, we can list constructors of a same type
                      -- by interspersing them with spaces.

  -- input for ℕ is \bn,
  -- input for → is \to, but -> is fine too
  -- Naturals.
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  -- Identity container
  data Id (A : Set) : Set where
    pack : A → Id A

  -- input for ⊥ is \bot
  -- Empty type. Absurd. False proposition.
  data ⊥ : Set where

  idℕ₀ : ℕ → ℕ
  idℕ₀ x = x

  idℕ₁ : (n : ℕ) → ℕ
  idℕ₁ x = x -- this `x` refers to the same argument as `n` in the type

  idℕ₂ : (_ : ℕ) → ℕ
  idℕ₂ x = x

  id₀ : (A : Set) → A → A
  id₀ _ a = a

  not : Bool → Bool
  not true  = false
  not false = true

  not₀ : Bool → Bool
  not₀ true  = false
  not₀ fals  = true

  data Three : Set where
    COne CTwo CThree : Three

  three2ℕ : Three → ℕ
  three2ℕ COne = zero
  three2ℕ Ctwo = succ zero
  --three2ℕ _    = succ (succ zero) -- intersects with the previous clause

  id : {A : Set} → A → A
  id a = a

  idTest₀ : ℕ → ℕ
  idTest₀ = id

    -- positional:
  id₁ : {A : Set} → A → A
  id₁ {A} a = a

  idTest₁ : ℕ → ℕ
  idTest₁ = id {ℕ}

  -- named:
  const₀ : {A : Set} {B : Set} → A → B → A
  const₀ {B = _} a _ = a

  constTest₀ : ℕ → ℕ → ℕ
  constTest₀ = const₀ {A = ℕ} {B = ℕ}

  id₃ : {A : Set} (a : A) → A
  id₃ a = a

  const : {A B : Set} → A → B → A
  const a _ = a

  idTest₃ : ℕ → ℕ
  idTest₃ = id₀ _

  unpack₀ : {A : _} → Id A → A
  unpack₀ (pack a) = a

  -- input for ∀ is \all or \forall
  unpack : ∀ {A} → Id A → A
  unpack (pack a) = a

  -- explicit argument version:
  unpack₁ : ∀ A → Id A → A
  unpack₁ _ (pack a) = a

  unpack₂ : ∀ {A B} → Id A → Id B → A
  unpack₂ (pack a) _ = a

  unpack₃ : ∀ {A} (_ : Id A) {B} → Id B → A
  unpack₃ (pack a) _ = a

  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then a else _ = a
  if false then _ else b = b

  -- Are two ℕs equal?
  _=ℕ?_ : ℕ → ℕ → Bool
  zero   =ℕ? zero   = true
  zero   =ℕ? succ m = false
  succ m =ℕ? zero   = false
  succ n =ℕ? succ m = n =ℕ? m

  -- Sum for ℕ.
  infix 6 _+_
  _+_ : ℕ → ℕ → ℕ
  zero   + n = n
  succ n + m = succ (n + m)

  ifthenelseTest₀ : ℕ
  ifthenelseTest₀ = if (zero + succ zero) =ℕ? zero
    then zero
    else succ (succ zero)

  -- Lists
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  [_] : {A : Set} → A → List A
  [ a ] = a ∷ []

  listTest₁ : List ℕ
  listTest₁ = []

  listTest₂ : List ℕ
  listTest₂ = zero ∷ (zero ∷ (succ zero ∷ []))

  ifthenelseTest₁ : ℕ
  ifthenelseTest₁ = if (zero + succ zero) =ℕ? zero
    then zero
    else x
    where
    x = succ (succ zero)
  
  -- ⊥ implies anything.
  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  -- Absurd implies anything, take two.
  ⊥-elim₀ : {A : Set} → ⊥ → A
  ⊥-elim₀ x = ⊥-elim x

  record Pair (A B : Set) : Set where
    field
      first  : A
      second : B

  getFirst : ∀ {A B} → Pair A B → A
  getFirst = Pair.first

  -- input for ⊤ is \top
  -- One element type. Record without fields. True proposition.
  record ⊤ : Set where

  tt : ⊤
  tt = record {}

  -- input for ‵ is \`
  -- input for ′ is \'
  ⊥-elim‵′ : {A : Set} → ⊥ → A
  ⊥-elim‵′ ∀x:⊥→-- = ⊥-elim ∀x:⊥→--

  div2 : ℕ → ℕ
  div2 zero = zero
  div2 (succ (succ n)) = succ (div2 n)
  div2 (succ zero) = zero

  even : ℕ → Set
  even zero = ⊤
  even (succ zero) = ⊥
  even (succ (succ n)) = even n
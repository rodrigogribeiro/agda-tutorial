module Cases where

data Bool : Set where
  true  : Bool
  false : Bool

¬_ : Bool → Bool
¬ true = false
¬ false = true

_∧_ : Bool → Bool → Bool
true ∧ t = t
false ∧ _ = false 

infixr 6 _∧_

_∨_ : Bool → Bool → Bool
false ∨ t = t
true ∨ _ = true

infixr 5 _∨_

-------------------------------

data Answer : Set where
  yes no maybe : Answer

anot : Answer → Answer
anot yes = no
anot no = yes
anot maybe = maybe

aand : Answer → Answer → Answer
aand yes t = t
aand no _  = no
aand maybe _ = maybe

aor : Answer → Answer → Answer
aor yes _ = yes
aor no t  = t
aor maybe t = t


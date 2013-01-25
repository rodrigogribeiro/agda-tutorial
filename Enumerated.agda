module Enumerated where

data Bool : Set where
  true : Bool
  false : Bool

-- Exercises

-- Define a set named Answer with three elements, yes, no and maybe.

data Answer : Set where
  yes : Answer
  no  : Answer
  maybe : Answer

-- Define a set named Quarter with four elements, east, west, north and south.

data Quarter : Set where
  east : Quarter
  west : Quarter
  north : Quarter
  south : Quarter

data ⊥ : Set where   -- There is no constructor.

data ⊤ : Set where
  tt : ⊤
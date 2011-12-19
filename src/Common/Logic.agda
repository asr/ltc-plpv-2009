------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Common.Logic where

-- Fixity declarations (precedence level and associativity).
-- Agda default: infix 20.

infixl 60 _∧_
infixl 50 _∨_

-- The false type.
data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ A = A → ⊥

-- The disjunction type.
-- The symbol is '\vee', not 'v'.
data _∨_ (A B : Set) : Set where
  ∨-il : A → A ∨ B
  ∨-ir : B → A ∨ B

∨-elim : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
∨-elim f g (∨-il a) = f a
∨-elim f g (∨-ir b) = g b

-- The conjunction type.
data _∧_ (A B : Set) : Set where
  ∧-i : A → B → A ∧ B

∧-fst : {A B : Set} → A ∧ B → A
∧-fst (∧-i a _) = a

∧-snd : {A B : Set} → A ∧ B → B
∧-snd (∧-i _ b) = b

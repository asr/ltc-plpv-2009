------------------------------------------------------------------------------
-- The relation of divisibility
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.Divisibility where

open import Inductive.Core
  using ( _==_ ; ==-refl ; ==-sym ; ==-trans -- from Identity
        ;  ∃ ; ∃-i ; ¬ ; _∧_ ; ∧-i ; ⊥-elim -- from Logical-Constants
        ; D ; zero ; succ
        ; N ; zN ; sN
        ; 0≠S
        )
open import Inductive.Arithmetic
  using ( _+_ ; _*_ ; _-_
        ; mult-comm ; mult-x0
        )

open import Inductive.Inequalities using ( _≤_ )

-- It seems there is not agreement about if 0∣0 (e.g. see Coq definition
-- (0∣0), Agda library (0∤0), or MathWorld (0∤0)). At the moment, in our
-- definition 0∤0.

-- The relation of divisibility.
-- The symbol is '\mid' not '|'.
{-
data _∣_ : D → D → Set where
  ∣-i : {m n : D} → ∃ D (λ k → n == k * succ m) → succ m ∣ n
-}

-- ToDo: What about change '∃' by '(k : D)'.
_∣_ : D → D → Set
m ∣ n = ¬ (m == zero) ∧ ∃ (λ k → n == k * m)

------------------------------------------------------------------------------
-- Divisibility properties
------------------------------------------------------------------------------

-- 0 doesn't divide any number.
0∤x : {n : D} → ¬ (zero ∣ n)
0∤x (∧-i 0≠0 _) = ⊥-elim (0≠0 ==-refl)

-- Any positive number divides 0.
S∣0 : {n : D} → N n → succ n ∣ zero
S∣0 {n} Nn = ∧-i (λ S=0 → 0≠S (==-sym S=0))
             (∃-i zero  (==-trans (==-sym (mult-x0 (succ n )))
                                  (mult-comm (sN Nn) zN )))

postulate

  -- If m divides n, and n is positive, then m ≤ n.
  ∣-≤ : {m n : D} → N m → N n → m ∣ (succ n) → m ≤ succ n

  -- The divisibility relation is reflexive for positive numbers.
  ∣-refl-S : {n : D} → N n → succ n ∣ succ n

  -- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
  x∣y→x∣z→x∣y+z : {m n p : D} → N m → N n → N p →
                  m ∣ n → m ∣ p → m ∣ n + p

  -- If 'x' divides 'y' and 'z' then 'x' divides 'y - z'.
  x∣y→x∣z→x∣y-z : {m n p : D} → N m → N n → N p →
                  m ∣ n → m ∣ p → m ∣ n - p

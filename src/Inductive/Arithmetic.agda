-------------------------------------------------------------------------
-- Primitive recursive functions and some types via LTC terms
-------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.Arithmetic where

open import Inductive.Core
  using ( _==_
        ; D
        ; ƛ
        ; zero ; succ ; pred
        ; N
        )

open import Inductive.Rec using ( rec ; CR₁ )

open import Inductive.Inequalities using ( _>_ ; _≤_ )

-------------------------------------------------------------------------
-- Remark: We are using Agda's definitional equality '=' as
-- LTC's definitional equality.

-- Fixity declarations (precedence level and associativity).
-- Agda default: infix 20.

infixl 70 _*_
infixl 60 _+_ _-_

-- Recursion on the second argument.
_+_ : D → D → D
m + n = rec n m (ƛ (λ x → ƛ (λ y → succ y)))

-- Recursion on the second argument.
_*_ : D → D → D
m * n = rec n zero (ƛ (λ x → ƛ (λ y → y + m)))

-- m - 0        = m
-- m - (succ n) = pred (m - n)
_-_ : D → D → D
m - n = rec n m (ƛ (λ x → ƛ (λ y → pred y)))

-------------------------------------------------------------------------
-- Some properties
-------------------------------------------------------------------------

postulate
  x>y→x-y+y=x : {x y : D} → N x → N y → x > y → (x - y) + y == x
  x≤y→y-x+x=y : {x y : D} → N x → N y → x ≤ y → (y - x) + x == y
  plus-comm   : {m n : D} → N m → N n → m + n == n + m
  mult-comm   : {m n : D} → N m → N n → m * n == n * m
  minus-N     : {m n : D} → N m → N n → N (m - n)
  mult-N      : {m n : D} → N m → N n → N (m * n)

mult-x0 : (n : D) → n * zero == zero
mult-x0 n = CR₁ zero

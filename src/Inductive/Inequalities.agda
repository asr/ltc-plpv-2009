------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.Inequalities where

open import Inductive.Core
  using ( _==_ ; ==-refl ; ==-trans ; ==-subst ; ==-sym
        ; _∨_ ; ∨-il ; ∨-ir ; ⊥ -- from Logical-Constants
        ; D
        ; true ; false ; if_then_else_ ; cB₁ ; cB₂
        ; zero ; succ ; isZero ; pred ; cZ₁ ; cZ₂ ; cP₂
        ; ƛ ; _∙_ ; cBeta
        ; fix ; cFix
        ; N ; zN ; sN
        )

import Common.EqualityReasoning
open module ER-Inequalities =
  Common.EqualityReasoning _==_ ==-refl ==-trans

-- Fixity declarations (precedence level and associativity).
-- Agda default: infix 20.

infix  40 _≻_ _≺_

------------------------------------------------------------------------------
-- '≺' on partial natural numbers
------------------------------------------------------------------------------

-- The symbol is '\prec'.
-- _        ≺ zero     = false
-- zero     ≺ (succ n) = true
-- (succ m) ≺ (succ n) = m ≺ n

lth : D → D
lth = λ lt → ƛ (λ m → ƛ (λ n →
              if (isZero n) then false
                 else (if (isZero m) then true
                          else (lt ∙ (pred m) ∙ (pred n)))))

_≺_ : D → D → D
m ≺ n = fix lth ∙ m ∙ n

-- The execution of '≺'

private

  ----------------------------------------------------------------------------
  -- The steps

  -- We follow the same methodology used in Inductive.GCD.Equations
  -- (see it for the documentation).

  -- Initially, the conversion rule 'cFix' is applied.
  ≺-s₁ : D → D → D
  ≺-s₁ m n =  lth (fix lth) ∙ m ∙ n

  -- First argument application.
  ≺-s₂ : D → D
  ≺-s₂ m = ƛ (λ n →
             if (isZero n) then false
                else (if (isZero m) then true
                         else ((fix lth) ∙ (pred m) ∙ (pred n))))


  -- Second argument application.
  ≺-s₃ : D → D → D
  ≺-s₃ m n = if (isZero n) then false
                else (if (isZero m) then true
                         else ((fix lth) ∙ (pred m) ∙ (pred n)))

  -- Reduction 'isZero n == b'.
  ≺-s₄ : D → D → D → D
  ≺-s₄ m n b = if b then false
                  else (if (isZero m) then true
                           else ((fix lth) ∙ (pred m) ∙ (pred n)))

  -- Reduction 'isZero n == true'.
  -- It should be
  -- ≺-s₅ : D → D → D
  -- ≺-s₅ m n = false
  -- but we do not give a name to this step.

  -- Reduction 'isZero n == false'.
  ≺-s₅ : D → D → D
  ≺-s₅ m n = if (isZero m) then true
                 else ((fix lth) ∙ (pred m) ∙ (pred n))


  -- Reduction 'isZero m == b'.
  ≺-s₆ : D → D → D → D
  ≺-s₆ m n b = if b then true
                  else ((fix lth) ∙ (pred m) ∙ (pred n))

  -- Reduction 'isZero m == true'
  -- It should be
  -- ≺-s₇ : D → D → D
  -- ≺-s₇ m n = true
  -- but we do not give a name to this step.

   -- Reduction 'isZero m == false'.
  ≺-s₇ : D → D → D
  ≺-s₇ m n = (fix lth) ∙ (pred m) ∙ (pred n)

  -- Reduction 'pred (succ m) == m'.
  ≺-s₈ : D → D → D
  ≺-s₈ m n = (fix lth) ∙ m ∙ (pred n)

  -- Reduction 'pred (succ n) == n'.
  ≺-s₉ : D → D → D
  ≺-s₉ m n = (fix lth) ∙ m ∙ n

  ----------------------------------------------------------------------------
  -- The execution steps

  -- We follow the same methodology used in Inductive.GCD.Equations
  -- (see it for the documentation).

  -- Application of the conversion rule 'cFix'.
  proof₀₋₁ : (m n : D) → fix lth ∙ m ∙ n  == ≺-s₁ m n
  proof₀₋₁ m n = ==-subst (λ x → x ∙ m ∙ n  ==
                                 lth (fix lth) ∙ m ∙ n )
                          (==-sym (cFix lth ))
                          ==-refl

  -- Application of the first argument.
  proof₁₋₂ : (m n : D) → ≺-s₁ m n == ≺-s₂ m ∙ n
  proof₁₋₂ m n = ==-subst (λ x → x ∙ n == ≺-s₂ m ∙ n)
                          (==-sym (cBeta ≺-s₂ m))
                          ==-refl

  -- Application of the second argument.
  proof₂₋₃ : (m n : D) → ≺-s₂ m ∙ n == ≺-s₃ m n
  proof₂₋₃ m n = cBeta (≺-s₃ m) n


  -- Reduction 'isZero n == b' using that proof.
  proof₃₋₄ : (m n b : D) → isZero n == b →
             ≺-s₃ m n == ≺-s₄ m n b
  proof₃₋₄ m n b prf = ==-subst (λ x → ≺-s₄ m n x == ≺-s₄ m n b )
                                (==-sym prf )
                                ==-refl

  -- Reduction of 'isZero n == true' using the conversion rule 'cB₁'.
  proof₄₊ : (m n : D) → ≺-s₄ m n true == false
  proof₄₊ m n = cB₁ false

  -- Reduction of 'isZero n == false ...' using the conversion rule 'cB₂'.
  proof₄₋₅ : (m n : D) → ≺-s₄ m n false == ≺-s₅ m n
  proof₄₋₅ m n = cB₂ (≺-s₅ m n)


  -- Reduction 'isZero m == b' using that proof.
  proof₅₋₆ : (m n b : D) → isZero m == b →
             ≺-s₅ m n == ≺-s₆ m n b
  proof₅₋₆ m n b prf = ==-subst (λ x → ≺-s₆ m n x == ≺-s₆ m n b )
                                (==-sym prf )
                                ==-refl

  -- Reduction of 'isZero m == true' using the conversion rule 'cB₁'.
  proof₆₊ : (m n : D) → ≺-s₆ m n true == true
  proof₆₊ m n = cB₁ true

  -- Reduction of 'isZero m == false ...' using the conversion rule 'cB₂'.
  proof₆₋₇ : (m n : D) → ≺-s₆ m n false == ≺-s₇ m n
  proof₆₋₇ m n = cB₂ (≺-s₇ m n)

  -- Reduction 'pred (succ m) == m' using the conversion rule 'cP₂'.
  proof₇₋₈ : (m n : D) → ≺-s₇ (succ m) n  == ≺-s₈ m n
  proof₇₋₈ m n = ==-subst (λ x → ≺-s₈ x n == ≺-s₈ m n)
                          (==-sym (cP₂ m ))
                            ==-refl

  -- Reduction 'pred (succ n) == n' using the conversion rule 'cP₂'.
  proof₈₋₉ : (m n : D) → ≺-s₈ m (succ n)  == ≺-s₉ m n
  proof₈₋₉ m n = ==-subst (λ x → ≺-s₉ m x == ≺-s₉ m n)
                          (==-sym (cP₂ n ))
                          ==-refl

------------------------------------------------------------------------------
-- Some properties of '≺'
------------------------------------------------------------------------------

-- ToDo: It works for *any* 'x'.
x≺0=false : (n : D) → n ≺ zero == false
x≺0=false n =
  chain> (fix lth ∙ n ∙ zero)
    === ≺-s₁ n zero        by proof₀₋₁ n zero
    === ≺-s₂ n ∙ zero      by proof₁₋₂ n zero
    === ≺-s₃ n zero        by proof₂₋₃ n zero
    === ≺-s₄ n zero true   by proof₃₋₄ n zero true cZ₁
    === false              by proof₄₊ n zero
  qed

0≺S=true : (n : D) → zero ≺ succ n == true
0≺S=true n =
  chain> (fix lth ∙ zero ∙ (succ n))
    === ≺-s₁ zero (succ n)        by proof₀₋₁ zero (succ n)
    === ≺-s₂ zero ∙ (succ n)      by proof₁₋₂ zero (succ n)
    === ≺-s₃ zero (succ n)        by proof₂₋₃ zero (succ n)
    === ≺-s₄ zero (succ n) false  by proof₃₋₄ zero (succ n) false (cZ₂ n)
    === ≺-s₅ zero (succ n)        by proof₄₋₅ zero (succ n)
    === ≺-s₆ zero (succ n) true   by proof₅₋₆ zero (succ n) true cZ₁
    === true                      by proof₆₊  zero (succ n)
  qed

Sx≺Sy=x≺y : (m n : D) → succ m ≺ succ n == m ≺ n
Sx≺Sy=x≺y m n =
  chain> (fix lth ∙ (succ m) ∙ (succ n))
    === ≺-s₁ (succ m) (succ n)        by proof₀₋₁ (succ m) (succ n)
    === ≺-s₂ (succ m) ∙ (succ n)      by proof₁₋₂ (succ m) (succ n)
    === ≺-s₃ (succ m) (succ n)        by proof₂₋₃ (succ m) (succ n)
    === ≺-s₄ (succ m) (succ n) false  by proof₃₋₄ (succ m) (succ n)
                                                  false (cZ₂ n)
    === ≺-s₅ (succ m) (succ n)        by proof₄₋₅ (succ m) (succ n)
    === ≺-s₆ (succ m) (succ n) false  by proof₅₋₆ (succ m) (succ n)
                                                  false (cZ₂ m)
    === ≺-s₇ (succ m) (succ n)        by proof₆₋₇ (succ m) (succ n)
    === ≺-s₈ m (succ n)               by proof₇₋₈ m (succ n)
    === ≺-s₉ m n                      by proof₈₋₉ m n
  qed

------------------------------------------------------------------------------
-- '≻' on partial natural numbers
------------------------------------------------------------------------------

-- The symbol is '\succ'.
_≻_ : D → D → D
m ≻ n = n ≺ m

------------------------------------------------------------------------------
-- Some data types
------------------------------------------------------------------------------

_>_ : D → D → Set
m > n = m ≻ n == true

_<_ : D → D  → Set
m < n = m ≺ n == true

_≤_ : D → D → Set
m ≤ n = m ≻ n == false

_≥_ : D → D → Set
m ≥ n = m ≺ n == false

------------------------------------------------------------------------------
-- Some properties
------------------------------------------------------------------------------

x>y∨x≤y : {m n : D} → N m → N n → (m > n) ∨ (m ≤ n)
x>y∨x≤y {n = n} zN          _           = ∨-ir (x≺0=false n)
x>y∨x≤y         (sN {m} Nm) zN          = ∨-il (0≺S=true m)
x>y∨x≤y         (sN {m} Nm) (sN {n} Nn) =
  ==-subst (λ a → (a == true) ∨ (a == false))
           (==-sym (Sx≺Sy=x≺y n m))
           (x>y∨x≤y Nm Nn )

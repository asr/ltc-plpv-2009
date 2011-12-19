------------------------------------------------------------------------------
-- Agda as a logical framework for LTC

-- LTC                              Agda
-- * Logical constants              * Curry-Howard isomorphism
-- * Equality                       * Identity type
-- * Term language                  * Postulates
-- * Inductive predicates           * Inductive families
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.Core where

-- Fixity declarations (precedence level and associativity).
-- Agda default: infix 20.
infixl 80 _∙_
infix  30 _==_
infix  40 if_then_else_

------------------------------------------------------------------------------
-- The universal domain
------------------------------------------------------------------------------

postulate D : Set

------------------------------------------------------------------------------
-- Equality: identity type
------------------------------------------------------------------------------

-- The LTC's equality is the propositional identity on 'D'.

-- The identity type.
data _==_ (x : D) : D → Set where
  ==-refl : x == x

-- Identity properties.

==-subst : (P : D → Set){x y : D} → x == y → P x → P y
==-subst P ==-refl px = px

==-sym : {x y : D} → x == y →  y == x
==-sym ==-refl = ==-refl

==-trans : {x y z : D} → x == y → y == z → x == z
==-trans ==-refl y==z  = y==z

------------------------------------------------------------------------------
-- Logical constants: Curry-Howard isomorphism
------------------------------------------------------------------------------

-- The LTC's logical constants are the type theory's logical
-- constants via the Curry-Howard isomorphism.
-- For the implication and the universal quantifier
-- we use Agda (dependent) function type.
-- Note that the module 'Common.Logic' is exported by this module.
open import Common.Logic public

-- The existential quantifier type on 'D'
data ∃ (P : D → Set) : Set where
  ∃-i : (witness : D)  → P witness → ∃ P

∃-fst : {P : D → Set} → ∃ P → D
∃-fst (∃-i x px) = x

∃-snd : {P : D → Set} → (x-px : ∃ P) → P (∃-fst x-px)
∃-snd (∃-i x px) = px


------------------------------------------------------------------------------
--  The term language: postulates
------------------------------------------------------------------------------

-- The term language of LTC correspond to the PCF terms

--   t ::= x | t t | \x -> t
--           | true | false | if t then t else t
--           | 0 | succ t | pred t | isZero t
--           | error
--           | fix x. t

-- The fixed point operator 'fix' binds a variable, and we have
-- 'error' for explicit error handling.

--------------------
-- The terms

postulate

  -- LTC partial booleans.
  true          : D
  false         : D
  if_then_else_ : D → D → D → D

  -- LTC partial natural numbers.
  zero   : D
  succ   : D → D
  pred   : D → D
  isZero : D → D

  -- LTC abstraction.
  ƛ : (D → D) → D

  -- LTC application
  -- Left associative aplication operator
  -- The Agda application has higher precedence level than LTC application

  _∙_ : D → D → D

  -- LTC error
  error : D

  -- LTC fixed point operator
  fix : (D → D) → D

----------------------
-- Conversion rules

postulate
  -- Conversion rules for booleans.
  cB₁ : (a : D){b : D} → if true then a else b  == a
  cB₂ : {a : D}(b : D) → if false then a else b == b

  -- Conversion rules for natural numbers.
  cP₁ : pred zero               == zero
  cP₂ : (n : D) → pred (succ n) == n

  cZ₁ : isZero zero               == true
  cZ₂ : (n : D) → isZero (succ n) == false

  -- Conversion rule for the abstraction and the application.
  cBeta : (f : D → D)(a : D) → (ƛ f) ∙ a == f a

  -- Conversion rule for the fixed pointed operator.
  cFix : (f : D → D) → fix f == f (fix f)

-------------------------
-- Discrimination rules

postulate
  true≠false : ¬ (true == false)
  0≠S        : {n : D} → ¬ ( zero == succ n)

------------------------------------------------------------------------------
-- Inductive predicate for booleans : Inductive family
------------------------------------------------------------------------------

-- The booleans type.
data B : D → Set where
  tB : B true
  fB : B false

-- The rule of proof by case analysis on 'B'.
if : (P : D → Set) → P true → P false →
     {b : D} → B b → P b
if P pt pf tB = pt
if P pt pf fB = pf

------------------------------------------------------------------------------
-- Inductive predicate for natural numbers : Inductive family
------------------------------------------------------------------------------

-- The inductive predicate 'N' represents the type of the natural
-- numbers. They are a subset of 'D'.

-- The natural numbers type.
data N : D → Set where
  zN : N zero
  sN : {n : D} → N n → N (succ n)

-- Induction principle on 'N'  (elimination rule).
indN : (P : D → Set) →
       P zero →
       ({n : D} → N n → P n → P (succ n)) →
       {n : D} → N n → P n
indN P p0 h zN      = p0
indN P p0 h (sN Nn) = h Nn (indN P  p0  h Nn)

------------------------------------------------------------------------------
-- The five equations for the gcd
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.GCD.Equations where

open import Inductive.Core
  using ( _==_ ; ==-refl ; ==-subst ; ==-sym ; ==-trans
        ; D
        ; true ; false ; if_then_else_ ; cB₁ ; cB₂
        ; zero ; succ ; isZero ; cZ₁ ; cZ₂
        ; ƛ ; _∙_ ; cBeta
        ; fix ; cFix
        ; error
        ; N ; zN ; sN
        )

open import Inductive.Inequalities using ( _≻_ ; _>_ ; _≤_ )
open import Inductive.Arithmetic using ( _-_ )

import Common.EqualityReasoning
open module ER-GCD = Common.EqualityReasoning _==_ ==-refl ==-trans

open import Inductive.GCD.Definition using ( gcdh ; gcd )

private
  -- Before to prove some properties for 'gcd i j' it is convenient
  -- to descompose the behavior of the function step by step.

  -- Initially, we define the possible states ('gcd-s₁',
  -- 'gcd-s₂', ...). Then we write down the proof for
  -- the execution step from the state 'p' to the state 'q'
  -- (e.g 'proof₂₋₃ : (m n : D) → gcd-s₂ m n → gcd-s₃ m n' ).

  -- The functions 'gcd-00', 'gcd-Sm0', 'gcd-0Sn', 'gcd-m>n' and
  -- 'gcd-m>n' show the use of the states 'gcd-s₁', 'gcd-s₂', ..., and the
  -- proofs associated with the execution steps.

  ----------------------------------------------------------------------------
  -- The steps

  -- Initially, the conversion rule 'cFix' is applied.
  gcd-s₁ : D → D → D
  gcd-s₁ m n = gcdh (fix gcdh) ∙ m ∙ n

  -- First argument application.
  gcd-s₂ : D → D
  gcd-s₂ m = ƛ (λ n →
               if (isZero n)
                  then (if (isZero m)
                           then error
                           else m)
                  else (if (isZero m)
                           then n
                           else (if (m ≻ n)
                                    then fix gcdh ∙ (m - n) ∙ n
                                    else fix gcdh ∙ m ∙ (n - m))))

  -- Second argument application.
  gcd-s₃ : D → D → D
  gcd-s₃ m n = if (isZero n)
                  then (if (isZero m)
                           then error
                           else m)
                  else (if (isZero m)
                           then n
                           else (if (m ≻ n)
                                    then fix gcdh ∙ (m - n) ∙ n
                                    else fix gcdh ∙ m ∙ (n - m)))

  -- Conversion (first if_then_else) 'isZero n = b'.
  gcd-s₄ : D → D → D → D
  gcd-s₄ m n b = if b
                  then (if (isZero m)
                           then error
                           else m)
                  else (if (isZero m)
                           then n
                           else (if (m ≻ n)
                                    then fix gcdh ∙ (m - n) ∙ n
                                    else fix gcdh ∙ m ∙ (n - m)))

  -- Conversion first if_then_else when 'if true ...'.
  gcd-s₅ : D → D
  gcd-s₅ m  = if (isZero m) then error else m

  -- Conversion first if_then_else when 'if false ...'.
  gcd-s₆ : D → D → D
  gcd-s₆ m n = if (isZero m)
                  then n
                  else (if (m ≻ n)
                           then fix gcdh ∙ (m - n) ∙ n
                           else fix gcdh ∙ m ∙ (n - m))

  -- Conversion (second if_then_else) 'isZero m = b'.
  gcd-s₇ : D → D → D
  gcd-s₇ m b = if b then error else m

  -- Conversion (third if_then_else) 'isZero m = b'.
  gcd-s₈ : D → D → D → D
  gcd-s₈ m n b = if b
                    then n
                    else (if (m ≻ n)
                             then fix gcdh ∙ (m - n) ∙ n
                             else fix gcdh ∙ m ∙ (n - m))

  -- Conversion third if_then_else, when 'if false ...'.
  gcd-s₉ : D → D → D
  gcd-s₉ m n = if (m ≻ n)
                   then fix gcdh ∙ (m - n) ∙ n
                   else fix gcdh ∙ m ∙ (n - m)

  -- Conversion (fourth if_then_else) 'gt m n = b'.
  gcd-s₁₀ : D → D → D → D
  gcd-s₁₀ m n b = if b
                     then fix gcdh ∙ (m - n) ∙ n
                     else fix gcdh ∙ m ∙ (n - m)

  ----------------------------------------------------------------------------
  -- The execution steps

  {-
  To prove the execution steps
  (e.g. proof₃₋₄ : (m n : D) → gcd-s₃ m n → gcd_s₄ m n),
  we usually need to prove that

                         C [m]  == C [n]    (1)

  given that
                             m == n,              (2)

  where (2) is a conversion rule usually.
  We prove (1) using
  '==-subst : {A : Set}(P : A → Set){x y : A} → x == y → P x → P y'
  where
  'P' is given by 'λ m → C [m ] == C [n]',
  'x == y' is given 'n == m' (actually, we use '==-sym (m == n)'), and
  'P x' is given by 'C [n] == C [n]' (i.e. '==-refl').
  -}

  -- Application of the conversion rule 'cFix'.
  proof₀₋₁ : (m n : D) → fix gcdh ∙ m ∙ n  == gcd-s₁ m n
  proof₀₋₁ m n = ==-subst (λ x → x ∙ m ∙ n == gcdh (fix gcdh) ∙ m ∙ n )
                          (==-sym (cFix gcdh ))
                          ==-refl

  -- Application of the first argument.
  proof₁₋₂ : (m n : D) → gcd-s₁ m n == gcd-s₂ m ∙ n
  proof₁₋₂ m n = ==-subst (λ x → x ∙ n == gcd-s₂ m ∙ n)
                          (==-sym (cBeta gcd-s₂ m ))
                          ==-refl

  -- Second argument application.
  proof₂₋₃ : (m n : D) → gcd-s₂ m ∙ n == gcd-s₃ m n
  proof₂₋₃ m n  = cBeta (gcd-s₃ m) n

  -- Conversion (first if_then_else) 'isZero n = b' using that proof.
  proof₃₋₄ : (m n b : D) → isZero n == b  → gcd-s₃ m n == gcd-s₄ m n b
  proof₃₋₄ m n b prf = ==-subst (λ x → gcd-s₄ m n x == gcd-s₄ m n b )
                                (==-sym prf )
                                ==-refl

  -- Conversion first if_then_else when 'if true ...' using cB₁.
  proof₄₋₅ : (m n : D) → gcd-s₄ m n true == gcd-s₅ m
  proof₄₋₅ m _ = cB₁ (gcd-s₅ m)

  -- Conversion first if_then_else when 'if false ...' using cB₂.
  proof₄₋₆ : (m n : D) → gcd-s₄ m n false == gcd-s₆ m n
  proof₄₋₆ m n = cB₂ (gcd-s₆ m n)

  -- -- Conversion (second if_then_else) 'isZero m = b' using that proof.
  proof₅₋₇ : (m b : D) → isZero m == b  → gcd-s₅ m  == gcd-s₇ m b
  proof₅₋₇ m b prf = ==-subst (λ x → gcd-s₇ m x == gcd-s₇ m b )
                              (==-sym prf )
                              ==-refl

  -- Conversion (third if_then_else) 'isZero m = b' using that proof.
  proof₆₋₈ : (m n b : D) → isZero m == b  → gcd-s₆ m n == gcd-s₈ m n b
  proof₆₋₈ m n b prf = ==-subst (λ x → gcd-s₈ m n x == gcd-s₈ m n b )
                              (==-sym prf )
                              ==-refl

  -- Conversion second if_then_else when 'if true ...' using cB₁.
  proof₇₊ : (m : D) → gcd-s₇ m true == error
  proof₇₊ _ = cB₁ error

  -- Conversion second if_then_else when 'if false ...' using cB₂.
  proof₇₋ : (m : D) → gcd-s₇ m false == m
  proof₇₋ m = cB₂ m

  -- Conversion third if_then_else when 'if true ...' using cB₁.
  proof₈₊ : (m n : D) → gcd-s₈ m n true == n
  proof₈₊ _ n = cB₁ n

  -- Conversion third if_then_else when 'if false ...' using cB₂.
  proof₈₋₉ : (m n : D) → gcd-s₈ m n false == gcd-s₉ m n
  proof₈₋₉ m n = cB₂ (gcd-s₉ m n)

  -- Conversion (fourth if_then_else) 'gt m n = b' using that proof.
  proof₉₋₁₀ : (m n b : D) → m ≻ n == b  → gcd-s₉ m n == gcd-s₁₀ m n b
  proof₉₋₁₀ m n b prf = ==-subst (λ x → gcd-s₁₀ m n x == gcd-s₁₀ m n b )
                                  (==-sym prf )
                                  ==-refl

  -- Conversion fourth if_then_else when 'if true ...' using cB₁.
  proof₁₀₊ : (m n : D) → gcd-s₁₀ m n true == fix gcdh ∙ (m - n) ∙ n
  proof₁₀₊ m n = cB₁ (fix gcdh ∙ (m - n) ∙ n)

  -- Conversion fourth if_then_else when 'if was ...' using cB₂.
  proof₁₀₋ : (m n : D) → gcd-s₁₀ m n false == fix gcdh ∙ m ∙ (n - m)
  proof₁₀₋ m n = cB₂ (fix gcdh ∙ m ∙ (n - m))

------------------------------------------------------------------------------
-- The five equations for gcd
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- First equation.
-- We do not use this equation for reasoning about gcd.
gcd-00 : gcd zero zero == error
gcd-00 =
  chain> gcd zero zero
    === gcd-s₁ zero zero        by proof₀₋₁ zero zero
    === gcd-s₂ zero ∙ zero      by proof₁₋₂ zero zero
    === gcd-s₃ zero zero        by proof₂₋₃ zero zero
    === gcd-s₄ zero zero true   by proof₃₋₄ zero zero true cZ₁
    === gcd-s₅ zero             by proof₄₋₅ zero zero
    === gcd-s₇ zero true        by proof₅₋₇ zero true cZ₁
    === error                   by proof₇₊ zero
  qed

------------------------------------------------------------------------------
-- Second equation.
gcd-S0 : {m : D} → N m → gcd (succ m) zero == succ m
gcd-S0 {m} _ =
  chain> gcd (succ m) zero
    === gcd-s₁  (succ m) zero        by proof₀₋₁  (succ m) zero
    === gcd-s₂  (succ m) ∙ zero      by proof₁₋₂  (succ m) zero
    === gcd-s₃  (succ m) zero        by proof₂₋₃  (succ m) zero
    === gcd-s₄  (succ m) zero true   by proof₃₋₄  (succ m) zero true cZ₁
    === gcd-s₅  (succ m)             by proof₄₋₅  (succ m) zero
    === gcd-s₇  (succ m) false       by proof₅₋₇  (succ m) false (cZ₂ m)
    === succ m                       by proof₇₋   (succ m)
  qed

------------------------------------------------------------------------------
-- Third equation.
gcd-0S : {n : D} → N n → gcd zero (succ n) == succ n
gcd-0S {n} _ =
  chain> gcd zero (succ n)
    === gcd-s₁  zero (succ n)         by proof₀₋₁ zero (succ n)
    === gcd-s₂  zero ∙ (succ n)       by proof₁₋₂ zero (succ n)
    === gcd-s₃  zero (succ n)         by proof₂₋₃ zero (succ n)
    === gcd-s₄  zero (succ n) false   by proof₃₋₄ zero (succ n) false (cZ₂ n)
    === gcd-s₆  zero (succ n)         by proof₄₋₆ zero (succ n)
    === gcd-s₈  zero (succ n) true    by proof₆₋₈ zero (succ n) true cZ₁
    === (succ n)                      by proof₈₊  zero (succ n)
  qed

------------------------------------------------------------------------------
-- Fourth equation.

gcd-S>S : {m n : D} → N m → N n → (succ m > succ n) →
          gcd (succ m) (succ n) == gcd (succ m - succ n) (succ n)

gcd-S>S {m} {n} Nm Nn Sm>Sn =
  chain> gcd (succ m) (succ n)
    === gcd-s₁  (succ m) (succ n)              by proof₀₋₁  (succ m) (succ n)
    === gcd-s₂  (succ m) ∙ (succ n)            by proof₁₋₂  (succ m) (succ n)
    === gcd-s₃  (succ m) (succ n)              by proof₂₋₃  (succ m) (succ n)
    === gcd-s₄  (succ m) (succ n) false        by proof₃₋₄  (succ m) (succ n)
                                                            false (cZ₂ n)
    === gcd-s₆  (succ m) (succ n)              by proof₄₋₆  (succ m) (succ n)
    === gcd-s₈  (succ m) (succ n) false        by proof₆₋₈  (succ m) (succ n)
                                                            false (cZ₂ m)
    === gcd-s₉ (succ m) (succ n)               by proof₈₋₉  (succ m) (succ n)
    === gcd-s₁₀ (succ m) (succ n) true         by proof₉₋₁₀ (succ m) (succ n)
                                                            true Sm>Sn
    === fix gcdh ∙ (succ m - succ n) ∙ succ n  by proof₁₀₊  (succ m) (succ n)
  qed

------------------------------------------------------------------------------
-- Fifth equation.

gcd-S≤S : {m n : D} → N m → N n → succ m ≤ succ n →
          gcd (succ m) (succ n)  == gcd (succ m) (succ n - succ m)
gcd-S≤S {m} {n} Nm Nn Sm≤Sn =
  chain> gcd (succ m) (succ n)
    === gcd-s₁  (succ m) (succ n)               by proof₀₋₁  (succ m) (succ n)
    === gcd-s₂  (succ m) ∙ (succ n)             by proof₁₋₂  (succ m) (succ n)
    === gcd-s₃  (succ m) (succ n)               by proof₂₋₃  (succ m) (succ n)
    === gcd-s₄  (succ m) (succ n) false         by proof₃₋₄  (succ m) (succ n)
                                                             false (cZ₂ n)
    === gcd-s₆  (succ m) (succ n)               by proof₄₋₆  (succ m) (succ n)
    === gcd-s₈  (succ m) (succ n) false         by proof₆₋₈  (succ m) (succ n)
                                                             false (cZ₂ m)
    === gcd-s₉ (succ m) (succ n)                by proof₈₋₉  (succ m) (succ n)
    === gcd-s₁₀ (succ m) (succ n) false         by proof₉₋₁₀ (succ m) (succ n)
                                                             false Sm≤Sn
    === fix gcdh ∙ succ m ∙ (succ n - succ m)   by proof₁₀₋  (succ m) (succ n)
  qed

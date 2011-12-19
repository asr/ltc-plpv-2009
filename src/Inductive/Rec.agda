------------------------------------------------------------------------------
-- The primitive recursive combinator 'rec' and its conversion
-- rules 'CR₁' and 'CR₂'
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.Rec where

open import Inductive.Core
  using ( _==_ ; ==-refl ; ==-trans ; ==-subst ; ==-sym
        ; D
        ; true ; false ; if_then_else_ ; cB₁ ; cB₂
        ; zero ; succ ; isZero ; pred ; cZ₁ ; cZ₂ ; cP₂
        ; ƛ ; _∙_ ; cBeta
        ; fix ; cFix
        )

import Common.EqualityReasoning
open module ER-Rec = Common.EqualityReasoning _==_ ==-refl ==-trans

------------------------------------------------------------------------------
-- The 'rec' definition using the fixed point combinator
------------------------------------------------------------------------------

rech : D → D
rech r = ƛ (λ n → ƛ (λ a → ƛ (λ f →
           (if (isZero n)
               then a
               else f ∙ (pred n) ∙ (r ∙ (pred n) ∙ a ∙ f)))))

rec : D → D → D → D
rec n a f = fix rech ∙ n ∙ a ∙ f

------------------------------------------------------------------------------
-- The conversion rules for 'rec'
------------------------------------------------------------------------------

private

  ----------------------------------------------------------------------------
  -- The steps

  -- We follow the same methodology used in Inductive.GCD.Equations
  -- (see it for the documentation).

  -- Initially, the conversion rule 'cFix' is applied.
  rec-s₁ : D → D → D → D
  rec-s₁ n a f =  rech (fix rech) ∙ n ∙ a ∙ f

  -- First argument application.
  rec-s₂ : D → D
  rec-s₂ n = ƛ (λ a → ƛ (λ f →
               (if (isZero n)
                   then a
                   else f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f))))

  -- Second argument application.
  rec-s₃ : D → D → D
  rec-s₃ n a = ƛ (λ f →
                  (if (isZero n)
                      then a
                      else f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f)))

  -- Third argument application.
  rec-s₄ : D → D → D → D
  rec-s₄ n a f = if (isZero n)
                     then a
                     else f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f)

  -- Reduction 'isZero n == b'.
  rec-s₅ : D → D → D → D → D
  rec-s₅ n a f b = if b
                      then a
                      else f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f)

  -- Reduction of 'isZero n == true'
  -- It should be
  -- rec-s₆ : D → D → D → D
  -- rec-s₆ n a f = a
  -- but we do not give a name to this step.

  -- Reduction 'isZero n == false'.
  rec-s₆ : D → D → D → D
  rec-s₆ n a f = f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f)

  -- Reduction 'pred (succ n) == n'.
  rec-s₇ : D → D → D → D
  rec-s₇ n a f = f ∙ n ∙ ((fix rech) ∙ n ∙ a ∙ f)

  ----------------------------------------------------------------------------
  -- The execution steps

  -- We follow the same methodology used in Inductive.GCD.Equations
  -- (see it for the documentation).

  -- Application of the conversion rule 'cFix'.
  proof₀₋₁ : (n a f : D) → fix rech ∙ n ∙ a ∙ f == rec-s₁ n a f
  proof₀₋₁ n a f = ==-subst (λ x → x ∙ n ∙ a ∙ f  ==
                                   rech (fix rech) ∙ n ∙ a ∙ f )
                            (==-sym (cFix rech ))
                            ==-refl

  -- Application of the first argument.
  proof₁₋₂ : (n a f : D) → rec-s₁ n a f == rec-s₂ n ∙ a ∙ f
  proof₁₋₂ n a f = ==-subst (λ x → x ∙ a ∙ f == rec-s₂ n ∙ a ∙ f )
                            (==-sym (cBeta rec-s₂ n) )
                            ==-refl

  -- Application of the second argument.
  proof₂₋₃ : (n a f : D) → rec-s₂ n ∙ a ∙ f == rec-s₃ n a ∙ f
  proof₂₋₃ n a f = ==-subst (λ x → x ∙ f == rec-s₃ n a ∙ f )
                            (==-sym (cBeta (rec-s₃ n) a))
                            ==-refl

  -- Application of the third argument.
  proof₃₋₄ : (n a f : D) → rec-s₃ n a ∙ f == rec-s₄ n a f
  proof₃₋₄ n a f = cBeta (rec-s₄ n a) f

  -- Cases 'isZero n == b' using that proof.
  proof₄₋₅ : (n a f b : D) → isZero n == b →
             rec-s₄ n a f == rec-s₅ n a f b
  proof₄₋₅ n a f b prf = ==-subst (λ x → rec-s₅ n a f x == rec-s₅ n a f b )
                                (==-sym prf )
                                ==-refl

  -- Reduction of 'if true ...' using the conversion rule 'cB₁'.
  proof₅₊ : (n a f : D) → rec-s₅ n a f true == a
  proof₅₊ n a f = cB₁ a

   -- Reduction of 'if false ...' using the conversion rule 'cB₂'.
  proof₅₋₆ : (n a f : D) → rec-s₅ n a f false == rec-s₆ n a f
  proof₅₋₆ n a f = cB₂ (rec-s₆ n a f)

  -- Reduction 'pred (succ n) == n' using the conversion rule 'cP₂'.
  proof₆₋₇ : (n a f : D) → rec-s₆ (succ n) a f  == rec-s₇ n a f
  proof₆₋₇ n a f = ==-subst (λ x → rec-s₇ x a f == rec-s₇ n a f)
                            (==-sym (cP₂ n ))
                            ==-refl

------------------------------------------------------------------------------
-- The conversion rules for 'rec'.

CR₁ : (a : D){f : D} → rec zero a f == a
CR₁ a {f} =
  chain> (fix rech ∙ zero ∙ a ∙ f)
    === rec-s₁ zero a f        by proof₀₋₁ zero a f
    === rec-s₂ zero ∙ a ∙ f    by proof₁₋₂ zero a f
    === rec-s₃ zero a ∙ f      by proof₂₋₃ zero a f
    === rec-s₄ zero a f        by proof₃₋₄ zero a f
    === rec-s₅ zero a f true   by proof₄₋₅ zero a f true cZ₁
    === a                      by proof₅₊ zero a f
  qed

CR₂ : (n a f : D) → rec (succ n) a f == f ∙ n ∙ (rec n a f)
CR₂ n a f =
  chain> (fix rech ∙ (succ n) ∙ a ∙ f)
    === rec-s₁ (succ n) a f        by proof₀₋₁ (succ n) a f
    === rec-s₂ (succ n) ∙ a ∙ f    by proof₁₋₂ (succ n) a f
    === rec-s₃ (succ n) a ∙ f      by proof₂₋₃ (succ n) a f
    === rec-s₄ (succ n) a f        by proof₃₋₄ (succ n) a f
    === rec-s₅ (succ n) a f false  by proof₄₋₅ (succ n) a f false (cZ₂ n)
    === rec-s₆ (succ n) a f        by proof₅₋₆ (succ n) a f
    === rec-s₇ n a f               by proof₆₋₇ n a f
  qed

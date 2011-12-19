------------------------------------------------------------------------------
-- Euclid's algorithm for calculate the gcd using repetead subtraction
-- and fixed pointed operator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.GCD.Definition where

open import Inductive.Core
  using ( D
        ; if_then_else_
        ; ƛ ; _∙_
        ; isZero
        ; error
        ; fix
        )

open import Inductive.Arithmetic using ( _-_ )

open import Inductive.Inequalities using ( _≻_ )

{-
It is possible to define two different versions of gcd based on which
(partial) order on natural numbers we are considering. In one version,
'gcd 0 0' is defined (e.g. in Coq standard library), and in the other
version, it isn't defined (e.g. in Agda library). We followed the
approach of the Agda library.
-}

-- Instead of define
-- 'gcdh : ((D → D → D) → (D → D → D)) → D → D → D', we use the LTC
-- abstraction ('λ') and application ('∙') to avoid use a polymorphic fixed
-- point operator.
gcdh : D → D
gcdh = λ g → ƛ (λ m → ƛ (λ n →
           if (isZero n)
              then (if (isZero m)
                       then error
                       else m)
              else (if (isZero m)
                       then n
                       else (if (m ≻ n)
                                then g ∙ (m - n) ∙ n
                                else g ∙ m ∙ (n - m)))))

gcd : D → D → D
gcd m n = fix gcdh ∙ m ∙ n

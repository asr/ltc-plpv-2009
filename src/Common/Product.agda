------------------------------------------------------------------------------
-- Product data type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Common.Product where

open import Common.Logic using ( _∧_ ; ∧-i ; ∧-fst ; ∧-snd )

-- The product data type is the conjunction data type.
-- The symbol is '\times', not is 'x'.
_×_ : (A B : Set) →  Set
_×_ = _∧_

_,_ : {A B : Set} → A → B → A × B
_,_ = ∧-i

×-fst : {A B : Set} → A × B → A
×-fst = ∧-fst

×-snd : {A B : Set} → A × B → B
×-snd = ∧-snd

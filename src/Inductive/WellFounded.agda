------------------------------------------------------------------------------
-- Well-founded induction on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.WellFounded where

open import Inductive.Core using ( _==_; D ; N ; succ )
open import Common.Product using ( _×_ ; _,_ )
open import Inductive.Inequalities using ( _<_ ; _≤_ ; _>_ )
open import Inductive.Arithmetic using ( _-_ )

------------------------------------------------------------------------------
-- Lexicographical order on 'D'
------------------------------------------------------------------------------

data _<₂_ : D × D → D × D → Set where
  <₂-x : (x y x' y' : D) → x < x' → (x , y) <₂ (x' , y')
  <₂-y : (x y x' y' : D) → x == x → y < y' → (x , y) <₂ (x' , x')

postulate
  Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] : {m n : D} → N m → N n → succ m ≤ succ n →
                              (succ m , succ n - succ m) <₂ (succ m , succ n)
  Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] : {m n : D} → N m → N n → succ m > succ n →
                              (succ m - succ n , succ n) <₂ (succ m , succ n)

------------------------------------------------------------------------------
-- Well-founded induction on 'N'
------------------------------------------------------------------------------

postulate
  wfN : (P : D → Set) →
        ({n : D} → N n → ({m : D} → N m → m < n → P m) → P n) →
        {n : D} → N n  → P n

------------------------------------------------------------------------------
-- Well-founded induction on pairs of 'N'
------------------------------------------------------------------------------

postulate
 wf₂N :
    (P : D → D → Set) →
    ({m n : D} → N m → N n →
        ({m' n' : D} → N m' → N n' → (m' , n') <₂ (m , n) → P m' n')
          → P m n
    ) →
    {m n : D} → N m → N n → P m n

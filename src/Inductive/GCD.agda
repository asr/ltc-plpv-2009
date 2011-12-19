------------------------------------------------------------------------------
-- Specification of the Euclid's algorithm for calculate the greatest
-- common divisor of two natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Inductive.GCD where

open import Inductive.Core
  using ( _==_ ; ==-refl ; ==-subst ; ==-sym ; ==-trans -- from Identity
        ; ⊥-elim -- from Identity
        ; _∨_ ; ∨-il ; ∨-ir ; ∨-elim -- from Logical-Constants
        ; _∧_ ; ∧-i ; ∧-fst ; ∧-snd  -- from Logical-Constants
        ; ¬ -- from Logical-Constants
        ; D
        ; zero ; succ
        ; N ; zN ; sN
        ; error
        ; 0≠S ; true≠false
        )

open import Inductive.Arithmetic
  using ( _-_
        ; x>y→x-y+y=x
        ; x≤y→y-x+x=y
        ; minus-N
        )

open import Inductive.Inequalities
  using ( _>_
        ; _≤_
        ; x>y∨x≤y
        ; x≺0=false ; 0≺S=true
        )

open import Inductive.Divisibility
  using ( _∣_
        ; ∣-≤
        ; ∣-refl-S
        ; 0∤x
        ; x∣y→x∣z→x∣y+z
        ; x∣y→x∣z→x∣y-z
        ; S∣0
        )

open import Inductive.WellFounded
  using ( wf₂N ; _<₂_
        ; Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] ; Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy]
        )

open import Common.Product using ( _,_ )

open import Inductive.GCD.Definition using ( gcd )

-- The comments remove/active the use of the gcd equations from the definition.
-- {-
open import Inductive.GCD.Equations
  using ( gcd-S0 ; gcd-0S ; gcd-S>S ; gcd-S≤S )
-- -}

-- The comments remove/active the use of the gcd equations via postulates.
{-
postulate
  gcd-00 : gcd zero zero                         == error
  gcd-S0 : {m : D} → N m → gcd (succ m) zero  == succ m
  gcd-0S : {n : D} → N n → gcd zero (succ n)  == succ n
  gcd-S>S : {m n : D} → N m → N n → succ m > succ n →
            gcd (succ m) (succ n) == gcd (succ m - succ n) (succ n)
  gcd-S≤S : {m n : D} → N m → N n → succ m ≤ succ n →
            gcd (succ m) (succ n) == gcd (succ m) (succ n - succ m)
-}

------------------------------------------------------------------------------
-- The gcd specification
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Some properties

-- Common divisor.
CD : D → D → D → Set
CD m n d = (d ∣ m) ∧ (d ∣ n)

-- Divisible for any common divisor.
DIVISIBLE : D → D → D → Set
DIVISIBLE m n g = {d : D} → N d → CD m n d → d ∣ g

-- Greatest that any common divisor.
GRT : D → D → D → Set
GRT m n g = (d : D) → N d → CD m n d → d ≤ g

-- To be the gcd.
GCD : D → D → D → Set
GCD m n g = CD m n g ∧ GRT m n g

------------------------------------------------------------------------------
-- Some auxiliary functions

0∧0≠0-elim : {A : Set} → ¬ ((zero == zero) ∧ (zero == zero)) → A
0∧0≠0-elim 00≠0 = ⊥-elim (00≠0 (∧-i ==-refl ==-refl))

0>x-elim : {A : Set}{x : D} → zero > x → A
0>x-elim {x = x} 0>x = ⊥-elim (true≠false (==-trans (==-sym 0>x )
                                                    (x≺0=false x)))
S≤0-elim : {A : Set}{x : D} → succ x ≤ zero → A
S≤0-elim {x = x} Sx≤0 = ⊥-elim (true≠false (==-trans (==-sym (0≺S=true x))
                                                     Sx≤0 ))

S=0-elim : {A : Set}{n : D} → succ n == zero → A
S=0-elim S=0 = ⊥-elim (0≠S (==-sym S=0 ))

------------------------------ -----------------------------------------------
-- The gcd is N
------------------------------------------------------------------------------

-- We will prove that 'gcd-N : ... → N (gcd m n).

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is N.
gcd-0S-N : {n : D} → N n → N (gcd zero (succ n))
gcd-0S-N Nn = ==-subst (λ x → N x )
                        (==-sym (gcd-0S Nn))
                        (sN Nn)

------------------------------------------------------------------------------
-- The 'gcd (succ m) 0' is N.

gcd-S0-N : {m : D} → N m → N (gcd (succ m) zero)
gcd-S0-N Nm = ==-subst (λ x → N x )
                        (==-sym (gcd-S0 Nm))
                        (sN Nm)

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is N.

gcd-S>S-N : {m n : D} → N m → N n →
              N (gcd (succ m - succ n) (succ n)) →
              succ m > succ n →
              N (gcd (succ m) (succ n))
gcd-S>S-N Nm Nn acc Sm>Sn =
  ==-subst (λ x → N x )
           (==-sym (gcd-S>S Nm Nn Sm>Sn))
           acc

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is N.

gcd-S≤S-N : {m n : D} → N m → N n →
            N (gcd (succ m) (succ n - succ m)) →
            succ m ≤ succ n →
            N (gcd (succ m) (succ n))
gcd-S≤S-N Nm Nn ih Sm≤Sn =
  ==-subst (λ x → N x )
           (==-sym (gcd-S≤S Nm  Nn Sm≤Sn ))
           ih

------------------------------------------------------------------------------
-- The 'gcd m n' when 'm > n' is N.

-- ToDo: If '>' were an inductive data type, we would use the absurd pattern
-- to prove the second case.

gcd-x>y-N :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → (m' , n') <₂ (m , n) →
       ¬ ((m' == zero) ∧ (n' == zero)) → N (gcd m' n')) →
  m > n →
  ¬ ((m == zero) ∧ (n == zero)) → N (gcd m n)

gcd-x>y-N zN           zN           _      _     00≠0 = 0∧0≠0-elim 00≠0
gcd-x>y-N zN           (sN _)       _      0>Sn  _    = 0>x-elim 0>Sn
gcd-x>y-N (sN Nm)      zN           _      _     _    = gcd-S0-N Nm
gcd-x>y-N (sN {m} Nm) (sN {n} Nn) allAcc Sm>Sn _    =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
    -- Inductive hypothesis
    ih : N (gcd (succ m - succ n) (succ n))
    ih = allAcc (minus-N (sN Nm) (sN Nn))
                (sN Nn)
                (Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] Nm Nn Sm>Sn)
                (λ p → S=0-elim (∧-snd p))

------------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is N.

-- ToDo: If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.

gcd-x≤y-N :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → (m' , n') <₂ (m , n) →
       ¬ ((m' == zero) ∧ (n' == zero)) → N (gcd m' n')) →
  m ≤ n →
  ¬ ((m == zero) ∧ (n == zero)) → N (gcd m n)

gcd-x≤y-N zN           zN         _      _     00≠0 = 0∧0≠0-elim 00≠0
gcd-x≤y-N zN           (sN Nn)    _      _     _    = gcd-0S-N Nn
gcd-x≤y-N (sN _ )      zN         _      Sm≤0  _    = S≤0-elim Sm≤0
gcd-x≤y-N (sN {m} Nm) (sN {n} Nn) allAcc Sm≤Sn _    =
  gcd-S≤S-N Nm Nn ih Sm≤Sn
  where
    -- Inductive hypothesis
    ih : N (gcd (succ m) (succ n - succ m))
    ih = allAcc (sN Nm)
                (minus-N (sN Nn)  (sN Nm ))
                (Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] Nm Nn Sm≤Sn)
                (λ p → S=0-elim (∧-fst p))

------------------------------------------------------------------------------
-- The 'gcd' is N.

gcd-N : {m n : D} → N m → N n → ¬ ((m == zero) ∧ (n == zero)) →
        N (gcd m n)
gcd-N {m} {n} Nm Nn = wf₂N P istep Nm Nn
  where
    P : D → D → Set
    P i j = ¬ ((i == zero) ∧ (j == zero)) → N (gcd i j )

    istep :
      {i j : D} → N i → N j →
      ({i' j' : D} → N i' → N j' → (i' , j') <₂ (i , j) → P i' j') →
      P i j
    istep {i} {j} Ni Nj allAcc = ∨-elim (gcd-x>y-N Ni Nj allAcc )
                                        (gcd-x≤y-N Ni Nj allAcc )
                                        (x>y∨x≤y Ni Nj)

------------------------------------------------------------------------------
-- Some cases of the gcd-∣₁
------------------------------------------------------------------------------

-- We don't prove that 'gcd-∣₁ : ... → (gcd m n) ∣ m'
-- because this proof should be defined mutually recursive with the proof
-- 'gcd-∣₂ : ... → (gcd m n) ∣ n'. Therefore, instead of prove
-- 'gcd-CD : ... → CD m n (gcd m n)' using these proof (i.e. the conjunction
-- of them), we proved it using well-found induction.

------------------------------------------------------------------------------
-- 'gcd 0 (succ n) ∣ 0'.

gcd-0S-∣₁ : {n : D} → N n → gcd zero (succ n) ∣ zero
gcd-0S-∣₁ {n} Nn = ==-subst (λ x → x ∣ zero )
                             (==-sym (gcd-0S Nn))
                             (S∣0 Nn)

------------------------------------------------------------------------------
-- 'gcd (succ m) 0 ∣ succ m'.

gcd-S0-∣₁ : {m : D} → N m → gcd (succ m) zero ∣ succ m
gcd-S0-∣₁ {m} Nm = ==-subst (λ x → x ∣ (succ m ))
                             (==-sym (gcd-S0 Nm))
                             (∣-refl-S Nm)

------------------------------------------------------------------------------
-- 'gcd (succ m) (succ n) ∣ succ m', when 'succ m ≤ succ n'.

gcd-S≤S-∣₁ :
  {m n : D} → N m → N n →
  (gcd (succ m) (succ n - succ m) ∣ succ m) →
  succ m ≤ succ n →
  gcd (succ m) (succ n) ∣ succ m
gcd-S≤S-∣₁ {m = m} Nm Nn ih Sm≤Sn =
  ==-subst (λ x → x ∣ succ m )
           (==-sym (gcd-S≤S Nm  Nn  Sm≤Sn))
           ih


------------------------------------------------------------------------------
-- 'gcd (succ m) (succ n) ∣ succ m' when 'succ m > succ n'.

-- We use gcd-∣₂
-- We apply the theorem that if 'm∣n' and 'm∣o' then 'm∣(n+o)'.

gcd-S>S-∣₁ :
  {m n : D} → N m → N n →
  (gcd (succ m - succ n) (succ n) ∣ (succ m - succ n)) →
  (gcd (succ m - succ n) (succ n) ∣ succ n) →
  succ m > succ n →
  gcd (succ m) (succ n) ∣ succ m

{- Proof:
1. gcd (Sm - Sn) Sn | (Sm - Sn)        IH
2. gcd (Sm - Sn) Sn | Sn               gcd-∣₂
3. gcd (Sm - Sn) Sn | (Sm - Sn) + Sn   m∣n→m∣o→m∣n+o 1,2
4. Sm > Sn                             Hip
5. gcd (Sm - Sn) Sn | Sm               arith-gcd-m>n₂ 3,4
6. gcd Sm Sn = gcd (Sm - Sn) Sn        gcd eq. 4
7. gcd Sm Sn | Sm                      subst 5,6
-}

gcd-S>S-∣₁ {m} {n} Nm Nn ih gcd-∣₂ Sm>Sn =
  -- The first substitution is based on
  -- 'gcd (succ m) (succ n) = gcd (succ m - succ n) (succ n)'.
  ==-subst (λ x → x ∣ (succ m) )
           (==-sym (gcd-S>S Nm  Nn Sm>Sn))
           -- The second substitution is based on
           -- 'm = (m - n) + n'.
           (==-subst (λ y → gcd (succ m - succ n) (succ n) ∣ y )
                     (x>y→x-y+y=x (sN Nm) (sN Nn) Sm>Sn)
                     (x∣y→x∣z→x∣y+z
                         {gcd (succ m - succ n) (succ n)}
                         {succ m - succ n}
                         {succ n}
                         (gcd-N Sm-Sn-N  (sN Nn ) (λ p → S=0-elim (∧-snd p)))
                         Sm-Sn-N
                         (sN Nn)
                         ih
                         gcd-∣₂
                      )
           )
  where Sm-Sn-N : N (succ m - succ n)
        Sm-Sn-N = minus-N (sN Nm) (sN Nn)


------------------------------------------------------------------------------
-- Some case of the gcd-∣₂
------------------------------------------------------------------------------

-- We don't prove that 'gcd-∣₂ : ... → gcd m n ∣ n'. The reason is
-- the same to don't prove 'gcd-∣₁ : ... → gcd m n ∣ m'.

------------------------------------------------------------------------------
-- 'gcd 0 (succ n) ∣₂ succ n'.

gcd-0S-∣₂ : {n : D} → N n → gcd zero (succ n) ∣ succ n
gcd-0S-∣₂ {n} Nn = ==-subst (λ x → x ∣ (succ n ))
                             (==-sym (gcd-0S Nn))
                             (∣-refl-S Nn)

------------------------------------------------------------------------------
-- 'gcd (succ m) 0 ∣ 0'.

gcd-S0-∣₂ : {m : D} → N m → gcd (succ m) zero ∣ zero
gcd-S0-∣₂  {m} Nm = ==-subst (λ x → x ∣ zero )
                              (==-sym (gcd-S0 Nm))
                              (S∣0 Nm)

------------------------------------------------------------------------------
-- 'gcd (succ m) (succ n) ∣ succ n' when 'succ m > succ n'.

gcd-S>S-∣₂ :
  {m n : D} → N m → N n →
  (gcd (succ m - succ n) (succ n) ∣ succ n) →
  succ m > succ n →
  gcd (succ m) (succ n) ∣ succ n

gcd-S>S-∣₂ {m} {n} Nm Nn ih Sm>Sn =
  ==-subst (λ x → x ∣ (succ n) )
           (==-sym (gcd-S>S Nm Nn Sm>Sn))
           ih

------------------------------------------------------------------------------
-- 'gcd (succ m) (succ n) ∣ succ n' when 'succ m ≤ succ n'.

-- We use gcd-∣₁.
-- We apply the theorem that if 'm∣n' and 'm∣o' then 'm∣(n+o)'.
gcd-S≤S-∣₂ :
  {m n : D} → N m → N n →
  (gcd (succ m) (succ n - succ m) ∣ (succ n - succ m)) →
  (gcd (succ m) (succ n - succ m) ∣ succ m) →
  succ m ≤ succ n →
  gcd (succ m) (succ n) ∣ succ n

{- Proof:
1. gcd Sm (Sn - Sm) | (Sn - Sm)        IH
2  gcd Sm (Sn - Sm) | Sm               gcd-∣₁
3. gcd Sm (Sn - Sm) | (Sn - Sm) + Sm   m∣n→m∣o→m∣n+o 1,2
4. Sm ≤ Sn                             Hip
5. gcd (Sm - Sn) Sn | Sm               arith-gcd-m≤n₂ 3,4
6. gcd Sm Sn = gcd Sm (Sn - Sm)        gcd eq. 4
7. gcd Sm Sn | Sn                      subst 5,6
-}

gcd-S≤S-∣₂ {m} {n} Nm Nn ih gcd-∣₁ Sm≤Sn =
  -- The first substitution is based on 'gcd m n = gcd m (n - m)'.
  ==-subst (λ x → x ∣ succ n )
           (==-sym (gcd-S≤S Nm  Nn  Sm≤Sn ))
           -- The second substitution is based on.
           -- 'n = (n - m) + m'
           (==-subst (λ y → gcd (succ m) (succ n - succ m) ∣ y )
                     (x≤y→y-x+x=y (sN Nm) (sN Nn) Sm≤Sn )
                     (x∣y→x∣z→x∣y+z
                       {gcd (succ m) (succ n - succ m)}
                       {succ n - succ m}
                       {succ m}
                       ((gcd-N (sN Nm ) Sn-Sm-N (λ p → S=0-elim (∧-fst p))) )
                       Sn-Sm-N
                       (sN Nm )
                       ih
                       gcd-∣₁
                     )
           )
  where Sn-Sm-N : N (succ n - succ m)
        Sn-Sm-N = minus-N (sN Nn) (sN Nm)

------------------------------------------------------------------------------
-- The gcd is CD
------------------------------------------------------------------------------

-- We will prove that 'gcd-CD : ... → CD m n (gcd m n).

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is CD.

gcd-0S-CD : {n : D} → N n → CD zero (succ n) (gcd zero (succ n))
gcd-0S-CD Nn = ∧-i (gcd-0S-∣₁ Nn ) (gcd-0S-∣₂ Nn )

------------------------------------------------------------------------------
-- The 'gcd (succ m) 0 ' is CD.

gcd-S0-CD : {m : D} → N m → CD (succ m) zero (gcd (succ m) zero)
gcd-S0-CD Nm = ∧-i (gcd-S0-∣₁ Nm) (gcd-S0-∣₂ Nm )


------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is CD.

gcd-S>S-CD :
  {m n : D} → N m → N n →
  (CD (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))) →
  succ m > succ n →
  CD (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S>S-CD {m} {n} Nm Nn acc Sm>Sn =
  ∧-i (gcd-S>S-∣₁ Nm Nn acc-∣₁ acc-∣₂ Sm>Sn )
      (gcd-S>S-∣₂ Nm Nn acc-∣₂ Sm>Sn )
  where
    acc-∣₁ : gcd (succ m - succ n) (succ n) ∣ (succ m - succ n)
    acc-∣₁ = ∧-fst acc

    acc-∣₂ : gcd (succ m - succ n) (succ n) ∣ succ n
    acc-∣₂ = ∧-snd acc

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is CD.

gcd-S≤S-CD :
  {m n : D} → N m → N n →
  (CD (succ m) (succ n - succ m) (gcd (succ m) (succ n - succ m))) →
  succ m ≤ succ n →
  CD (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S≤S-CD {m} {n} Nm Nn acc Sm≤Sn =
  ∧-i (gcd-S≤S-∣₁ Nm Nn acc-∣₁ Sm≤Sn)
      (gcd-S≤S-∣₂ Nm Nn acc-∣₂ acc-∣₁ Sm≤Sn)
  where
    acc-∣₁ : gcd (succ m) (succ n - succ m) ∣ succ m
    acc-∣₁ = ∧-fst acc

    acc-∣₂ : gcd (succ m) (succ n - succ m) ∣ (succ n - succ m)
    acc-∣₂ = ∧-snd acc

------------------------------------------------------------------------------
-- The 'gcd m n' when 'm > n' is CD

-- ToDo: If '>' were an inductive data type, we would use the absurd pattern
-- to prove the second case.

gcd-x>y-CD :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → (m' , n') <₂ (m , n) →
       ¬ ((m' == zero) ∧ (n' == zero)) → CD m' n' (gcd m' n')) →
  m > n →
  ¬ ((m == zero) ∧ (n == zero)) → CD m n (gcd m n)

gcd-x>y-CD zN           zN         _      _     00≠0 = 0∧0≠0-elim 00≠0
gcd-x>y-CD zN          (sN _)      _      0>Sn  _    = 0>x-elim 0>Sn
gcd-x>y-CD (sN Nm)     zN          _      _     _    = gcd-S0-CD Nm
gcd-x>y-CD (sN {m} Nm) (sN {n} Nn) allAcc Sm>Sn _    =
  gcd-S>S-CD Nm Nn ih Sm>Sn
  where
    -- Inductive hypothesis.
    ih : CD (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))
    ih  = allAcc {succ m - succ n}
                 {succ n}
                 (minus-N (sN Nm) (sN Nn))
                 (sN Nn)
                 (Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] Nm Nn Sm>Sn )
                 (λ p → S=0-elim (∧-snd p))


------------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is CD.

-- ToDo: If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.

gcd-x≤y-CD :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → (m' , n') <₂ (m , n)
       → ¬ ((m' == zero) ∧ (n' == zero)) → CD m' n' (gcd m' n')) →
  m ≤ n →
  ¬ ((m == zero) ∧ (n == zero)) → CD m n (gcd m n)

gcd-x≤y-CD zN          zN          _      _     00≠0  = 0∧0≠0-elim 00≠0
gcd-x≤y-CD zN          (sN Nn)     _      _     _     = gcd-0S-CD Nn
gcd-x≤y-CD (sN _ )     zN          _      Sm≤0  _     = S≤0-elim Sm≤0
gcd-x≤y-CD (sN {m} Nm) (sN {n} Nn) allAcc Sm≤Sn _     =
  gcd-S≤S-CD Nm Nn ih Sm≤Sn
  where
    -- Inductive hypothesis
    ih : CD (succ m) (succ n - succ m)  (gcd (succ m) (succ n - succ m))
    ih = allAcc {succ m}
                {succ n - succ m}
                (sN Nm)
                (minus-N (sN Nn) (sN Nm))
                (Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] Nm Nn Sm≤Sn)
                (λ p → S=0-elim (∧-fst p))

------------------------------------------------------------------------------
-- The 'gcd' is CD.

gcd-CD : {m n : D} → N m → N n → ¬ ((m == zero) ∧ (n == zero)) →
         CD m n (gcd m n)
gcd-CD {m} {n} Nm Nn = wf₂N P istep Nm Nn
  where
    P : D → D → Set
    P i j = ¬ ((i == zero) ∧ (j == zero)) → CD i j  (gcd i j )

    istep :
      {i j : D} → N i → N j →
      ({i' j' : D} → N i' → N j' → (i' , j') <₂ (i , j) → P i' j') →
      P i j
    istep {i} {j} Ni Nj allAcc = ∨-elim (gcd-x>y-CD Ni Nj allAcc)
                                        (gcd-x≤y-CD Ni Nj allAcc)
                                        (x>y∨x≤y Ni Nj )


------------------------------------------------------------------------------
-- The gcd is DIVISIBLE
------------------------------------------------------------------------------

-- We will prove that 'gcd-DIVISIBLE : ... → DIVISIBLE m n (gcd m n).

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is DIVISIBLE.

gcd-0S-DIVISIBLE : {n : D} → N n →
                    DIVISIBLE zero (succ n) (gcd zero (succ n))
gcd-0S-DIVISIBLE Nn {d} _ (∧-i d∣0 d∣Sn) = ==-subst (λ x → d ∣ x )
                                                    (==-sym (gcd-0S Nn))
                                                    d∣Sn


------------------------------------------------------------------------------
-- The 'gcd (succ m) 0' is DIVISIBLE.

gcd-S0-DIVISIBLE : {m : D} → N m →
                    DIVISIBLE (succ m) zero (gcd (succ m) zero)
gcd-S0-DIVISIBLE Nm {d} _ (∧-i d∣Sm d∣0) = ==-subst (λ x → d ∣ x )
                                                    (==-sym (gcd-S0 Nm))
                                                    d∣Sm

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is DIVISIBLE.

gcd-S>S-DIVISIBLE :
  {m n : D} → N m → N n →
  (DIVISIBLE (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))) →
  succ m > succ n →
  DIVISIBLE (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S>S-DIVISIBLE {m} {n} Nm Nn acc Sm>Sn {d} Nd (∧-i d∣Sm d∣Sn) =
{-
Proof:
   ----------------- (Hip.)
     d' | m    d' | n
   ---------------------- (Thm.)   -------- (Hip.)
       d' | (m - n)                   d' | n
     ------------------------------------------ (IH)
              d' | gcd m (n - m)                          m > n
             --------------------------------------------------- (gcd def.)
                             d' | gcd m n
-}
 ==-subst (λ x → d ∣ x )
           (==-sym (gcd-S>S Nm  Nn  Sm>Sn))
           (acc Nd (∧-i d|Sm-Sn d∣Sn))
 where
   d|Sm-Sn : d ∣ succ m - succ n
   d|Sm-Sn = x∣y→x∣z→x∣y-z Nd (sN Nm ) (sN Nn ) d∣Sm d∣Sn


------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is DIVISIBLE.

gcd-S≤S-DIVISIBLE :
  {m n : D} → N m → N n →
  (DIVISIBLE (succ m) (succ n - succ m) (gcd (succ m) (succ n - succ m))) →
  succ m ≤ succ n →
  DIVISIBLE (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S≤S-DIVISIBLE {m} {n} Nm Nn acc Sm≤Sn {d} Nd (∧-i d∣Sm d∣Sn) =
{-
Proof
                            ----------------- (Hip.)
                                d' | m    d' | n
        -------- (Hip.)       ---------------------- (Thm.)
         d' | m                      d' | n - m
     ------------------------------------------ (IH)
              d' | gcd m (n - m)                          m ≤ n
             --------------------------------------------------- (gcd def.)
                             d' | gcd m n
-}

  ==-subst (λ x → d ∣ x )
           (==-sym (gcd-S≤S Nm  Nn  Sm≤Sn))
           (acc Nd (∧-i d∣Sm d|Sn-Sm))
  where
        d|Sn-Sm : d ∣ succ n - succ m
        d|Sn-Sm = x∣y→x∣z→x∣y-z Nd (sN Nn ) (sN Nm ) d∣Sn  d∣Sm

------------------------------------------------------------------------------
-- The 'gcd m n' when 'm > n' is DIVISIBLE.

-- ToDo: If '>' were an inductive data type, we would use the absurd pattern
-- to prove the second case.

gcd-x>y-DIVISIBLE :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → (m' , n') <₂ (m , n) →
    ¬ ((m' == zero) ∧ (n' == zero)) → DIVISIBLE m' n' (gcd m' n')) →
  m > n →
  ¬ ((m == zero) ∧ (n == zero)) → DIVISIBLE m n (gcd m n)

gcd-x>y-DIVISIBLE zN zN      _ _    00≠0 _ _  = 0∧0≠0-elim 00≠0
gcd-x>y-DIVISIBLE zN (sN Nn) _ 0>Sn _    _ _  = 0>x-elim 0>Sn
gcd-x>y-DIVISIBLE (sN Nm) zN _ _    _    d cd = gcd-S0-DIVISIBLE Nm d cd
gcd-x>y-DIVISIBLE (sN {m} Nm)
                  (sN {n} Nn)
                  allAcc
                  Sm>Sn
                  SmSn≠0
                  d
                  cd = gcd-S>S-DIVISIBLE Nm Nn ih Sm>Sn d cd
  where -- Inductive hypothesis.
        ih : DIVISIBLE (succ m - succ n)
                       (succ n)
                       (gcd (succ m - succ n) (succ n))
        ih = allAcc (minus-N (sN Nm) (sN Nn))
                    (sN Nn)
                    (Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] Nm Nn Sm>Sn)
                    (λ p → S=0-elim (∧-snd p))

------------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is DIVISIBLE.

-- ToDo: If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.

gcd-x≤y-DIVISIBLE :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → (m' , n') <₂ (m , n) →
    ¬ ((m' == zero) ∧ (n' == zero)) → DIVISIBLE m' n' (gcd m' n')) →
  m ≤ n →
  ¬ ((m == zero) ∧ (n == zero)) → DIVISIBLE m n (gcd m n)

gcd-x≤y-DIVISIBLE zN      zN      _ _    00≠0 _ _  = 0∧0≠0-elim 00≠0
gcd-x≤y-DIVISIBLE zN      (sN Nn) _ _    _    d cd = gcd-0S-DIVISIBLE Nn d cd
gcd-x≤y-DIVISIBLE (sN Nm) zN      _ Sm≤0 _    _ _  = S≤0-elim Sm≤0
gcd-x≤y-DIVISIBLE (sN {m} Nm)
                  (sN {n} Nn)
                  allAcc
                  Sm≤Sn
                  SmSn≠0
                  d
                  cd = gcd-S≤S-DIVISIBLE Nm Nn ih Sm≤Sn d cd
  where -- Inductive hypothesis.
        ih : DIVISIBLE (succ m)
                       (succ n - succ m)
                       (gcd (succ m) (succ n - succ m))
        ih = allAcc (sN Nm)
                    (minus-N (sN Nn)  (sN Nm ))
                    (Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] Nm Nn Sm≤Sn)
                    (λ p → S=0-elim (∧-fst p))

------------------------------------------------------------------------------
-- The gcd is DIVISIBLE.

gcd-DIVISIBLE : {m n : D} → N m → N n → ¬ ((m == zero) ∧ (n == zero)) →
                DIVISIBLE m n (gcd m n)
gcd-DIVISIBLE {m} {n} Nm Nn = wf₂N P istep Nm Nn
  where
    P : D → D → Set
    P i j = ¬ ((i == zero) ∧ (j == zero)) → DIVISIBLE i j (gcd i j)

    istep :
      {i j : D} → N i → N j →
      ({i' j' : D} → N i' → N j' → (i' , j') <₂ (i , j) → P i' j') →
      P i j
    istep {i} {j} Ni Nj allAcc = ∨-elim (gcd-x>y-DIVISIBLE Ni Nj allAcc )
                                        (gcd-x≤y-DIVISIBLE Ni Nj allAcc )
                                        (x>y∨x≤y Ni Nj)

------------------------------------------------------------------------------
-- The 'gcd' is GRT
------------------------------------------------------------------------------

-- Knowing that 'gcd m n' is a common divisor of 'm' and 'n', and that
-- any other common divisor of 'm' and 'n' divides it, we can
-- prove that 'gcd m n' is the largest common divisor

-- We need 'N d'.
-- ToDo: Why the dependent type '$' doesn't work in '⊥-elim (0∤n d∣m)'?

gcd-GRT : {m n g : D} → N g → CD m n g → DIVISIBLE m n g → GRT m n g
gcd-GRT zN     (∧-i 0∣m _) = ⊥-elim (0∤x 0∣m )
gcd-GRT (sN Ng) _          =
  λ divisible-mnSg d Nd cd-mnd → ∣-≤ Nd Ng (divisible-mnSg Nd cd-mnd )

------------------------------------------------------------------------------
-- The 'gcd' is GCD
------------------------------------------------------------------------------

gcd-GCD : {m n : D} → N m → N n → ¬ ((m == zero) ∧ (n == zero)) →
          GCD m n (gcd m n)
gcd-GCD {m} {n} Nm Nn mn≠0 =
  ∧-i gcd-cd (gcd-GRT (gcd-N Nm Nn mn≠0) gcd-cd (gcd-DIVISIBLE Nm Nn mn≠0))
  where gcd-cd : CD m n (gcd m n)
        gcd-cd = gcd-CD Nm Nn mn≠0

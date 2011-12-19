------------------------------------------------------------------------------
-- Code accompanying the paper "Embedding a Logical Theory of
-- Constructions in Agda" by Ana Bove, Peter Dybjer, and Andrés
-- Sicard-Ramírez (PLPV'09).
------------------------------------------------------------------------------

-- The code presented here does not match the paper exactly.

-- The code has been tested with Agda 2.3.0.

module LTC where

-- LTC-independent files (logical constants, equality reasoning, etc.)
open import Common.EqualityReasoning
open import Common.Logic
open import Common.Product

-- Encoding of LTC
open import Inductive.Core

-- LTC library
open import Inductive.Arithmetic
open import Inductive.Divisibility
open import Inductive.Inequalities
open import Inductive.Rec
open import Inductive.WellFounded

-- Definition of the greatest common divisor
open import Inductive.GCD.Definition
open import Inductive.GCD.Equations

-- Proofs of termination and correctness for greatest common divisor
open import Inductive.GCD

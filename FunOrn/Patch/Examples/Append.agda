module FunOrn.Patch.Examples.Append
         (A : Set)
       where

open import FunOrn.Functions.Examples.Plus
open import FunOrn.FunOrnament.Examples.Append

open import FunOrn.FunOrnament
open import FunOrn.Patch

open import Data.Unit
open import Logic.Logic

-- Paper: Example 5.18
typeILookup : Set
typeILookup = Patch _+_ (typeAppend A)


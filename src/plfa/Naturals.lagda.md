# Exercises for Naturals

## Exercise Bin

Normalize binary numbers
```agda
module plfa.Naturals where

open import Data.Nat

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin -> Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from :  Bin → ℕ
from ⟨⟩ = 0
from (⟨⟩ O) = 0
from (⟨⟩ I) = 1
from (b O) = 2 * from b
from (b I) = suc (2 * from b)
```

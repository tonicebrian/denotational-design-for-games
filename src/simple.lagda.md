# Introduction

This module is an initial exploration on how to define and present all the definitions for a game, a very simplistic game.

So let's start by defining a module and loading all relevant modules
```agda
module simple where

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality
```

Let's define a simple game that consist of 2 players. Players will be named after capital letters so we'll have `A` and `B`  as players.

```agda
data Player : Set where
  A : Player
  B : Player
```

Players will be able to submit an action that is a number between 0 and 10.

```agda
-- TODO. Learn how to create this type alias
-- type Action = Fin 10
```

Once actions from both players have been received the game engine compares both values and declares winner by telling the user who sent
the max value or declares a Tie when both users picked the same value.

```agda
data Result : Set where
  Winner : Player -> Result
  Tie : Result
```

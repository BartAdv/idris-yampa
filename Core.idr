module Core

import public HList
import public Descriptors

%access public export

-- Signal Representation --

SigRep : SigDesc -> Type
SigRep (E a) = Maybe a
SigRep (C a) = a

SVRep : SVDesc -> Type
SVRep ds = HList (map SigRep ds)

-- Time --

Time : Type
Time = Double

DTime : Type
DTime = Double

t0 : Time
t0 = 0

-- Signal Function Representation --

infixl 91 ***
infixl 90 >>>

data SF : SVDesc -> SVDesc -> Decoupledness -> Type where
  Prim : (DTime -> state -> SVRep as -> (state, SVRep bs)) -> state -> SF as bs Causal
  DPrim : (DTime -> state -> ((SVRep as -> state), SVRep bs)) -> state -> SF as bs Decoupled
  (>>>) : SF as bs d1 -> SF bs cs d2 -> SF as cs (d1 && d2)
  (***) : SF as cs d1 -> SF bs ds d2 -> SF (as ++ bs) (cs ++ ds) (d1 || d2)

-- Utility Functions --

svsplit : SVRep (as ++ bs) -> (SVRep as, SVRep bs)
svsplit {as=[]} xs = ([], xs)
svsplit {as=a::as} (x :: xs) with (svsplit xs)
  | (xs', ys') = (x::xs', ys')

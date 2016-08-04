module Primitives

import Core
import Data.Bifunctor

%access export

private
mapE :  (a -> b) -> SVRep [E a] -> SVRep [E b]
mapE f [x] = [map f x]

private
mapC : (a -> b) -> SVRep [C a] -> SVRep [C b]
mapC f [x] = [f x]

private
mapC2 : (a -> b -> d) -> SVRep [C a, C b] -> SVRep [C d]
mapC2 f [a,b] = [f a b]

private
mkStateless : (SVRep as -> SVRep bs) -> SF as bs Causal
mkStateless f = Prim (\_, _, as => ((), f as)) ()

private
mkSource : (DTime -> st -> (st, SVRep bs)) -> st -> SF as bs Decoupled
mkSource f = DPrim (\t => first const . f t)

pureE : (a -> b) -> SF [E a] [E b] Causal
pureE = mkStateless . mapE

pure : (a -> b) -> SF [C a] [C b] Causal
pure = mkStateless . mapC

pure2 : (a -> b -> d) -> SF [C a, C b] [C d] Causal
pure2 = mkStateless . mapC2

mergeWith : (a -> a -> a) -> SF [E a, E a] [E a] Causal
mergeWith = mkStateless . mergeMaybesWith
  where mergeMaybesWith : (a -> a -> a) -> HList [Maybe a, Maybe a] -> HList [Maybe a]
        mergeMaybesWith f [Just x, Just y] = [Just (f x y)]
        mergeMaybesWith f [Nothing, mb] = [mb]
        mergeMaybesWith f [ma, Nothing] = [ma]

sample : SF [E b, C a] [E a] Causal
sample = mkStateless sampleAux
  where sampleAux : SVRep [E b, C a] -> SVRep [E a]
        sampleAux [me,a] = [map (const a) me]

constant : a -> SF as [C a] Decoupled
constant a = mkSource (\_,_ => ((), [a])) ()

never : SF as [E a] Decoupled
never = mkSource (\_,_ => ((), [Nothing])) ()

private
edgeAux : Bool -> SVRep [C Bool] -> (Bool, SVRep [E ()])
edgeAux s [b] = (b, if b || (not s) then [Just ()] else [Nothing])

-- -- edge never produces an event at Time0
edge : SF [C Bool] [E ()] Causal
edge = Prim (const edgeAux) True

-- iEdge will produce an event at Time0, if the initial input is true
iEdge : SF [C Bool] [E ()] Causal
iEdge = Prim (const edgeAux) False

holdWith : (a -> b -> b) -> b -> SF [E a] [C b] Causal
holdWith {a} {b} f = Prim (const holdAux)
  where
    holdAux : b -> SVRep [E a] -> (b, SVRep [C b])
    holdAux s [Just y] = let s' = f y s in (s', [s'])
    holdAux s [Nothing] = (s, [s])

iPre : a -> SF [C a] [C a] Decoupled
iPre x = let sv = [x] in DPrim (\_, s => (id, s)) sv

identity : SF as as Causal
identity = mkStateless id

sfFork : SF as (as ++ as) Causal
sfFork {as} = mkStateless (\xs => rewrite mapDistributesOverAppend SigRep as as in xs ++ xs)

sfSink : SF as [] Decoupled
sfSink = mkSource (\_, _ => ((), [])) ()

sfNil : SF [] [] Decoupled
sfNil = sfSink

time : SF as [C Time] Decoupled
time = mkSource (\dt, s => let s' = s + dt in (s', [s'])) t0

-- TODO: VectorSpace?
integral : SF [C Double] [C Double] Causal
integral = Prim integralAux t0
  where
    integralAux dt st [a] = let s' = st + dt * a in (s', [s'])

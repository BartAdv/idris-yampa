module Evaluator

import Core

%access public export

eval : DTime -> SF as bs d -> SVRep as -> (SF as bs d, SVRep bs)
eval dt (Prim f s) as =
  let (s', bs) = f dt s as
  in (Prim f s', bs)
eval dt (DPrim f s) as =
  let (g, bs) = f dt s
      s' = g as
  in (DPrim f s', bs)
eval dt (sfl >>> sfr) as =
  let (sfl', bs) = eval dt sfl as
      (sfr', cs) = eval dt sfr bs
  in (sfl' >>> sfr', cs)
eval dt ((***) {cs} {ds} sfl sfr) input =
  let (xs, ys) = svsplit input
      (sfl', xs') = eval dt sfl xs
      (sfr', ys') = eval dt sfr ys
  in (sfl' *** sfr', rewrite mapDistributesOverAppend SigRep cs ds in xs' ++ ys')

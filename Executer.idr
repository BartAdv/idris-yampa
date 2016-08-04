module Executer
       
import Core
import Evaluator
import Data.Vect

import Primitives

%access public export

-- Run a signal function over a finite amount of predetermined input
runSF : Vect n (SVRep as, DTime) -> SF as bs d -> (SF as bs d, Vect n (SVRep bs))
runSF [] sf = (sf, [])
runSF ((as, t) :: ass) sf with (eval t sf as)
  | (sf', bs) = let (sf'', inputs) = runSF ass sf'
                in (sf'', bs :: inputs)

-- Run a signal function that requires no input for n steps at a sampling rate t

-- simpleRun : n -> DTime -> SF [] bs d -> (SF [] bs d, Vec (SVRep bs) n)
-- simpleRun n t sf = runSF (MkVec (⟨⟩ , t)) sf

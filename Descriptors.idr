module Descriptors

%access public export

-- Decoupledness Descriptors --

-- Rather than create a datatype for Dec, we use booleans so we can use existing
-- boolean proofs
-- TODO check those proofs

Decoupledness : Type
Decoupledness = Bool

Decoupled : Decoupledness
Decoupled = False

Causal : Decoupledness
Causal = True

-- Signal Descriptors --

data SigDesc : Type where
  E : Type -> SigDesc
  C : Type -> SigDesc

SVDesc : Type
SVDesc = List SigDesc

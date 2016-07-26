module HList

%access public export

data HList : List Type -> Type where
  Nil  : HList []
  (::) : a -> HList as -> HList (a :: as)

(++) : HList xs -> HList ys -> HList (xs <+> ys)
Nil       ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

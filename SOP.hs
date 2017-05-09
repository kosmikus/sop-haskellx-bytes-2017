{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module SOP where

import Data.Coerce
import Data.Kind
import Data.List (intercalate)
{-
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField
import Database.PostgreSQL.Simple.FromRow
import Database.PostgreSQL.Simple.ToField
import Database.PostgreSQL.Simple.ToRow
-}
import Generics.SOP
import Generics.SOP.Constraint
import Generics.SOP.NP
import Generics.SOP.NS
import Generics.SOP.TH

-- Fun with Sums and Products
--
-- Andres Löh, Well-Typed LLP
--
-- 8 May 2017
-- HaskellX Bytes, Skills Matter, London



-- # 0. Motivation

-- generics-sop
--
-- https://hackage.haskell.org/package/generics-sop
-- https://github.com/well-typed/generics-sop
--
-- Edsko de Vries, Andres Löh
-- PRs by many other contributors, in particular Oleg Grenrus

-- - Datatype-generic programming
--
-- - Uniform yet typed representation of many datatypes
--
-- - Higher-order functions to work with these representations
--
-- - Define functions that work on many different datatypes
--
-- - Derivable type classes



-- # 1. from / to
--
-- - from, to, Rep, Code

-- from :: Generic a => a -> Rep a
-- to   :: Generic a => Rep a -> a
--
-- type Rep a = SOP I (Code a)



-- # 2. Example datatypes
--
-- - Bool, Ordering, Maybe, [], (,), (,,), IntTree, MyRecord
-- - deriveGeneric

data IntTree = Leaf Int | Node IntTree IntTree
  deriving Show

deriveGeneric ''IntTree



-- # 3. How to write a generic consumer

nrargs :: Generic a => a -> Int
nrargs =
  sum . hcollapse . hmap (\ (I _) -> K 1) . from
  -- or:
  -- sum . hcollapse . hmap (mapIK (const 1)) . from


-- >>> nrargs (Node (Leaf 3) (Leaf 4))
-- 2
--
-- >>> from (Node (Leaf 3) (Leaf 4))
-- SOP (S (Z (I (Leaf 3) :* I (Leaf 4) :* Nil)))
--
-- >>> hmap (mapIK (const 1)) it
-- SOP (S (Z (K 1 :* K 1 :* Nil)))
--
-- >>> hcollapse it
-- [1,1]
--
-- >>> sum it
-- 2

-- hmap and hcollapse are generalized versions of
-- map_SOP and collapse_SOP that could also be used
-- here.
--
-- map_SOP ::
--   All SListI xss => (forall a . f a -> g a) -> SOP f xss -> SOP g xss
-- collapse_SOP :: SListI xss => SOP (K a) xss -> [a]



-- # 4. Summing all integers

class HasTotal a where
  total :: a -> Int

instance HasTotal Int where
  total i = i

instance HasTotal Integer where
  total i = fromIntegral i

gtotal :: (Generic a, All2 HasTotal (Code a)) => a -> Int
gtotal =
    sum
  . hcollapse
  . hcmap (Proxy @HasTotal)
      (\ (I x) -> K (total x)) -- or: (mapIK total)
  . from

instance HasTotal IntTree where
  total = gtotal



-- # 5. Get the names of all constructors of a type

constructors ::
  (Generic a, HasDatatypeInfo a) =>
  Proxy a -> NP (K ConstructorName) (Code a)
constructors p =
  hmap
    (K . constructorName)
    (constructorInfo (datatypeInfo p))



-- # 6. Get the name of the constructor of a value

constructor ::
  forall a .
  (Generic a, HasDatatypeInfo a) => a -> String
constructor a =
  hcollapse $
  hzipWith
    (\ conName _args -> conName) -- or: const
    (constructors (Proxy @a))
    (unSOP $ from a)



-- # 7. Abstract a useful pattern

lookupByCon :: Generic a => NP (K b) (Code a) -> a -> b
lookupByCon np a =
  hcollapse $
  hzipWith
    const
    np
    (unSOP $ from a)

constructor' ::
  forall a .
  (Generic a, HasDatatypeInfo a) => a -> String
constructor' =
  lookupByCon (constructors (Proxy @a))



-- # 8. Name of constructor, for enumeration types only

type IsEnumType a = (Generic a, All IsEmpty (Code a))
type IsEmpty = ((~) '[])

conString :: (HasDatatypeInfo a, IsEnumType a) => a -> String
conString = constructor



-- # 9. Enum to string, using user-defined names

class IsEnumType a => HasNames a where
  names :: Proxy a -> NP (K String) (Code a)

instance HasNames Ordering where
  names _ =
    K "lessthan" :* K "equal" :* K "greaterthan" :* Nil

toName :: forall a . HasNames a => a -> String
toName =
  lookupByCon (names (Proxy @a))



-- # 10. Obtain all values, for enumeration types only

enum' :: IsEnumType a => NP (K a) (Code a)
enum' =
  hmap
    (mapKK to)
    (apInjs'_POP (POP (hcpure (Proxy @IsEmpty) Nil)))

enum :: IsEnumType a => [a]
enum =
  hcollapse enum'


-- >>> enum :: [Ordering]
-- [LT,EQ,GT]
--
-- >>> hcpure (Proxy @IsEmpty) Nil :: NP (NP I) (Code Ordering)
-- Nil :* Nil :* Nil :* Nil -- the first three are elements, the final is not
--
-- >>> POP it
-- POP (Nil :* Nil :* Nil :* Nil)
--
-- >>> apInjs'_POP it
-- K (SOP (Z Nil)) :* K (SOP (S (Z Nil))) :* K (SOP (S (S (Z Nil)))) :* Nil
--
-- >>> hmap (mapKK to) it :: NP (K Ordering) (Code Ordering)
-- K LT :* K EQ :* K GT :* Nil
--
-- >>> hcollapse it
-- [LT,EQ,GT]



-- # 11. String to enum, using user-defined names.

fromName :: forall a . HasNames a => String -> Maybe a
fromName =
  let
    table :: [(String, a)]
    table =
      hcollapse $
      hzipWith
        (mapKKK (,))
        (names (Proxy @a))
        enum'
  in
    flip lookup table

-- >>> enum' @Ordering
-- K LT :* K EQ :* K GT :* Nil
--
-- >>> hzipWith (mapKKK (,)) (names (Proxy @Ordering)) it
-- K ("lessthan",LT) :* K ("equal",EQ) :* K ("greaterthan",GT) :* Nil
--
-- >>> hcollapse it
-- [("lessthan",LT),("equal",EQ),("greatherthan",GT)]



-- # 12. postgresql-simple for record types
--
-- type IsRow a xs = (Generic a, Code a ~ '[ xs ])
--
-- inRow :: IsRow a xs => a -> NP I xs
-- inRow = unZ . unSOP . from
--
-- outRow :: IsRow a xs => NP I xs -> a
-- outRow = to . SOP . Z
--
-- gToRow :: (IsRow a xs, All ToField xs) => a -> [Action]
-- gToRow =
--     hcollapse
--   . hcmap (Proxy @ToField) (mapIK toField)
--   . inRow
--
-- gFromRow :: (IsRow a xs, All FromField xs) => RowParser a
-- gFromRow =
--   outRow <$>
--   hsequence (hcpure (Proxy @FromField) field)



-- # 13. More
--
-- generics-sop-0.3.0.0 has type-level metadata
--
-- records-sop: record subtyping
--
-- name-based accessors
--
-- migrations-sop: hopefully in the not too distant future

{-# LANGUAGE TypeFamilies, FlexibleContexts, RankNTypes #-}

module Bisim where

import Test.QuickCheck
import Data.Maybe
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set( Set )

class (Show p, Ord p) => Proc p where 
  type Event p
  step :: p -> [(Event p, p)]

(~~) :: (Proc p, Ord (Event p)) => p -> p -> Bool
p ~~ q =
  rep rel p == rep rel q
 where
  top = explore S.empty [p,q]
  rel = fix id refRel [top]    -- N.b.: not fix length!

explore :: Proc p => Set p -> [p] -> Set p
explore seen []       = seen
explore seen (p:ps)
  | p `S.member` seen = explore seen ps
  | otherwise         = explore (p `S.insert` seen) (map snd (step p) ++ ps)

refClass :: (Proc p, Ord (Event p)) => (p -> p) -> Set p -> [Set p]
refClass currrep ps =
  [ S.fromList qs
  | (_,qs) <- M.toList table
  ]
 where
  rep' p = map head $ group $ sort [ (e,currrep p') | (e,p') <- step p ]
  table  = M.fromListWith (++) [ (rep' p, [p]) | p <- S.toList ps ]

refRel :: (Proc p, Ord (Event p))  => [Set p] -> [Set p]
refRel pss =
  [ qs 
  | ps <- pss
  , qs <- refClass (rep pss) ps
  , S.size qs > 1
  ]

rep :: Proc p => [Set p] -> (p -> p)
rep pss p = head $
  [ S.findMin ps
  | ps <- pss
  , p `S.member` ps
  ] ++
  [ p ]  -- why is this needed? (because of the singleton-dropping optimization)

fix h f x
  | h x == h fx = x
  | otherwise   = fix h f fx 
 where
  fx = f x

-----------------------------------------------------
-- CCS (a la Koen)

data Msg
  = In Char
  | Out Char
 deriving ( Eq, Ord )

dual :: Msg -> Msg
dual (In a)  = Out a
dual (Out a) = In a

instance Show Msg where
  show (In  a) = [a,'?']
  show (Out a) = [a,'!']

instance Arbitrary Msg where
  arbitrary =
    do a <- growingElements ['a'..'h']
       b <- arbitrary
       return (if b then In a else Out a)

  shrink (In a)  = [ Out b | b <- [a,succ a] ] ++
                   [ In a'  | a' <- shrink a ]
  shrink (Out a) = [ Out a' | a' <- shrink a ]

type CCSEvent
  = Maybe Msg

data P
  = Nil
  | Act Msg P
  | P :+: P
  | P :|: P
 deriving ( Eq, Ord )

instance Show P where
  show Nil       = "0"
  show (Act m p) = show m ++ show p
  show (p :+: q) = "(" ++ show p ++ "+" ++ show q ++ ")"
  show (p :|: q) = "(" ++ show p ++ " | " ++ show q ++ ")"

instance Arbitrary P where
  arbitrary = sized (arbP . (`div` 3))
   where
    arbP n =
      frequency
      [ (1, return Nil)
      , (k, do m <- arbitrary
               p <- arbP n1
               return (Act m p))
      , (k, do p <- arbP n2
               q <- arbP n2
               op <- elements [(:|:),(:+:)]
               return (p `op` q))
      ]
     where
      k  = 5 `min` n
      n1 = n-1
      n2 = n `div` 2

  shrink Nil       = []
  shrink (Act m p) = [ p ] ++
                     [ Act m' p | m' <- shrink m ] ++
                     [ Act m p' | p' <- shrink p ]
  shrink (p :+: q) = [ p, q ] ++
                     [ p' :+: q | p' <- shrink p ] ++
                     [ p :+: q' | q' <- shrink q ]
  shrink (p :|: q) = [ p, q, p :+: q ] ++
                     [ p' :|: q | p' <- shrink p ] ++
                     [ p :|: q' | q' <- shrink q ]

instance Proc P where
  type Event P = CCSEvent

  step Nil =
    []

  step (Act m p) =
    [(Just m, p)]

  step (p :+: q) =
    step p ++ step q

  step (p :|: q) =
    [ (Nothing, p' :|: q')
    | (Just a, p') <- ps
    , (Just b, q') <- qs
    , a == dual b
    ] ++
    [ (m, p' :|: q)
    | (m, p') <- ps
    ] ++
    [ (m, p :|: q')
    | (m, q') <- qs
    ]
   where
    ps = step p
    qs = step q

type At p = forall a b. ((p -> a) -> b) -> (p -> a) -> b

atP :: At P
atP = id

atCCSEvent :: At Msg
atCCSEvent = id

prop_Refl p =
  p ~~ p

prop_Plus_Nil p =
  (Nil :+: p) ~~ p

prop_Par_Nil p =
  (Nil :|: p) ~~ p

prop_Wrong p q =
  expectFailure $
    p ~~ q

prop_Wrong2 m p q =
  expectFailure $
    Act m (p :+: q) ~~ (Act m p :+: Act m q)

prop_Wrong3 m p q =
  expectFailure $
    Act m (p :|: q) ~~ (Act m p :|: Act m q)

runPTests = do
    atP qc prop_Refl
    qc prop_Plus_Nil
    qc prop_Par_Nil
    atP qc prop_Wrong
    qc prop_Wrong2
    qc prop_Wrong3
  where
    qc :: Testable a => a -> IO ()
    qc = quickCheckWith stdArgs{maxSuccess=1000}
